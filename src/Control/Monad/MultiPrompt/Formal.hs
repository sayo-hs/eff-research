{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff).
-}
module Control.Monad.MultiPrompt.Formal where

import Control.Monad (ap)
import Data.FTCQueue (FTCQueue (..), ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import UnliftIO (MonadIO, MonadUnliftIO (withRunInIO), liftIO)

{- | An type-safe open union (extensible sum) that does not support permutation of the list, and
    behaves in a stack-like manner.

    The implementation itself is possible with the usual open-union, but in that case the type-level
    list of prompt stack frames becomes recursive and its size explodes exponentially, so this
    approach prevents that.
-}
data StackUnion (xs :: [k]) (h :: k -> [k] -> Type) where
    Here :: h x xs -> StackUnion (x : xs) h
    There :: StackUnion xs h -> StackUnion (x : xs) h

mapStackUnion :: (forall x r. h x r -> i x r) -> StackUnion xs h -> StackUnion xs i
mapStackUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapStackUnion f xs

forStackUnion :: StackUnion xs h -> (forall x r. h x r -> i x r) -> StackUnion xs i
forStackUnion u f = mapStackUnion f u

class Member x r xs | r xs -> x where
    inj :: h x r -> StackUnion xs h
    prj :: StackUnion xs h -> Maybe (h x r)

inject :: (Member x r xs) => Proxy r -> h x r -> StackUnion xs h
inject _ = inj

project :: (Member x r xs) => Proxy r -> StackUnion xs h -> Maybe (h x r)
project _ = prj

instance Member x xs (x : xs) where
    inj = Here
    prj = \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (Member x r xs) => Member x r (x' : xs) where
    inj = There . inj
    prj = \case
        Here _ -> Nothing
        There xs -> prj xs

infix 4 <

class xs < ys where
    weaken :: StackUnion xs h -> StackUnion ys h

instance xs < xs where
    weaken = id

instance {-# INCOHERENT #-} (xs < ys) => xs < y : ys where
    weaken = There . weaken

{- | A type-safe multi-prompt/control monad transformer.

    @frames@: A list of the current prompt stack frames. Each element represents the answer type of delimited continuations at that frame.

    @m@: The base monad.
-}
newtype CtlT promptFrames m a = CtlT {unCtlT :: m (CtlResult promptFrames m a)}

data CtlResult ps m a
    = Pure a
    | Ctl (Ctls ps m a)

type Ctls ps m a = StackUnion ps (CtlFrame ps m a)

data CtlFrame (w :: [Type]) (m :: Type -> Type) (a :: Type) (ans :: Type) (r :: [Type]) where
    Abort :: ans -> CtlFrame w m a ans r
    Control :: ((b -> CtlT r m ans) -> CtlT r m ans) -> FTCQueue (CtlT w m) b a -> CtlFrame w m a ans r

instance (Applicative f) => Functor (CtlResult frames f) where
    fmap f = \case
        Pure x -> Pure $ f x
        Ctl ctls -> Ctl $ forStackUnion ctls \case
            Abort ans -> Abort ans
            Control ctl q -> Control ctl $ q |> (CtlT . pure . Pure . f)

instance (Applicative f) => Functor (CtlT fs f) where
    fmap f (CtlT m) = CtlT $ fmap f <$> m

instance (Monad m) => Applicative (CtlT fs m) where
    pure = CtlT . pure . Pure
    (<*>) = ap

instance (Monad m) => Monad (CtlT fs m) where
    CtlT m >>= f =
        CtlT $
            m >>= \case
                Pure x -> unCtlT $ f x
                Ctl ctls -> pure $ Ctl $ forStackUnion ctls \case
                    Abort a -> Abort a
                    Control ctl q -> Control ctl $ q |> f

instance (MonadIO m) => MonadIO (CtlT fs m) where
    liftIO m = CtlT $ liftIO $ Pure <$> m

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] m) where
    withRunInIO f = CtlT $ withRunInIO \run -> Pure <$> f (run . runCtlT)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] f) where
    withRunInBase f = CtlT $ Pure <$> withRunInBase \run -> f (run . runCtlT)

prompt_ :: (Monad m) => CtlT (ans : ps) m ans -> CtlT ps m ans
prompt_ (CtlT m) =
    CtlT $
        m >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case ctls of
                Here (Control ctl q) -> unCtlT $ ctl $ prompt_ . qApp q
                Here (Abort ans) -> pure $ Pure ans
                There ctls' -> pure $ Ctl $ forStackUnion ctls' \case
                    (Control ctl q) -> Control ctl (tsingleton $ prompt_ . qApp q)
                    Abort r -> Abort r

prompt :: (Monad m) => (Proxy ps -> CtlT (ans : ps) m ans) -> CtlT ps m ans
prompt f = prompt_ $ f Proxy

control :: (Member ans psUnder ps, Applicative m) => Proxy psUnder -> ((a -> CtlT psUnder m ans) -> CtlT psUnder m ans) -> CtlT ps m a
control p f = CtlT . pure . Ctl . inject p $ Control f (tsingleton $ CtlT . pure . Pure)

delimitAbort ::
    forall ps m a psUnder ans.
    (Member ans psUnder ps, Monad m) =>
    Proxy psUnder ->
    CtlT ps m a ->
    (ans -> CtlT ps m a) ->
    CtlT ps m a
delimitAbort p (CtlT m) k =
    CtlT $
        m >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case project p ctls of
                Just (Abort r) -> unCtlT $ k r
                _ -> pure $ Ctl ctls

abort :: (Member ans psUnder ps, Applicative f) => Proxy psUnder -> ans -> CtlT ps f a
abort p = CtlT . pure . Ctl . inject p . Abort

embed :: (psUnder < ps, Monad m) => CtlT psUnder m a -> CtlT ps m a
embed (CtlT m) =
    CtlT $
        m <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ forStackUnion (weaken ctls) \case
                Abort ans -> Abort ans
                Control ctl q -> Control ctl $ tsingleton $ embed . qApp q

qApp :: (Monad m) => FTCQueue (CtlT ps m) a b -> a -> CtlT ps m b
qApp q x = CtlT $ case tviewl q of
    TOne k -> unCtlT $ k x
    k :| t ->
        unCtlT (k x) >>= \case
            Pure y -> unCtlT $ qApp t y
            Ctl ctls -> pure $ Ctl $ forStackUnion ctls \case
                Control ctl q' -> Control ctl $ q' >< t
                Abort r -> Abort r

liftCtlT :: (Functor f) => f a -> CtlT fs f a
liftCtlT a = CtlT $ Pure <$> a

runCtlT :: (Functor f) => CtlT '[] f a -> f a
runCtlT (CtlT m) =
    m <&> \case
        Pure x -> x
        Ctl ctls -> case ctls of {}

runPure :: CtlT '[] Identity a -> a
runPure (CtlT (Identity m)) = case m of
    Pure x -> x
    Ctl ctls -> case ctls of {}
