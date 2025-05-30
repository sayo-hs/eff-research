-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff).
-}
module Control.Monad.MultiPrompt.Formal where

import Control.Monad (ap, liftM)
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

class Member x r xs where
    inj :: h x r -> StackUnion xs h
    prj :: StackUnion xs h -> Maybe (h x r)

inject :: (Member x r xs) => Proxy '(x, r) -> h x r -> StackUnion xs h
inject _ = inj

project :: (Member x r xs) => Proxy '(x, r) -> StackUnion xs h -> Maybe (h x r)
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

{- | A type-safe multi-prompt/control monad transformer.

    @frames@: A list of the current prompt stack frames. Each element represents the answer type of delimited continuations at that frame.

    @m@: The base monad.
-}
newtype CtlT frames m a = CtlT {unCtlT :: m (CtlResult frames m a)}

data CtlResult frames m a
    = Pure a
    | Ctl (Ctls frames m a)

type Ctls frames m a = StackUnion frames (CtlFrame frames m a)

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

prompt_ :: (Monad m) => CtlT (ans : r) m ans -> CtlT r m ans
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

prompt :: (Monad m) => (Proxy '(ans, r) -> CtlT (ans : r) m ans) -> CtlT r m ans
prompt f = prompt_ $ f Proxy

control :: (Member ans r fs, Applicative m) => Proxy '(ans, r) -> ((a -> CtlT r m ans) -> CtlT r m ans) -> CtlT fs m a
control p f = CtlT . pure . Ctl . inject p $ Control f (tsingleton $ CtlT . pure . Pure)

delimitAbort ::
    forall fs m a ans r.
    (Member ans r fs, Monad m) =>
    Proxy '(ans, r) ->
    CtlT fs m a ->
    (ans -> CtlT fs m a) ->
    CtlT fs m a
delimitAbort p (CtlT m) k =
    CtlT $
        m >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case project p ctls of
                Just (Abort r) -> unCtlT $ k r
                _ -> pure $ Ctl ctls

abort :: (Member ans r fs, Applicative m) => Proxy '(ans, r) -> ans -> CtlT fs m a
abort p = CtlT . pure . Ctl . inject p . Abort

embed :: (Member ans r fs, Monad m) => Proxy '(ans, r) -> CtlT r m a -> CtlT fs m a
embed p m = control p (m >>=)

qApp :: (Monad m) => FTCQueue (CtlT fs m) a b -> a -> CtlT fs m b
qApp q x = CtlT $ case tviewl q of
    TOne k -> unCtlT $ k x
    k :| t ->
        unCtlT (k x) >>= \case
            Pure y -> unCtlT $ qApp t y
            Ctl ctls -> pure $ Ctl $ forStackUnion ctls \case
                Control ctl q' -> Control ctl $ q' >< t
                Abort r -> Abort r

runCtlT :: (Functor f) => CtlT '[] f a -> f a
runCtlT (CtlT m) =
    m <&> \case
        Pure x -> x
        Ctl ctls -> case ctls of {}

runPure :: CtlT '[] Identity a -> a
runPure (CtlT (Identity m)) = case m of
    Pure x -> x
    Ctl ctls -> case ctls of {}

runExcept :: (Monad m) => (Proxy '(Either e a, r) -> CtlT (Either e a : r) m a) -> CtlT r m (Either e a)
runExcept m = prompt_ $ Right <$> m Proxy

throw :: (Member (Either e ans) r fs, Monad m) => Proxy '(Either e ans, r) -> e -> CtlT fs m a
throw p e = abort p $ Left e

catch :: (Member (Either e ans) r fs, Monad m) => Proxy '(Either e ans, r) -> CtlT fs m a -> (e -> CtlT fs m a) -> CtlT fs m a
catch p m hdl =
    delimitAbort p m \case
        Left e -> hdl e
        r -> abort p r

test :: Either String Int
test = runPure do
    runExcept \p -> do
        catch p (throw p "BOOM") \s -> pure $ length s

-- >>> test
-- Right 4
