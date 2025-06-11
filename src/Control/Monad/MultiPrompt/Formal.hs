{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
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

-- | An type-safe open union.
data Union (xs :: [k]) (h :: k -> Type) where
    Here :: h x -> Union (x : xs) h
    There :: Union xs h -> Union (x : xs) h

mapUnion :: (forall x. h x -> i x) -> Union xs h -> Union xs i
mapUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapUnion f xs

forUnion :: Union xs h -> (forall x. h x -> i x) -> Union xs i
forUnion u f = mapUnion f u

class Member x xs where
    inj :: h x -> Union xs h
    prj :: Union xs h -> Maybe (h x)

inject :: (Member x xs) => Proxy x -> h x -> Union xs h
inject _ = inj

project :: (Member x xs) => Proxy x -> Union xs h -> Maybe (h x)
project _ = prj

instance Member x (x : xs) where
    inj = Here
    prj = \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (Member x xs) => Member x (x' : xs) where
    inj = There . inj
    prj = \case
        Here _ -> Nothing
        There xs -> prj xs

infix 4 <

class xs < ys where
    weaken :: Union xs h -> Union ys h

instance xs < xs where
    weaken = id

instance {-# INCOHERENT #-} (xs < ys) => xs < y : ys where
    weaken = There . weaken

data PromptFrame = PromptFrame Type [PromptFrame]

type family Answer p where
    Answer ('PromptFrame ans _) = ans

type family Underlying p where
    Underlying ('PromptFrame _ u) = u

{- | A type-safe multi-prompt/control monad transformer.

    @frames@: A list of the current prompt stack frames.

    @m@: The base monad.
-}
newtype CtlT (ps :: [PromptFrame]) m a = CtlT {unCtlT :: m (CtlResult ps m a)}

data CtlResult ps m a
    = Pure a
    | Ctl (Ctls ps m a)

type Ctls ps m a = Union ps (CtlFrame ps m a)

data CtlFrame (ps :: [PromptFrame]) (m :: Type -> Type) (a :: Type) (p :: PromptFrame) where
    Abort :: Answer p -> CtlFrame ps m a p
    Control :: ((b -> CtlT (Underlying p) m (Answer p)) -> CtlT (Underlying p) m (Answer p)) -> FTCQueue (CtlT ps m) b a -> CtlFrame ps m a p

instance (Applicative f) => Functor (CtlResult frames f) where
    fmap f = \case
        Pure x -> Pure $ f x
        Ctl ctls -> Ctl $ forUnion ctls \case
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
                Ctl ctls -> pure $ Ctl $ forUnion ctls \case
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

prompt :: (Monad m) => CtlT ('PromptFrame ans ps : ps) m ans -> CtlT ps m ans
prompt (CtlT m) =
    CtlT $
        m >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case ctls of
                Here (Control ctl q) -> unCtlT $ ctl $ prompt . qApp q
                Here (Abort ans) -> pure $ Pure ans
                There ctls' -> pure $ Ctl $ forUnion ctls' \case
                    (Control ctl q) -> Control ctl (tsingleton $ prompt . qApp q)
                    Abort r -> Abort r

prompt_ :: (Monad m) => (forall p. Proxy p -> CtlT (p : ps) m ans) -> CtlT ps m ans
prompt_ f = prompt $ f Proxy

control :: (Member p ps, Applicative m) => Proxy p -> ((a -> CtlT (Underlying p) m (Answer p)) -> CtlT (Underlying p) m (Answer p)) -> CtlT ps m a
control p f = CtlT . pure . Ctl . inject p $ Control f (tsingleton $ CtlT . pure . Pure)

delimitAbort ::
    forall ps m a p.
    (Member p ps, Monad m) =>
    Proxy p ->
    CtlT ps m a ->
    (Answer p -> CtlT ps m a) ->
    CtlT ps m a
delimitAbort p (CtlT m) k =
    CtlT $
        m >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case project p ctls of
                Just (Abort r) -> unCtlT $ k r
                _ -> pure $ Ctl ctls

abort :: (Member p ps, Applicative f) => Proxy p -> Answer p -> CtlT ps f a
abort p = CtlT . pure . Ctl . inject p . Abort

embed :: (p : Underlying p < ps, Monad m) => Proxy p -> CtlT (p : Underlying p) m a -> CtlT ps m a
embed p (CtlT m) =
    CtlT $
        m <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ forUnion (weaken ctls) \case
                Abort ans -> Abort ans
                Control ctl q -> Control ctl $ tsingleton $ embed p . qApp q

qApp :: (Monad m) => FTCQueue (CtlT ps m) a b -> a -> CtlT ps m b
qApp q x = CtlT $ case tviewl q of
    TOne k -> unCtlT $ k x
    k :| t ->
        unCtlT (k x) >>= \case
            Pure y -> unCtlT $ qApp t y
            Ctl ctls -> pure $ Ctl $ forUnion ctls \case
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

hoistCtlT :: (Monad m, Monad n) => (forall x. m x -> n x) -> (forall x. n x -> m x) -> CtlT ps m a -> CtlT ps n a
hoistCtlT to from (CtlT m) =
    CtlT $
        to m <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ forUnion ctls \case
                Abort r -> Abort r
                Control ctl q -> Control (hoistCtlT to from . ctl . (hoistCtlT from to .)) (tsingleton $ hoistCtlT to from . qApp q)

data Status ps m r = Done r | Continue (CtlT ps m (Status ps m r))

yield :: (Member p ps, Monad m, Answer p ~ Status (Underlying p) m r) => Proxy p -> CtlT ps m ()
yield p = control p \k -> pure $ Continue $ k ()
