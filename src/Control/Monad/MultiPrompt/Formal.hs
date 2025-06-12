{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use fmap" #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff).
-}
module Control.Monad.MultiPrompt.Formal where

import Control.Monad (ap)
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.FTCQueue (FTCQueue (..), ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (Identity), runIdentity)
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

{- | A type-safe multi-prompt/control monad transformer with reader environment.

    @ps@: A list of the current prompt stack frames.

    @r@: The reader environment.

    @m@: The base monad.
-}
newtype CtlT (ps :: [PromptFrame]) r m a = CtlT {unCtlT :: r -> m (CtlResult ps r m a)}

mapEnv :: (Monad m) => (r -> r') -> (r' -> r) -> CtlT ps r' m a -> CtlT ps r m a
mapEnv f g (CtlT m) = CtlT \v ->
    m (f v) <&> \case
        Pure x -> Pure x
        Ctl ctls -> Ctl $ forUnion ctls \case
            Abort r -> Abort r
            Control ctl q -> Control (mapEnv f g . ctl . (mapEnv g f .)) (tsingleton $ mapEnv f g . qApp q)

data CtlResult ps r m a
    = Pure a
    | Ctl (Ctls ps r m a)

type Ctls ps r m a = Union ps (CtlFrame ps r m a)

data CtlFrame (ps :: [PromptFrame]) r (m :: Type -> Type) (a :: Type) (p :: PromptFrame) where
    Abort :: Answer p -> CtlFrame ps r m a p
    Control :: ((b -> CtlT (Underlying p) r m (Answer p)) -> CtlT (Underlying p) r m (Answer p)) -> FTCQueue (CtlT ps r m) b a -> CtlFrame ps r m a p

instance (Applicative f) => Functor (CtlResult frames r f) where
    fmap f = \case
        Pure x -> Pure $ f x
        Ctl ctls -> Ctl $ forUnion ctls \case
            Abort ans -> Abort ans
            Control ctl q -> Control ctl $ q |> (CtlT . const . pure . Pure . f)

instance (Applicative f) => Functor (CtlT fs r f) where
    fmap f (CtlT m) = CtlT $ fmap (fmap f) . m

instance (Monad m) => Applicative (CtlT fs r m) where
    pure = CtlT . const . pure . Pure
    (<*>) = ap

instance (Monad m) => Monad (CtlT fs r m) where
    CtlT m >>= f =
        CtlT \v ->
            m v >>= \case
                Pure x -> unCtlT (f x) v
                Ctl ctls -> pure $ Ctl $ forUnion ctls \case
                    Abort a -> Abort a
                    Control ctl q -> Control ctl $ q |> f

instance (MonadIO m) => MonadIO (CtlT fs r m) where
    liftIO m = CtlT $ const $ liftIO $ Pure <$> m

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] r m) where
    withRunInIO f = CtlT \v -> withRunInIO \run -> Pure <$> f (run . runCtlT v)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f) => Unlift b (ReaderT r f) where
    withRunInBase f = ReaderT \v -> withRunInBase \run -> f $ run . flip runReaderT v

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] r f) where
    withRunInBase f = CtlT \v -> Pure <$> withRunInBase \run -> f (run . runCtlT v)

prompt :: (Monad m) => CtlT ('PromptFrame ans ps : ps) r m ans -> CtlT ps r m ans
prompt (CtlT m) =
    CtlT \v ->
        m v >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case ctls of
                Here (Control ctl q) -> unCtlT (ctl $ prompt . qApp q) v
                Here (Abort ans) -> pure $ Pure ans
                There ctls' -> pure $ Ctl $ forUnion ctls' \case
                    (Control ctl q) -> Control ctl (tsingleton $ prompt . qApp q)
                    Abort r -> Abort r

prompt_ :: (Monad m) => (forall p. Proxy p -> CtlT (p : ps) r m ans) -> CtlT ps r m ans
prompt_ f = prompt $ f Proxy

control :: (Member p ps, Applicative m) => Proxy p -> ((a -> CtlT (Underlying p) r m (Answer p)) -> CtlT (Underlying p) r m (Answer p)) -> CtlT ps r m a
control p f = CtlT . const . pure . Ctl . inject p $ Control f (tsingleton $ CtlT . const . pure . Pure)

delimitAbort ::
    forall ps r m a p.
    (Member p ps, Monad m) =>
    Proxy p ->
    CtlT ps r m a ->
    (Answer p -> CtlT ps r m a) ->
    CtlT ps r m a
delimitAbort p (CtlT m) k =
    CtlT \v ->
        m v >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case project p ctls of
                Just (Abort r) -> unCtlT (k r) v
                _ -> pure $ Ctl ctls

abort :: (Member p ps, Applicative f) => Proxy p -> Answer p -> CtlT ps r f a
abort p = CtlT . const . pure . Ctl . inject p . Abort

embed :: (u < ps, Monad m) => Proxy p -> CtlT u r m a -> CtlT ps r m a
embed p (CtlT m) =
    CtlT \v ->
        m v <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ forUnion (weaken ctls) \case
                Abort ans -> Abort ans
                Control ctl q -> Control ctl $ tsingleton $ embed p . qApp q

qApp :: (Monad m) => FTCQueue (CtlT ps r m) a b -> a -> CtlT ps r m b
qApp q x = CtlT \v -> case tviewl q of
    TOne k -> unCtlT (k x) v
    k :| t ->
        unCtlT (k x) v >>= \case
            Pure y -> unCtlT (qApp t y) v
            Ctl ctls -> pure $ Ctl $ forUnion ctls \case
                Control ctl q' -> Control ctl $ q' >< t
                Abort r -> Abort r

liftCtlT :: (Functor f) => f a -> CtlT fs r f a
liftCtlT a = CtlT $ const $ Pure <$> a

runCtlT :: (Functor f) => r -> CtlT '[] r f a -> f a
runCtlT v (CtlT m) =
    m v <&> \case
        Pure x -> x
        Ctl ctls -> case ctls of {}

runPure :: r -> CtlT '[] r Identity a -> a
runPure v (CtlT m) = case runIdentity $ m v of
    Pure x -> x
    Ctl ctls -> case ctls of {}

data Status ps v m r = Done r | Continue (CtlT ps v m (Status ps v m r))

yield :: (Member p ps, Monad m, Answer p ~ Status (Underlying p) v m r) => Proxy p -> CtlT ps v m ()
yield p = control p \k -> pure $ Continue $ k ()
