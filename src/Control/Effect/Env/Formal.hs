{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Effect.Env.Formal where

import Control.Monad.MultiPrompt.Formal (CtlT, Unlift (withRunInBase))
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO, liftIO, withRunInIO)

data Effect = Effect ((Type -> Type) -> Type -> Type) Resumption

data Resumption = Tail | NonTail Type

data Handlers (es :: [Effect]) f b where
    Here :: (forall fs x. e f x -> CtlT fs b x) -> Handlers ('Effect e Tail : es) f b
    HereNT :: (forall fs x. e f x -> CtlT (ans : fs) b x) -> Handlers ('Effect e (NonTail ans) : es) f b
    There :: Handlers es f b -> Handlers (e : es) f b

data Env es f b = forall g. Env
    { handlers :: Handlers es g b
    , koi :: forall x. f x -> g x
    }

hcmapEnv :: (forall x. f x -> g x) -> Env es g b -> Env es f b
hcmapEnv phi (Env f koi) = Env f (koi . phi)

class HFunctor ff where
    hfmap :: (forall x. f x -> g x) -> ff f a -> ff g a

(!:) ::
    (HFunctor e) =>
    ((forall fs x. e f x -> CtlT fs b x) -> r) ->
    (Env es f b -> r) ->
    Env ('Effect e Tail : es) f b ->
    r
(f !: g) (Env hs koi) = case hs of
    Here h -> f $ h . hfmap koi
    There hs' -> g $ Env hs' koi

(!!:) ::
    (HFunctor e) =>
    ((forall fs x. e f x -> CtlT (ans : fs) b x) -> r) ->
    (Env es f b -> r) ->
    Env ('Effect e (NonTail ans) : es) f b ->
    r
(f !!: g) (Env hs koi) = case hs of
    HereNT h -> f $ h . hfmap koi
    There hs' -> g $ Env hs' koi

newtype EffT es fs b a
    = EffT {unEffT :: Env es (EffT es fs b) b -> CtlT fs b a}
    deriving (Functor)

runEffT :: Env es (EffT es fs b) b -> EffT es fs b a -> CtlT fs b a
runEffT = flip unEffT

instance (Monad m) => Applicative (EffT es fs m) where
    pure x = EffT \_ -> pure x
    EffT ff <*> EffT fa = EffT \v -> ff v <*> fa v

instance (Monad m) => Monad (EffT es fs m) where
    EffT m >>= f = EffT \v -> m v >>= runEffT v . f

instance (MonadIO m) => MonadIO (EffT es fs m) where
    liftIO m = EffT \_ -> liftIO m

instance (MonadUnliftIO m) => MonadUnliftIO (EffT es '[] m) where
    withRunInIO f = EffT \v -> withRunInIO \run -> f $ run . runEffT v

instance (Unlift b f, Functor f) => Unlift b (EffT es '[] f) where
    withRunInBase f = EffT \v -> withRunInBase \run -> f $ run . runEffT v

trans :: (Env es' (EffT es fs f) f -> Env es (EffT es fs f) f) -> EffT es fs f a -> EffT es' fs f a
trans f (EffT withHandlers) = EffT $ withHandlers . f . hcmapEnv (trans f)
