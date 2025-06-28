{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal
import Control.Monad.MultiPrompt.Formal qualified as C
import Data.Coerce (Coercible, coerce)
import Data.Data (Proxy (Proxy))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)

-- | An effect monad built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: EffCtlT (PromptFrames es) es m a}

type family e !: m where
    e !: EffT es m = EffT (e : es) m
    E e (Ctl p) !: EffCtlT ps es m = EffCtlT (p : ps) (E e (Ctl p) : es) m
    E e (Tail u) !: EffCtlT ps es m = EffCtlT ps (E e (Tail u) : es) m

deriving instance (Applicative f) => Functor (EffT es f)

instance (Monad m) => Applicative (EffT es m) where
    pure x = EffT $ pure x
    EffT ff <*> EffT fm = EffT $ ff <*> fm

instance (Monad m) => Monad (EffT es m) where
    EffT m >>= f = EffT $ m >>= \x -> unEffT $ f x

type EffCtlT ps es m = CtlT ps (Env es m) m

type Effect = (Type -> Type) -> Type -> Type
type data EffectFrame = E Effect Resumption
type data Resumption = Tail [PromptFrame] | Ctl PromptFrame

type family PromptFrames es where
    PromptFrames (E _ (Ctl p) : es) = p : PromptFrames es
    PromptFrames (E _ (Tail _) : es) = PromptFrames es
    PromptFrames '[] = '[]

-- | A effect handler.
data Handler e w m where
    CtlHandler ::
        ( forall x.
          e (EffCtlT (Prompt ans (Env es m) u : u) w m) x ->
          EffCtlT (Prompt ans (Env es m) u : u) es m x
        ) ->
        Env es m ->
        Handler (E e (Ctl (Prompt ans (Env es m) u))) w m

-- | Vector of handlers.
data Handlers (es :: [EffectFrame]) (w :: [EffectFrame]) m where
    Cons :: Handler e w m -> Handlers es w m -> Handlers (e : es) w m
    Nil :: Handlers '[] w m

newtype Env es m = Env {unEnv :: Handlers es es m}

-- | A type-class for higher-order effects.
class EnvFunctor e where
    cmapEnv ::
        (Monad m, EnvFunctors es1, EnvFunctors es2) =>
        (Env es1 m -> Env es2 m) ->
        e (EffCtlT u es2 m) a ->
        e (EffCtlT u es1 m) a

    fromCtl :: e (EffCtlT (PromptFrames es) es m) a -> e (EffT es m) a

mapHandler ::
    (EnvFunctor e, Monad m, EnvFunctors es1, EnvFunctors es2) =>
    (Env es1 m -> Env es2 m) ->
    Handler (E e r) es1 m ->
    Handler (E e r) es2 m
mapHandler f = \case
    CtlHandler h v -> CtlHandler (h . cmapEnv f) v

class EnvFunctors es where
    mapHandlers ::
        (Monad m, EnvFunctors es1, EnvFunctors es2) =>
        (Env es1 m -> Env es2 m) ->
        Handlers es es1 m ->
        Handlers es es2 m

instance EnvFunctors '[] where
    mapHandlers _ Nil = Nil

instance (EnvFunctor e, EnvFunctors es) => EnvFunctors (E e r : es) where
    mapHandlers f (Cons h hs) = Cons (mapHandler f h) (mapHandlers f hs)

(!:) :: (EnvFunctor e, EnvFunctors es, Monad m) => Handler (E e r) es m -> Env es m -> Env (E e r : es) m
h !: Env hs = Env $ Cons (mapHandler (h !:) h) (mapHandlers (h !:) hs)

dropEnv :: (EnvFunctor e, EnvFunctors es, Monad m) => Env (E e r : es) m -> Env es m
dropEnv (Env (Cons _ hs)) = Env $ mapHandlers dropEnv hs

raise :: (EnvFunctor e, EnvFunctors es, Monad m) => EffCtlT ps es m a -> EffCtlT ps (E e r : es) m a
raise = cmapCtlT dropEnv

newtype Membership ff es p = Membership
    { getHandler :: forall w m. Handlers es w m -> Handler (E ff p) w m
    }

-- | Type-level search over elements in a vector.
class Elem ff (es :: [EffectFrame]) p | ff es -> p where
    membership :: Membership ff es p

instance Elem ff (E ff p : es) p where
    membership =
        Membership
            { getHandler = \(Cons h _) -> h
            }

instance {-# OVERLAPPABLE #-} (Elem ff es p) => Elem ff (E ff' p' : es) p where
    membership =
        Membership
            { getHandler = \(Cons _ hs) -> getHandler membership hs
            }

sendCtl ::
    (Member (Prompt ans r u) ps, Monad m, EnvFunctor e, p ~ Prompt ans r u) =>
    Proxy p ->
    Membership e es (Ctl p) ->
    e (EffCtlT (p : u) es m) a ->
    EffCtlT ps es m a
sendCtl p i e = CtlT \r@(Env hs) -> case getHandler i hs of
    CtlHandler h r' ->
        unCtlT (under p (\(Env hs') -> case getHandler i hs' of CtlHandler _ r'' -> r'') r' $ h e) r

interpretCtl ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p x. (p ~ Prompt a (Env es m) ps) => Proxy p -> e (EffCtlT (p : ps) es m) x -> EffCtlT (p : ps) es m x) ->
    (forall p. (p ~ Prompt a (Env es m) ps) => Proxy p -> EffCtlT (p : ps) (E e (Ctl p) : es) m a) ->
    EffCtlT ps es m a
interpretCtl h m =
    prompt (\r -> CtlHandler (h Proxy) r !: r) \p -> m p

interpretBy ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p. (p ~ Prompt b (Env es m) ps) => a -> EffCtlT (p : ps) (E e (Ctl p) : es) m b) ->
    (forall p x. (p ~ Prompt b (Env es m) ps) => e (EffCtlT (p : ps) es m) x -> (x -> EffCtlT ps es m b) -> EffCtlT ps es m b) ->
    (forall p. (p ~ Prompt b (Env es m) ps) => EffCtlT (p : ps) (E e (Ctl p) : es) m a) ->
    EffCtlT ps es m b
interpretBy ret hdl m =
    interpretCtl
        (\p e -> control p \k -> hdl e k)
        \_ -> do
            x <- m
            ret x

interpretCtl' ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p x. (p ~ Prompt a (Env es m) ps) => Proxy p -> e (EffCtlT (p : ps) (E e (Ctl p) : es) m) x -> EffCtlT (p : ps) es m x) ->
    (forall p. (p ~ Prompt a (Env es m) ps) => Proxy p -> EffCtlT (p : ps) (E e (Ctl p) : es) m a) ->
    EffCtlT ps es m a
interpretCtl' h m =
    prompt (\r -> CtlHandler (h Proxy . cmapEnv dropEnv) r !: r) \p -> m p

interpretBy' ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p. a -> EffT (E e (Ctl p) : es) m b) ->
    (forall p x. e (EffT (E e (Ctl p) : es) m) x -> (x -> EffT es m b) -> EffT es m b) ->
    (forall p. EffT (E e (Ctl p) : es) m a) ->
    EffT es m b
interpretBy' ret hdl m =
    EffT $ interpretCtl'
        (\p e -> control p \k -> unEffT $ hdl (fromCtl e) (EffT . k))
        \_ -> do
            x <- unEffT m
            unEffT $ ret x

runPure :: EffCtlT '[] '[] Identity a -> a
runPure = C.runPure (Env Nil)

runEffT :: (Functor f) => EffCtlT '[] '[] f a -> f a
runEffT = runCtlT (Env Nil)

newtype FirstOrder (e :: Effect) f a = FirstOrder (e f a)

instance (forall f g x. Coercible (e f x) (e g x)) => EnvFunctor (FirstOrder e) where
    cmapEnv _ = coerce
    fromCtl = coerce

data Throw e :: Effect where
    Throw :: e -> Throw e f a

data Catch e :: Effect where
    Catch :: f a -> (e -> f a) -> Catch e f a

deriving via FirstOrder (Throw e) instance EnvFunctor (Throw e)

instance EnvFunctor (Catch e) where
    cmapEnv f (Catch m k) = Catch (cmapCtlT f m) (cmapCtlT f . k)
    fromCtl = coerce
