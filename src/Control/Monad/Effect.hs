{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal (
    CtlT (..),
    FreerF (Pure),
    FreerT (FreerT),
    PromptFrame (..),
    cmapCtlT,
    runCtlT,
    runFreerT,
    under,
 )
import Control.Monad.MultiPrompt.Formal qualified as C
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.Coerce (Coercible, coerce)
import Data.Data (Proxy (Proxy))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)

type Effect = (Type -> Type) -> Type -> Type

infixr 6 :+
infixr 6 :/

type data Frames = Type :/ Frames | Effect :+ Frames | Nil

type data Frame = E Effect | P Type

type family ConsFrame e = r | r -> e where
    ConsFrame (E e) = (:+) e
    ConsFrame (P ans) = (:/) ans

type family Prompts m es where
    Prompts m (ans :/ es) = Prompt ans (Env m (ans :/ es)) : Prompts m (BasePrompt es)
    Prompts _ Nil = '[]

type family Effects es where
    Effects (e :+ es) = e : Effects es
    Effects (_ :/ es) = Effects es
    Effects Nil = '[]

type family FrameList es where
    FrameList (e :+ es) = E e : FrameList es
    FrameList (ans :/ es) = P ans : FrameList es
    FrameList Nil = '[]

type family BasePrompt es where
    BasePrompt (_ :+ es) = BasePrompt es
    BasePrompt (ans :/ es) = ans :/ es
    BasePrompt Nil = Nil

class (u :: [PromptFrame]) < (es :: Frames) where
    type Underlying u es :: Frames
    raiseUnderlying :: (Monad m) => EffT (Underlying u es) m a -> EffT es m a

newtype Env m es = Env {unEnv :: Handlers m es es}

mapEnv ::
    (Monad m, EnvFunctors es1, EnvFunctors es2) =>
    (forall w. Handlers m w es1 -> Handlers m w es2) ->
    Env m es1 ->
    Env m es2
mapEnv f (Env hs) = Env $ mapHandlers (mapEnv f) $ f hs

-- | A effect handler.
data Handler (m :: Type -> Type) (w :: Frames) (e :: Effect) (u :: Frames) where
    Handler :: (forall x. e (EffCtlT (Prompts m u) w m) x -> EffCtlT (Prompts m u) u m x) -> Env m u -> Handler m w e u

-- | Vector of handlers.
data Handlers (m :: Type -> Type) (w :: Frames) (es :: Frames) where
    ConsHandler :: Handler m w e (BasePrompt es) -> Handlers m w es -> Handlers m w (e :+ es)
    ConsPrompt :: Handlers m w es -> Handlers m w (ans :/ es)
    Nil :: Handlers w m Nil

-- | An effect monad built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: CtlT (Prompts m (BasePrompt es)) (Env m es) m a}
    deriving (Functor, Applicative, Monad)

newtype EffCtlT ps es m a = EffCtlT {unEffCtlT :: CtlT ps (Env m es) m a}
    deriving (Functor, Applicative, Monad)

class EnvFunctors es where
    mapHandlers ::
        (Monad m, EnvFunctors es1, EnvFunctors es2) =>
        (Env m es1 -> Env m es2) ->
        Handlers m es1 es ->
        Handlers m es2 es

instance EnvFunctors Nil where
    mapHandlers _ Nil = Nil

instance (EnvFunctor e, EnvFunctors es) => EnvFunctors (e :+ es) where
    mapHandlers f (ConsHandler h hs) = ConsHandler (mapHandler f h) (mapHandlers f hs)

instance (EnvFunctors es) => EnvFunctors (ans :/ es) where
    mapHandlers f (ConsPrompt hs) = ConsPrompt (mapHandlers f hs)

-- | A type-class for higher-order effects.
class EnvFunctor e where
    cmapEnv ::
        (Monad m, EnvFunctors es1, EnvFunctors es2) =>
        (Env m es1 -> Env m es2) ->
        e (EffCtlT u es2 m) a ->
        e (EffCtlT u es1 m) a

    fromCtl :: e (EffCtlT (Prompts m (BasePrompt es)) es m) a -> e (EffT es m) a
    toCtl :: e (EffT es m) a -> e (EffCtlT (Prompts m (BasePrompt es)) es m) a

mapHandler ::
    (EnvFunctor e, Monad m, EnvFunctors es1, EnvFunctors es2) =>
    (Env m es1 -> Env m es2) ->
    Handler m es1 e u ->
    Handler m es2 e u
mapHandler f = \case
    Handler h v -> Handler (h . cmapEnv f) v

(!:) :: (EnvFunctor e, EnvFunctors es, Monad m) => Handler m es e (BasePrompt es) -> Env m es -> Env m (ConsFrame (E e) es)
h@(Handler _ _) !: Env hs = Env $ ConsHandler (mapHandler (h !:) h) (mapHandlers (h !:) hs)

class IsFrame e where
    dropEnv :: (EnvFunctors es, Monad m) => Env m (ConsFrame e es) -> Env m es

instance (EnvFunctor e) => IsFrame (E e) where
    dropEnv (Env (ConsHandler _ hs)) = Env $ mapHandlers dropEnv hs

instance IsFrame (P ans) where
    dropEnv (Env (ConsPrompt hs)) = Env $ mapHandlers dropEnv hs

newtype Membership e es u = Membership
    { getHandler :: forall w m. Handlers m w es -> Handler m w e u
    }

-- | Type-level search over elements in a vector.
class Elem e (es :: Frames) u | e es -> u where
    membership :: Membership e es u

instance (u ~ BasePrompt es) => Elem e (e :+ es) u where
    membership =
        Membership
            { getHandler = \(ConsHandler h _) -> h
            }

instance {-# OVERLAPPABLE #-} (Elem e es u) => Elem e (e' :+ es) u where
    membership =
        Membership
            { getHandler = \(ConsHandler _ hs) -> getHandler membership hs
            }

instance (Elem e es u) => Elem e (ans :/ es) u where
    membership =
        Membership
            { getHandler = \(ConsPrompt hs) -> getHandler membership hs
            }

sendCtl ::
    forall e es u m a.
    (Prompts m u C.< Prompts m (BasePrompt es), Monad m) =>
    Membership e es u ->
    e (EffCtlT (Prompts m u) es m) a ->
    EffT es m a
sendCtl i e =
    EffT $ CtlT $ FreerT $ ReaderT \r@(Env hs) ->
        let Handler h r' = getHandler i hs
         in (`runReaderT` r)
                . runFreerT
                . unCtlT
                . under Proxy (\(Env hs') -> let Handler _ r'' = getHandler i hs' in r'') r'
                . unEffCtlT
                $ h e

sendTail :: forall e es m a. (Functor m) => Membership e es Nil -> e (EffCtlT '[] es m) a -> EffT es m a
sendTail i e = EffT $ CtlT $ FreerT $ ReaderT \(Env hs) ->
    let Handler h _ = getHandler i hs
     in Pure <$> runCtlT (Env Nil) (unEffCtlT $ h e)

class (EnvFunctors es) => Base es where
    dropToBasePrompt :: (Monad m) => Env m es -> Env m (BasePrompt es)
    supplyBaseHandlers :: (Monad m) => Handlers m w es -> Handlers m w (BasePrompt es) -> Handlers m w es

instance (Base es, EnvFunctor e) => Base (e :+ es) where
    dropToBasePrompt = dropToBasePrompt . dropEnv
    supplyBaseHandlers (ConsHandler h hs) hs' = ConsHandler h $ supplyBaseHandlers hs hs'

instance (EnvFunctors es) => Base (ans :/ es) where
    dropToBasePrompt = id
    supplyBaseHandlers _ = id

instance Base Nil where
    dropToBasePrompt = id
    supplyBaseHandlers _ = id

supplyBase :: (Base es, Monad m, EnvFunctors (BasePrompt es)) => Env m es -> Env m (BasePrompt es) -> Env m es
supplyBase (Env v) (Env v') = Env $ supplyBaseHandlers v (mapHandlers (supplyBase (Env v)) v')

interpret ::
    ( Monad m
    , EnvFunctor e
    , EnvFunctors (BasePrompt es)
    , Base es
    ) =>
    (forall x. e (EffT es m) x -> EffT es m x) ->
    EffT (e :+ es) m a ->
    EffT es m a
interpret f (EffT m) =
    EffT $
        cmapCtlT
            (\r -> Handler (EffCtlT . cmapCtlT (supplyBase r) . unEffT . f . fromCtl) (dropToBasePrompt r) !: r)
            m

prompt :: (Monad m, EnvFunctors es) => EffT (a :/ es) m a -> EffT es m a
prompt (EffT m) = EffT $ cmapCtlT (mapEnv ConsPrompt) $ C.prompt id $ const m

runPure :: EffT Nil Identity a -> a
runPure = C.runPure (Env Nil) . unEffT

runEffT :: (Functor f) => EffT Nil f a -> f a
runEffT = runCtlT (Env Nil) . unEffT

newtype FirstOrder (e :: Effect) f a = FirstOrder (e f a)

instance (forall f g x. Coercible (e f x) (e g x)) => EnvFunctor (FirstOrder e) where
    cmapEnv _ = coerce
    fromCtl = coerce
    toCtl = coerce

data Throw e :: Effect where
    Throw :: e -> Throw e f a

data Catch e :: Effect where
    Catch :: f a -> (e -> f a) -> Catch e f a

deriving via FirstOrder (Throw e) instance EnvFunctor (Throw e)

instance EnvFunctor (Catch e) where
    cmapEnv f (Catch m k) = Catch (EffCtlT $ cmapCtlT f $ unEffCtlT m) (EffCtlT . cmapCtlT f . unEffCtlT . k)
    fromCtl = coerce
    toCtl = coerce
