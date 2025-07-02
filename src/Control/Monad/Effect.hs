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
    FreerT (FreerT),
    PromptFrame (..),
    Sub,
    cmapCtlT,
    runCtlT,
    runFreerT,
    under,
 )
import Control.Monad.MultiPrompt.Formal qualified as C
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Type.Equality (gcastWith, (:~:) (Refl))

type Effect = (Type -> Type) -> Type -> Type

infixr 6 :+
infixr 6 :/

type data Frames = Type :/ Frames | Effect :+ Frames | Nil

type data Frame = E Effect | P Type

type family ConsFrame e = r | r -> e where
    ConsFrame (E e) = (:+) e
    ConsFrame (P ans) = (:/) ans

type family Prompts m es where
    Prompts m (_ :+ es) = Prompts m es
    Prompts m (ans :/ es) = Prompt ans (Env m (ans :/ es)) : Prompts m (DropToPromptBase es)
    Prompts _ Nil = '[]

type family Effects es where
    Effects (e :+ es) = e : Effects es
    Effects (_ :/ es) = Effects es
    Effects Nil = '[]

type family FrameList es where
    FrameList (e :+ es) = E e : FrameList es
    FrameList (ans :/ es) = P ans : FrameList es
    FrameList Nil = '[]

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
data Handler (m :: Type -> Type) (w :: Frames) (e :: Effect) (u :: Frames)
    = Handler
    { handler :: forall x. e (EffCtlT (Prompts m u) w m) x -> EffCtlT (Prompts m u) u m x
    , envOnHandler :: Env m u
    }

-- | Vector of handlers.
data Handlers (m :: Type -> Type) (w :: Frames) (es :: Frames) where
    ConsHandler :: Handler m w e (DropToPromptBase es) -> Handlers m w es -> Handlers m w (e :+ es)
    ConsPrompt :: Handlers m w es -> Handlers m w (ans :/ es)
    Nil :: Handlers w m Nil

-- | An effect monad built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: CtlT (Prompts m (DropToPromptBase es)) (Env m es) m a}
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

    fromCtl :: e (EffCtlT (Prompts m (DropToPromptBase es)) es m) a -> e (EffT es m) a
    toCtl :: e (EffT es m) a -> e (EffCtlT (Prompts m (DropToPromptBase es)) es m) a

mapHandler ::
    (EnvFunctor e, Monad m, EnvFunctors es1, EnvFunctors es2) =>
    (Env m es1 -> Env m es2) ->
    Handler m es1 e u ->
    Handler m es2 e u
mapHandler f = \case
    Handler h v -> Handler (h . cmapEnv f) v

(!:) ::
    (EnvFunctor e, EnvFunctors es, Monad m) =>
    Handler m es e (DropToPromptBase es) ->
    Env m es ->
    Env m (ConsFrame (E e) es)
h@(Handler _ _) !: Env hs = Env $ ConsHandler (mapHandler (h !:) h) (mapHandlers (h !:) hs)

class IsFrame e where
    dropEnv :: (EnvFunctors es, Monad m) => Env m (ConsFrame e es) -> Env m es
    dropHandler :: (EnvFunctors es, Monad m) => Handlers m w (ConsFrame e es) -> Handlers m w es

instance (EnvFunctor e) => IsFrame (E e) where
    dropEnv (Env (ConsHandler _ hs)) = Env $ mapHandlers dropEnv hs
    dropHandler (ConsHandler _ hs) = hs

instance IsFrame (P ans) where
    dropEnv (Env (ConsPrompt hs)) = Env $ mapHandlers dropEnv hs
    dropHandler (ConsPrompt hs) = hs

data Membership e es u m = Membership
    { getHandler :: forall w. Handlers m w es -> Handler m w e (DropToPromptBase u)
    , promptEvidence :: Sub (Prompts m (DropToPromptBase u)) (Prompts m (DropToPromptBase es))
    , dropHandlersToUnder :: forall w. Handlers m w es -> Handlers m w u
    }

mapUnder ::
    (DropToPromptBase es ~ DropToPromptBase es') =>
    (Handlers m w es -> Handlers m w es') ->
    Handlers m w (e :+ es) ->
    Handlers m w (e :+ es')
mapUnder f (ConsHandler h hs) = ConsHandler h (f hs)

type family a == b where
    a == a = 'True
    _ == _ = 'False

-- | Type-level search over elements in a vector.
class
    (EnvFunctors es, EnvFunctors u, Monad m, full ~ DropToPromptBase u == DropToPromptBase es) =>
    Elem e (es :: Frames) full u m
        | e es -> u
    where
    membership :: Membership e es u m

instance (PromptBase m es, EnvFunctor e, Monad m) => Elem e (e :+ es) 'True (e :+ es) m where
    membership =
        Membership
            { getHandler = \(ConsHandler h _) -> h
            , promptEvidence = gcastWith (promptBaseEquality @m @es) C.sub
            , dropHandlersToUnder = id
            }

instance
    {-# OVERLAPPABLE #-}
    (Elem e es 'True es m, EnvFunctor e') =>
    Elem e (e' :+ es) 'True (e' :+ es) m
    where
    membership =
        let ms = membership @e @es @'True @es @m
         in Membership
                { getHandler = \(ConsHandler _ hs) -> getHandler membership hs
                , promptEvidence = promptEvidence ms
                , dropHandlersToUnder = mapUnder $ dropHandlersToUnder ms
                }

instance
    {-# OVERLAPPABLE #-}
    (Elem e es 'False u m, EnvFunctor e') =>
    Elem e (e' :+ es) 'False u m
    where
    membership =
        let ms = membership @e @es @'False @u @m
         in Membership
                { getHandler = \(ConsHandler _ hs) -> getHandler membership hs
                , promptEvidence = promptEvidence ms
                , dropHandlersToUnder = dropHandlersToUnder ms . dropHandler
                }

instance
    ( Elem e es full u m
    , (DropToPromptBase u == (ans :/ es)) ~ 'False
    , EnvFunctors u
    , Monad m
    ) =>
    Elem e (ans :/ es) 'False u m
    where
    membership =
        Membership
            { getHandler = \(ConsPrompt hs) -> getHandler membership hs
            , promptEvidence = C.Sub $ C.There . C.embed (promptEvidence $ membership @e @es @full @u @m)
            , dropHandlersToUnder = dropHandlersToUnder $ membership @e
            }

sendCtl ::
    forall e ps es u m a.
    (PromptBase m u, Monad m) =>
    Sub (Prompts m u) ps ->
    Membership e es u m ->
    e (EffCtlT (Prompts m u) es m) a ->
    EffCtlT ps es m a
sendCtl sub i e =
    EffCtlT $ CtlT $ FreerT $ ReaderT \r@(Env hs) ->
        let Handler h r' = getHandler i hs
         in (`runReaderT` r)
                . runFreerT
                . unCtlT
                . under sub (envOnHandler . getHandler i . unEnv) r'
                . unEffCtlT
                $ gcastWith (promptBaseEquality @m @u)
                $ h e

send ::
    forall m u e es a.
    (PromptBase m u, Monad m, EnvFunctor e, EnvFunctors es) =>
    Membership e es u m ->
    e (EffT u m) a ->
    EffT es m a
send i e =
    gcastWith (promptBaseEquality @m @u) $
        EffT . unEffCtlT $
            sendCtl (promptEvidence i) i $
                cmapEnv (mapEnv $ dropHandlersToUnder i) $
                    toCtl e

class (EnvFunctors es) => PromptBase m es where
    promptBaseEquality :: Prompts m es :~: Prompts m (DropToPromptBase es)
    dropEnvToPromptBase :: (Monad m) => Env m es -> Env m (DropToPromptBase es)
    supplyPromptBaseHandlers :: (Monad m) => Handlers m w es -> Handlers m w (DropToPromptBase es) -> Handlers m w es

type family DropToPromptBase es where
    DropToPromptBase (_ :+ es) = DropToPromptBase es
    DropToPromptBase (ans :/ es) = ans :/ es
    DropToPromptBase Nil = Nil

instance (EnvFunctor e, PromptBase m es) => PromptBase m (e :+ es) where
    promptBaseEquality = case promptBaseEquality @m @es of
        Refl -> Refl

    dropEnvToPromptBase = dropEnvToPromptBase . dropEnv

    supplyPromptBaseHandlers (ConsHandler h hs) hs' = ConsHandler h $ supplyPromptBaseHandlers hs hs'

instance (EnvFunctors es) => PromptBase m (ans :/ es) where
    promptBaseEquality = Refl
    dropEnvToPromptBase = id
    supplyPromptBaseHandlers _ = id

instance PromptBase m Nil where
    promptBaseEquality = Refl
    dropEnvToPromptBase = id
    supplyPromptBaseHandlers _ = id

supplyBase :: (PromptBase m es, Monad m, EnvFunctors (DropToPromptBase es)) => Env m es -> Env m (DropToPromptBase es) -> Env m es
supplyBase (Env v) (Env v') = Env $ supplyPromptBaseHandlers v (mapHandlers (supplyBase (Env v)) v')

interpret ::
    ( Monad m
    , EnvFunctor e
    , EnvFunctors (DropToPromptBase es)
    , PromptBase m es
    ) =>
    (forall x. e (EffT es m) x -> EffT es m x) ->
    EffT (e :+ es) m a ->
    EffT es m a
interpret f (EffT m) =
    EffT $
        cmapCtlT
            (\r -> Handler (EffCtlT . cmapCtlT (supplyBase r) . unEffT . f . fromCtl) (dropEnvToPromptBase r) !: r)
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
