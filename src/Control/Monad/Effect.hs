{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal (
    CtlT (CtlT),
    Member,
    PromptFrame (PromptFrame),
    Underlying,
    Unlift,
    abort,
    delimitAbort,
    embed,
    mapEnv,
    prompt,
    runCtlT,
    unCtlT,
    type (<),
 )
import Control.Monad.MultiPrompt.Formal qualified as C
import Data.Coerce (Coercible, coerce)
import Data.Data (Proxy (Proxy))
import Data.Function ((&))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO)

type Effect = (Type -> Type) -> Type -> Type
type data EffectFrame = E Effect Resumption

type data Resumption = Ctl PromptFrame | Tail [PromptFrame]

type family PromptFrames es where
    PromptFrames (E _ (Ctl p) : es) = p : PromptFrames es
    PromptFrames (E _ (Tail _) : es) = PromptFrames es
    PromptFrames '[] = '[]

-- | A effect handler.
data Handler e r m where
    ControlHandler :: (forall x. e (CtlT (p : Underlying p) r m) x -> CtlT (p : Underlying p) r m x) -> Handler (E e (Ctl p)) r m
    TailHandler :: (forall x. e (CtlT u r m) x -> CtlT u r m x) -> Handler (E e (Tail u)) r m

-- | A type-class for higher-order effects.
class HFunctor ff where
    hfmap :: (Monad m, HFunctors es, HFunctors es') => (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> ff (EffT_ u es m) a -> ff (EffT_ u es' m) a
    hfmapEmbed :: (Monad m) => (u < ps) => ff (EffT_ u es m) a -> ff (EffT_ ps es m) a

mapHandler :: (HFunctor ff, HFunctors es, HFunctors es', Monad m) => (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> Handler (E ff r) (Env es' m) m -> Handler (E ff r) (Env es m) m
mapHandler f g = \case
    ControlHandler h -> ControlHandler $ mapEnv f g . h . hfmap f g
    TailHandler h -> TailHandler $ mapEnv f g . h . hfmap f g

-- | Vector of handlers.
data Handlers (es :: [EffectFrame]) r m where
    Cons :: Handler e r m -> Handlers es r m -> Handlers (e : es) r m
    Nil :: Handlers '[] r m

class HFunctors es where
    mapHandlers :: (HFunctors es1, HFunctors es2, Monad m) => (Env es1 m -> Env es2 m) -> (Env es2 m -> Env es1 m) -> Handlers es (Env es2 m) m -> Handlers es (Env es1 m) m

instance HFunctors '[] where
    mapHandlers _ _ Nil = Nil

instance (HFunctor ff, HFunctors es) => HFunctors (E ff r : es) where
    mapHandlers f g (Cons h hs) = Cons (mapHandler f g h) (mapHandlers f g hs)

data Membership ff es p = Membership
    { getHandler :: forall r m. Handlers es r m -> Handler (E ff p) r m
    , updateHandler :: forall r m. Handler (E ff p) r m -> Handlers es r m -> Handlers es r m
    }

-- | Type-level search over elements in a vector.
class Elem ff (es :: [EffectFrame]) p | ff es -> p where
    membership :: Membership ff es p

instance Elem ff (E ff p : es) p where
    membership =
        Membership
            { getHandler = \(Cons h _) -> h
            , updateHandler = \h (Cons _ hs) -> Cons h hs
            }

instance {-# OVERLAPPABLE #-} (Elem ff es p) => Elem ff (E ff' p' : es) p where
    membership =
        Membership
            { getHandler = \(Cons _ hs) -> getHandler membership hs
            , updateHandler = \h (Cons h' hs) -> Cons h' $ updateHandler membership h hs
            }

newtype Env es m = Env {unEnv :: Handlers es (Env es m) m}

-- | Prepend to the handler vector environment.
(!:) :: (HFunctors es, HFunctor ff, Monad m) => Handler (E ff r) (Env es m) m -> Env es m -> Env (E ff r : es) m
h !: Env hs = Env $ Cons (mapHandler dropEnv (h !:) h) (mapHandlers dropEnv (h !:) hs)

-- | Remove the head of the handler vector environment.
dropEnv :: (HFunctors es, HFunctor ff, Monad m) => Env (E ff r : es) m -> Env es m
dropEnv (Env (Cons h hs)) = Env $ mapHandlers (consHandler h) dropEnv hs

consHandler :: (HFunctors es, HFunctor ff, Monad m) => Handler (E ff r) (Env (E ff r : es) m) m -> Env es m -> Env (E ff r : es) m
consHandler h = (mapHandler (consHandler h) dropEnv h !:)

mapSubEnv :: (HFunctors es, HFunctors es', HFunctor e, Monad m) => (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> EffT_ u (E e r : es') m a -> EffT_ u (E e r : es) m a
mapSubEnv f g = mapEnv (alterSubEnv g f) (alterSubEnv f g)

alterSubEnv :: (HFunctors es, HFunctors es', HFunctor e, Monad m) => (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> Env (E e r : es') m -> Env (E e r : es) m
alterSubEnv f g v@(Env (Cons h _)) =
    let h' = mapHandler (alterSubEnv g f) (alterSubEnv f g) h
     in Env $ Cons h' (mapHandlers dropEnv (consHandler h') $ unEnv $ g (dropEnv v))

data Test :: Effect where
    Test :: (HFunctor e) => EffT_ u (E e r : es) m a -> Test (EffT_ u es m) a

instance HFunctor Test where
    hfmap f g (Test m) = Test $ mapSubEnv g f m
    hfmapEmbed (Test m) = Test $ embed Proxy m

type EffT_ ps es m = CtlT ps (Env es m) m

-- | An effect monad built on top of a multi-prompt/control monad.
type EffT es m = CtlT (PromptFrames es) (Env es m) m

interpretCtl ::
    (Monad m, p ~ 'PromptFrame a (PromptFrames es), HFunctor e, HFunctors es) =>
    (forall x. Proxy p -> e (EffT_ (p : PromptFrames es) es m) x -> EffT_ (p : PromptFrames es) es m x) ->
    EffT (E e (Ctl p) : es) m a ->
    EffT es m a
interpretCtl h = prompt . mapEnv (ControlHandler (h Proxy) !:) dropEnv

interpret ::
    (Monad m, u ~ PromptFrames es, HFunctor e, HFunctors es) =>
    (forall x. e (EffT_ u es m) x -> EffT_ u es m x) ->
    EffT (E e (Tail u) : es) m a ->
    EffT es m a
interpret h = mapEnv (TailHandler h !:) dropEnv

sendCtl ::
    (p : Underlying p < ps, Monad m, HFunctor ff) =>
    Membership ff es (Ctl p) ->
    ff (EffT_ (p : Underlying p) es m) a ->
    EffT_ ps es m a
sendCtl i e =
    CtlT \r@(Env v) -> case getHandler i v of
        ControlHandler h -> unCtlT (embed Proxy $ h $ hfmapEmbed e) r

send :: (u < ps, Monad m, HFunctor ff) => Membership ff es (Tail u) -> ff (EffT_ u es m) a -> EffT_ ps es m a
send i e =
    CtlT \r@(Env v) -> case getHandler i v of
        TailHandler h -> unCtlT (embed Proxy $ h $ hfmapEmbed e) r

runPure :: EffT '[] Identity a -> a
runPure = C.runPure (Env Nil)

runEffT :: (Functor f) => EffT '[] f a -> f a
runEffT = runCtlT (Env Nil)

newtype FirstOrder (e :: Effect) f a = FirstOrder (e f a)

instance (forall f g x. Coercible (e f x) (e g x)) => HFunctor (FirstOrder e) where
    hfmap _ _ = coerce
    hfmapEmbed = coerce

data Throw e :: Effect where
    Throw :: e -> Throw e f a

data Catch e :: Effect where
    Catch :: f a -> (e -> f a) -> Catch e f a

deriving via FirstOrder (Throw e) instance HFunctor (Throw e)

instance HFunctor (Catch e) where
    hfmap f g (Catch m hdl) = Catch (mapEnv g f m) (mapEnv g f . hdl)
    hfmapEmbed (Catch m hdl) = Catch (embed Proxy m) (embed Proxy . hdl)

runThrow ::
    forall m e a es.
    (Monad m, HFunctors es) =>
    EffT (E (Throw e) (Ctl ('PromptFrame (Either e a) (PromptFrames es))) : es) m a ->
    EffT es m (Either e a)
runThrow m =
    Right <$> m & interpretCtl \p -> \case
        Throw e -> abort p $ Left e

runCatch ::
    forall e m a ps es ans r.
    (HFunctors es, Member ('PromptFrame (Either e ans) ps) r, Monad m) =>
    EffT (E (Catch e) (Tail (PromptFrames es)) : es) m a ->
    EffT_ r es m a
runCatch = interpret \case
    Catch m' hdl ->
        let p = Proxy @('PromptFrame (Either e ans) ps)
         in delimitAbort p m' \case
                Left e -> hdl e
                x -> abort p x

perform :: (Elem e es u) => (Membership e es u -> r) -> r
perform f = f membership

throw :: forall e es u m a ps ans. ('PromptFrame ans u : u < ps, Monad m) => Membership (Throw e) es (Ctl ('PromptFrame ans u)) -> e -> EffT_ ps es m a
throw i = sendCtl i . Throw

catch ::
    forall e es u m a ps.
    (u < ps, Monad m) =>
    Membership (Catch e) es (Tail u) ->
    EffT_ u es m a ->
    (e -> EffT_ u es m a) ->
    EffT_ ps es m a
catch i m h = send i $ Catch m h

test :: Either String (Either Int Int)
test = runPure . runThrow . runThrow . runCatch @String . runCatch @Int $ do
    perform
        catch
        do
            -- perform catch (perform (throw @Int) 123456) \(i :: Int) -> perform throw $ show i
            undefined
        \(s :: String) -> pure (length s)

-- >>> test
-- Left ""
