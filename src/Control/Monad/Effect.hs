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
import Control.Monad.Trans.Reader (ReaderT (ReaderT))
import Data.Coerce (Coercible, coerce)
import Data.Data (Proxy (Proxy), (:~:) (Refl))
import Data.FTCQueue
import Data.Function (fix, (&))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO)

-- | An effect monad built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: CtlEnvT (PromptFrames es) es m a}
    deriving newtype (Functor, Applicative, Monad)

type EffT_ es m = CtlEnvT (PromptFrames es) es m

type CtlReaderT ps r m = CtlT ps (ReaderT r m)

mapCtlReaderT :: (Monad m) => (r -> r') -> (r' -> r) -> CtlReaderT ps r m a -> CtlReaderT ps r' m a
mapCtlReaderT f g (CtlT (ReaderT m)) =
    CtlT $ ReaderT \v ->
        m (g v) <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ forCtls ctls \case
                Control ctl q -> Control (mapCtlReaderT f g . ctl . (mapCtlReaderT g f .)) (tsingleton $ mapCtlReaderT f g . qApp q)

type Effect = (Type -> Type) -> Type -> Type
type data EffectFrame = E Effect Resumption
type data Resumption = Tail [PromptFrame] | Ctl PromptFrame

type family PromptFrames es where
    PromptFrames (E _ (Ctl p) : es) = p : PromptFrames es
    PromptFrames (E _ (Tail _) : es) = PromptFrames es
    PromptFrames '[] = '[]

-- | A effect handler.
data Handler e r m where
    CtlHandler ::
        ( forall x.
          e (CtlReaderT (Prompt ans u : u) r m) x ->
          CtlReaderT (Prompt ans u : u) r m x
        ) ->
        Handler (E e (Ctl (Prompt ans u))) r m

-- | Vector of handlers.
data Handlers (es :: [EffectFrame]) r m where
    Cons :: Handler e r m -> Handlers es r m -> Handlers (e : es) r m
    Nil :: Handlers '[] r m

class EnvFunctors es where
    mapHandlers ::
        (EnvFunctors es1, EnvFunctors es2, Monad m) =>
        (Env es1 m -> Env es2 m) ->
        (Env es2 m -> Env es1 m) ->
        Handlers es (Env es1 m) m ->
        Handlers es (Env es2 m) m

instance EnvFunctors '[] where
    mapHandlers _ _ Nil = Nil

instance (EnvFunctor ff, EnvFunctors es) => EnvFunctors (E ff r : es) where
    mapHandlers f g (Cons h hs) = Cons (mapHandler f g h) (mapHandlers f g hs)

mapHandler ::
    (EnvFunctor ff, EnvFunctors es, EnvFunctors es', Monad m) =>
    (Env es m -> Env es' m) ->
    (Env es' m -> Env es m) ->
    Handler (E ff r) (Env es m) m ->
    Handler (E ff r) (Env es' m) m
mapHandler f g = \case
    CtlHandler h -> CtlHandler $ mapCtlReaderT f g . h . mapEnv g f

newtype Env es m = Env {unEnv :: Handlers es (Env es m) m}

type CtlEnvT ps es m = CtlReaderT ps (Env es m) m

-- | A type-class for higher-order effects.
class EnvFunctor ff where
    mapEnv :: (Monad m, EnvFunctors es, EnvFunctors es') => (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> ff (CtlEnvT u es m) a -> ff (CtlEnvT u es' m) a
    underEnv :: (Monad m) => (Member p ps, EnvFunctors es) => p :~: Prompt ans u -> ff (CtlEnvT u es m) a -> ff (CtlEnvT ps es m) a

-- | Prepend to the handler vector environment.
(!:) :: (EnvFunctors es, EnvFunctor ff, Monad m) => Handler (E ff r) (Env es m) m -> Env es m -> Env (E ff r : es) m
h !: Env hs = Env $ Cons (mapHandler (h !:) dropEnv h) (mapHandlers (h !:) dropEnv hs)

-- | Remove the head of the handler vector environment.
dropEnv :: (EnvFunctors es, EnvFunctor ff, Monad m) => Env (E ff r : es) m -> Env es m
dropEnv (Env (Cons h hs)) = Env $ mapHandlers dropEnv (consHandler h) hs

consHandler ::
    (EnvFunctors es, EnvFunctor ff, Monad m) =>
    Handler (E ff r) (Env (E ff r : es) m) m ->
    Env es m ->
    Env (E ff r : es) m
consHandler h = (mapHandler dropEnv (consHandler h) h !:)

mapSubEnv ::
    (EnvFunctors es, EnvFunctors es', EnvFunctor e, Monad m) =>
    (Env es m -> Env es' m) ->
    (Env es' m -> Env es m) ->
    CtlEnvT u (E e r : es') m a ->
    CtlEnvT u (E e r : es) m a
mapSubEnv f g = mapCtlReaderT (alterSubEnv f g) (alterSubEnv g f)

alterSubEnv ::
    (EnvFunctors es, EnvFunctors es', EnvFunctor e, Monad m) =>
    (Env es m -> Env es' m) ->
    (Env es' m -> Env es m) ->
    Env (E e r : es') m ->
    Env (E e r : es) m
alterSubEnv f g v@(Env (Cons h _)) =
    let h' = mapHandler (alterSubEnv f g) (alterSubEnv g f) h
     in Env $ Cons h' (mapHandlers (consHandler h') dropEnv $ unEnv $ g (dropEnv v))

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

interpretCtl ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p x. p :~: Prompt a (PromptFrames es) -> e (CtlEnvT (p : PromptFrames es) es m) x -> CtlEnvT (p : PromptFrames es) es m x) ->
    (forall p. p :~: Prompt a (PromptFrames es) -> EffT (E e (Ctl p) : es) m a) ->
    EffT es m a
interpretCtl h m =
    EffT $ prompt \Refl -> mapCtlReaderT dropEnv (CtlHandler (h Refl) !:) $ unEffT (m Refl)

interpretBy ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (a -> EffT es m b) ->
    (forall p x. p :~: Prompt b (PromptFrames es) -> e (CtlEnvT (p : PromptFrames es) es m) x -> (x -> EffT es m b) -> EffT es m b) ->
    (forall p. p :~: Prompt b (PromptFrames es) -> EffT (E e (Ctl p) : es) m a) ->
    EffT es m b
interpretBy ret hdl m =
    interpretCtl
        (\p e -> control p \k -> unEffT $ hdl p e (EffT . k))
        \p -> do
            x <- m p
            raise $ ret x

raise :: (Monad m) => EffT es m a -> EffT (E e (Ctl p) : es) m a
raise (EffT m) = EffT $ raiseCtlT $ mapCtlReaderT undefined undefined m

{-
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
-}

data Test1 :: Effect where
    Test1 :: (EnvFunctor e) => (forall u. CtlEnvT (Prompt a u : u) (E e (Ctl (Prompt a u)) : es) m a) -> Test1 (CtlEnvT ps es m) a

instance EnvFunctor Test1 where
    mapEnv f g (Test1 m) = Test1 $ mapSubEnv g f m
    underEnv _ (Test1 m) = Test1 m

data Test2 :: Effect where
    Test2 :: (EnvFunctor e) => (forall u. CtlEnvT ps (E e u : es) m a) -> Test2 (CtlEnvT ps es m) a

instance EnvFunctor Test2 where
    mapEnv f g (Test2 m) = Test2 $ mapSubEnv g f m
    underEnv p (Test2 m) = Test2 $ under p m
