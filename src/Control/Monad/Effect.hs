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
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.Coerce (Coercible, coerce)
import Data.Data (Proxy (Proxy), (:~:) (Refl))
import Data.FTCQueue
import Data.Function (fix, (&))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO)

-- | An effect monad built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: EffCtlT (PromptFrames es) es m a}

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
    mapEnv ::
        (Monad m) =>
        (Env es1 m -> Env es2 m) ->
        e (EffCtlT u es1 m) a ->
        e (EffCtlT u es2 m) a

cmapHandler :: (EnvFunctor e, Monad m) => (Env es1 m -> Env es2 m) -> Handler (E e r) es2 m -> Handler (E e r) es1 m
cmapHandler f = \case
    CtlHandler h v -> CtlHandler (h . mapEnv f) v

class EnvFunctors es where
    cmapHandlers :: (Monad m) => (Env es1 m -> Env es2 m) -> Handlers es es2 m -> Handlers es es1 m

instance EnvFunctors '[] where
    cmapHandlers _ Nil = Nil

instance (EnvFunctor e, EnvFunctors es) => EnvFunctors (E e r : es) where
    cmapHandlers f (Cons h hs) = Cons (cmapHandler f h) (cmapHandlers f hs)

(!:) :: (EnvFunctor e, EnvFunctors es, Monad m) => Handler (E e r) es m -> Env es m -> Env (E e r : es) m
h !: Env hs = Env $ Cons (cmapHandler dropEnv h) (cmapHandlers dropEnv hs)

dropEnv :: (EnvFunctor e, EnvFunctors es, Monad m) => Env (E e r : es) m -> Env es m
dropEnv (Env (Cons h hs)) = Env $ cmapHandlers (fix \f -> (cmapHandler f h !:)) hs

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
    (Member (Prompt ans r u) ps, Monad m, EnvFunctor e) =>
    p :~: Prompt ans r u ->
    Membership e es (Ctl p) ->
    e (EffCtlT (p : u) es m) a ->
    EffCtlT ps es m a
sendCtl p@Refl i e = CtlT \r@(Env hs) -> case getHandler i hs of
    CtlHandler h r' ->
        unCtlT (under p (\(Env hs') -> case getHandler i hs' of CtlHandler _ r'' -> r'') r' $ h e) r

interpretCtl ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p x. p :~: Prompt a (Env es m) ps -> e (EffCtlT (p : ps) es m) x -> EffCtlT (p : ps) es m x) ->
    (forall p. p :~: Prompt a (Env es m) ps -> EffCtlT (p : ps) (E e (Ctl p) : es) m a) ->
    EffCtlT ps es m a
interpretCtl h m =
    prompt (\r -> CtlHandler (h Refl) r !: r) \Refl -> m Refl

interpretBy ::
    (Monad m, EnvFunctor e, EnvFunctors es) =>
    (forall p. a -> EffT (E e (Ctl p) : es) m b) ->
    (forall p ps x. e (EffCtlT (p : ps) es m) x -> (x -> EffCtlT ps es m b) -> EffT es m b) ->
    (forall p. EffT (E e (Ctl p) : es) m a) ->
    EffT es m b
interpretBy ret hdl m =
    EffT $ interpretCtl
        (\p e -> control p \k -> unEffT $ hdl e k)
        \_ -> do
            x <- unEffT m
            unEffT $ ret x

{-
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
    mapEnv ::
        (Monad m, EnvFunctors es, EnvFunctors es') =>
        (Env es m -> Env es' m) ->
        (Env es' m -> Env es m) ->
        ff (CtlEnvT u es m) a ->
        ff (CtlEnvT u es' m) a

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

sendCtl ::
    (Member (Prompt ans u) (PromptFrames es), Monad m) =>
    p :~: Prompt ans u ->
    Membership e es (Ctl p) ->
    e (CtlEnvT (p : u) es m) a ->
    EffT es m a
sendCtl p@Refl i e = EffT $ CtlT $ ReaderT \r@(Env v) -> case getHandler i v of
    CtlHandler h -> runReaderT (unCtlT $ under' p $ h e) r

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

data Test2 :: Effect where
    Test2 :: (EnvFunctor e) => (forall u. CtlEnvT ps (E e u : es) m a) -> Test2 (CtlEnvT ps es m) a

instance EnvFunctor Test2 where
    mapEnv f g (Test2 m) = Test2 $ mapSubEnv g f m
-}
