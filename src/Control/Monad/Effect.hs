{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
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
    PromptFrame (PromptFrame),
    Underlying,
    Unlift,
    embed,
    mapEnv,
    prompt,
    unCtlT,
    type (<),
 )
import Data.Data (Proxy (Proxy))
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO)

type Effect = (Type -> Type) -> Type -> Type
type data EffectFrame = E Effect Resumption

type data Resumption = Control PromptFrame | Tail [PromptFrame]

type family PromptFrames es where
    PromptFrames (E _ (Control p) : es) = p : PromptFrames es
    PromptFrames (E _ (Tail _) : es) = PromptFrames es
    PromptFrames '[] = '[]

-- | A effect handler.
data Handler e r m where
    ControlHandler :: (forall x. e (CtlT (p : Underlying p) r m) x -> CtlT (p : Underlying p) r m x) -> Handler (E e (Control p)) r m
    TailHandler :: (forall x. e (CtlT u r m) x -> CtlT u r m x) -> Handler (E e (Tail u)) r m

-- | A type-class for higher-order effects.
class HFunctor ff where
    hfmap :: (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> ff (CtlT u (Env es m) m) a -> ff (CtlT u (Env es' m) m) a
    hfmapEmbed :: (u < PromptFrames es) => ff (EffT es m) a -> ff (CtlT u (Env es m) m) a

mapHandler :: (HFunctor ff, Monad m) => (Env es m -> Env es' m) -> (Env es' m -> Env es m) -> Handler (E ff r) (Env es' m) m -> Handler (E ff r) (Env es m) m
mapHandler f g = \case
    ControlHandler h -> ControlHandler $ mapEnv f g . h . hfmap f g
    TailHandler h -> TailHandler $ mapEnv f g . h . hfmap f g

-- | Vector of handlers.
data Handlers (es :: [EffectFrame]) r m where
    Cons :: Handler e r m -> Handlers es r m -> Handlers (e : es) r m
    Nil :: Handlers '[] r m

class HFunctors es where
    mapHandlers :: (Monad m) => (Env es' m -> Env es'' m) -> (Env es'' m -> Env es' m) -> Handlers es (Env es'' m) m -> Handlers es (Env es' m) m

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

-- | An effect monad transformer built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: CtlT (PromptFrames es) (Env es m) m a}
    deriving (Functor, Applicative, Monad, MonadIO)

deriving instance (MonadUnliftIO m, PromptFrames es ~ '[]) => MonadUnliftIO (EffT es m)
deriving instance (Unlift b f, PromptFrames es ~ '[], Functor f) => Unlift b (EffT es f)

interpretAlg ::
    (Monad m, p ~ 'PromptFrame a (PromptFrames es), HFunctor e, HFunctors es) =>
    Handler (E e (Control p)) (Env es m) m ->
    EffT (E e (Control p) : es) m a ->
    EffT es m a
interpretAlg h (EffT m) = EffT $ prompt $ mapEnv (h !:) dropEnv m

interpret ::
    (Monad m, u ~ PromptFrames es, HFunctor e, HFunctors es) =>
    Handler (E e (Tail u)) (Env es m) m ->
    EffT (E e (Tail u) : es) m a ->
    EffT es m a
interpret h (EffT m) = EffT $ mapEnv (h !:) dropEnv m

sendAlg ::
    (p : Underlying p < PromptFrames es, Monad m, HFunctor ff) =>
    Membership ff es (Control p) ->
    ff (EffT es m) a ->
    EffT es m a
sendAlg i e =
    EffT $ CtlT \r@(Env v) -> case getHandler i v of
        ControlHandler h -> unCtlT (embed Proxy $ h $ hfmapEmbed e) r

send :: (u < PromptFrames es, Monad m, HFunctor ff) => Membership ff es (Tail u) -> ff (EffT es m) a -> EffT es m a
send i e =
    EffT $ CtlT \r@(Env v) -> case getHandler i v of
        TailHandler h -> unCtlT (embed Proxy $ h $ hfmapEmbed e) r

{-
interpretAll :: Handlers es m -> EffT ('Frames es ps) m a -> CtlT ps m a
interpretAll = flip unEffT

runEffT :: (Functor f) => EffT ('Frames '[] '[]) f a -> f a
runEffT = C.runCtlT . interpretAll Nil

runPure :: EffT ('Frames '[] '[]) Identity a -> a
runPure = C.runPure . interpretAll Nil

liftEffT :: CtlT ps m a -> EffT ('Frames es ps) m a
liftEffT m = EffT $ const m

trans :: (Handlers es' m -> Handlers es m) -> EffT ('Frames es ps) m a -> EffT ('Frames es' ps) m a
trans f (EffT withHandlerVec) = EffT $ withHandlerVec . f

send ::
    forall e es ps psUnder m a.
    (psUnder < ps, HFunctor e, Monad m) =>
    Membership e es psUnder ->
    e (EffT ('Frames es psUnder) m) a ->
    EffT ('Frames es ps) m a
send ix e =
    EffT \v ->
        case getHandler ix v of
            Handler h -> embed $ h $ hfmap (interpretAll v) e

prompt :: (Monad m) => EffT ('Frames es ('PromptFrame ans ps : ps)) m ans -> EffT ('Frames es ps) m ans
prompt (EffT m) = EffT \v -> C.prompt_ $ m v

interpret ::
    (HFunctor e, Monad m) =>
    (forall x. Proxy ('PromptFrame ans ps : ps) -> e (EffT ('Frames es ('PromptFrame ans ps : ps)) m) x -> EffT ('Frames es ('PromptFrame ans ps : ps)) m x) ->
    EffT ('Frames ('E e ('PromptFrame ans ps : ps) : es) ('PromptFrame ans ps : ps)) m ans ->
    EffT ('Frames es ps) m ans
interpret f m = EffT \v -> interpretAll v $ prompt $ trans (Handler (interpretAll v . f Proxy . hfmap liftEffT) !:) m

interpretTail ::
    (HFunctor e) =>
    (forall x. e (EffT ('Frames es ps) m) x -> EffT ('Frames es ps) m x) ->
    EffT ('Frames ('E e ps : es) ps) m a ->
    EffT ('Frames es ps) m a
interpretTail f m = EffT \v -> interpretAll v $ trans (Handler (interpretAll v . f . hfmap liftEffT) !:) m

data Throw e :: Effect where
    Throw :: e -> Throw e f a

data Catch e :: Effect where
    Catch :: f a -> (e -> f a) -> Catch e f a

instance HFunctor (Throw e) where
    hfmap _ = coerce

instance HFunctor (Catch e) where
    hfmap f = \case
        Catch m hdl -> Catch (f m) (f . hdl)

runThrow ::
    forall m e a ps es.
    (Monad m) =>
    EffT ('Frames ('E (Throw e) ('PromptFrame (Either e a) ps : ps) : es) ('PromptFrame (Either e a) ps : ps)) m a ->
    EffT ('Frames es ps) m (Either e a)
runThrow m =
    Right <$> m & interpret \p -> \case
        Throw e -> liftEffT $ abort p $ Left e

runCatch ::
    forall e m a ps es ans r.
    (Member ('PromptFrame (Either e ans) ps) r, Elem (Throw e) es r, Monad m) =>
    EffT ('Frames ('E (Catch e) ps : es) ps) m a ->
    EffT ('Frames es ps) m a
runCatch = interpretTail \case
    Catch m' hdl ->
        withEffToCtl \run ->
            let p = Proxy @('PromptFrame (Either e ans) ps)
             in delimitAbort p (run m') \case
                    Left e -> run $ hdl e
                    x -> abort p x

perform :: (Elem e es psUnder) => (Membership e es psUnder -> r) -> r
perform f = f membership

throw :: forall e es r ps m a. (r < ps, Monad m) => Membership (Throw e) es r -> e -> EffT ('Frames es ps) m a
throw i = send i . Throw

catch :: forall e es r ps m a. (r < ps, Monad m) => Membership (Catch e) es r -> EffT ('Frames es r) m a -> (e -> EffT ('Frames es r) m a) -> EffT ('Frames es ps) m a
catch i m h = send i $ Catch m h

test :: Either String (Either Int Int)
test = runPure . runThrow . runThrow . runCatch @String . runCatch @Int $ do
    perform
        catch
        do
            perform catch (perform (throw @Int) 123456) \(i :: Int) -> perform throw $ show i
        \(s :: String) -> pure (length s)

-- >>> test
-- Right (Right 6)
-}
