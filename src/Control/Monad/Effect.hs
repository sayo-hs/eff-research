{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal (CtlT (CtlT), Member, PromptFrame (PromptFrame), Underlying, Unlift (withRunInBase), abort, delimitAbort, embed, hoistCtlT, weaken, type (<))
import Control.Monad.MultiPrompt.Formal qualified as C
import Control.Monad.Trans.Reader (ReaderT)
import Data.Coerce (coerce)
import Data.Data (Proxy (Proxy))
import Data.Function ((&))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO, liftIO, withRunInIO)

type Effect = (Type -> Type) -> Type -> Type
data EffectFrame = E Effect PromptFrame

type family PromptFrames es where
    PromptFrames ('E _ p : es) = p : PromptFrames es
    PromptFrames '[] = '[]

-- | A effect handler.
data Handler e r m where
    Handler :: (forall x. e (EnvCtlT r (p : Underlying p) m) x -> EnvCtlT r (p : Underlying p) m x) -> Handler ('E e p) r m

-- | Vector of handlers.
data Handlers (es :: [EffectFrame]) r m where
    Cons :: Handler e r m -> Handlers es r m -> Handlers (e : es) r m
    Nil :: Handlers '[] r m

data Membership ff es p = Membership
    { getHandler :: forall r m. Handlers es r m -> Handler ('E ff p) r m
    , updateHandler :: forall r m. Handler ('E ff p) r m -> Handlers es r m -> Handlers es r m
    }

-- | Type-level search over elements in a vector.
class Elem ff (es :: [EffectFrame]) p | ff es -> p where
    membership :: Membership ff es p

instance Elem ff ('E ff p : es) p where
    membership =
        Membership
            { getHandler = \(Cons h _) -> h
            , updateHandler = \h (Cons _ hs) -> Cons h hs
            }

instance {-# OVERLAPPABLE #-} (Elem ff es p) => Elem ff ('E ff' p' : es) p where
    membership =
        Membership
            { getHandler = \(Cons _ hs) -> getHandler membership hs
            , updateHandler = \h (Cons h' hs) -> Cons h' $ updateHandler membership h hs
            }

-- | Prepend to the handler vector.
(!:) :: Handler e r m -> Handlers es r m -> Handlers (e : es) r m
(!:) = Cons

newtype EnvCtlT r ps (m :: Type -> Type) a = EnvCtlT {unEnvCtlT :: ReaderT r (CtlT ps (EnvCtlT r ps m)) a}
    deriving (Functor, Applicative, Monad)

{-
runEnvT :: Handlers es m -> EnvT es m a -> m a
runEnvT = flip unEnvT

liftEnvT :: m a -> EnvT es m a
liftEnvT m = EnvT $ const m

instance (Applicative m) => Applicative (EnvT es m) where
    pure x = EnvT \_ -> pure x
    EnvT ff <*> EnvT fa = EnvT \v -> ff v <*> fa v

instance (Monad m) => Monad (EnvT es m) where
    EnvT m >>= f = EnvT \v -> m v >>= runEnvT v . f

instance (MonadIO m) => MonadIO (EnvT es m) where
    liftIO m = EnvT \_ -> liftIO m

instance (MonadUnliftIO m) => MonadUnliftIO (EnvT es m) where
    withRunInIO f = EnvT \v -> withRunInIO \run -> f $ run . runEnvT v

instance (Unlift b f) => Unlift b (EnvT es f) where
    withRunInBase f = EnvT \v -> withRunInBase \run -> f $ run . runEnvT v

-- | An effect monad transformer built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: EnvT es (CtlT (PromptFrames es) (EnvT es m)) a}
    deriving (Functor, Applicative, Monad, MonadIO)

deriving instance (MonadUnliftIO m, PromptFrames es ~ '[]) => MonadUnliftIO (EffT es m)
deriving instance (Unlift b f, PromptFrames es ~ '[], Functor f) => Unlift b (EffT es f)

overwrite :: CtlT (PromptFrames es) (EnvT es m) a -> EffT es m a
overwrite (CtlT (EnvT m)) = EffT $ EnvT \v -> undefined

interpret :: (Monad m) => Handler e (EffT es m) -> EffT (e : es) m a -> EffT es m a
interpret (Handler h) (EffT (EnvT m)) = EffT $ EnvT \v -> undefined $ m $ Handler (hoistCtlT (undefined . runEnvT v . unEffT) undefined . h . undefined) !: undefined v
-}

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

-- | A type-class for higher-order effects.
class HFunctor ff where
    hfmap :: (forall x. f x -> g x) -> ff f a -> ff g a

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
