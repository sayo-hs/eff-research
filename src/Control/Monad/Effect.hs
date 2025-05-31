{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal (CtlT, Member, Unlift (withRunInBase), abort, delimitAbort, embed, type (<))
import Control.Monad.MultiPrompt.Formal qualified as C
import Data.Coerce (coerce)
import Data.Data (Proxy (Proxy))
import Data.Function ((&))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO, liftIO, withRunInIO)

type Effect = (Type -> Type) -> Type -> Type
data Frame = E Effect [Type]

-- | A effect handler.
data Handler e m where
    Handler :: (forall x. e (CtlT ps m) x -> CtlT ps m x) -> Handler ('E e ps) m

-- | Vector of handlers.
data Handlers (es :: [Frame]) m where
    Cons :: Handler e m -> Handlers es m -> Handlers (e : es) m
    Nil :: Handlers '[] m

data Membership ff es ps = Membership
    { getHandler :: forall m. Handlers es m -> Handler ('E ff ps) m
    , updateHandler :: forall m. Handler ('E ff ps) m -> Handlers es m -> Handlers es m
    }

-- | Type-level search over elements in a vector.
class Elem ff (es :: [Frame]) ps | ff es -> ps where
    membership :: Membership ff es ps

instance Elem ff ('E ff ps : es) ps where
    membership =
        Membership
            { getHandler = \(Cons h _) -> h
            , updateHandler = \h (Cons _ hs) -> Cons h hs
            }

instance {-# OVERLAPPABLE #-} (Elem ff es ps) => Elem ff ('E ff' ps' : es) ps where
    membership =
        Membership
            { getHandler = \(Cons _ hs) -> getHandler membership hs
            , updateHandler = \h (Cons h' hs) -> Cons h' $ updateHandler membership h hs
            }

-- | Prepend to the handler vector.
(!:) :: Handler e m -> Handlers es m -> Handlers (e : es) m
(!:) = Cons

-- | An effect monad transformer built on top of a multi-prompt/control monad.
newtype EffT es ps m a
    = EffT {unEffT :: Handlers es m -> CtlT ps m a}
    deriving (Functor)

interpretAll :: Handlers es m -> EffT es ps m a -> CtlT ps m a
interpretAll = flip unEffT

runEffT :: (Functor f) => EffT '[] '[] f a -> f a
runEffT = C.runCtlT . interpretAll Nil

runPure :: EffT '[] '[] Identity a -> a
runPure = C.runPure . interpretAll Nil

liftEffT :: CtlT ps m a -> EffT es ps m a
liftEffT m = EffT $ const m

instance (Monad m) => Applicative (EffT es ps m) where
    pure x = EffT \_ -> pure x
    EffT ff <*> EffT fa = EffT \v -> ff v <*> fa v

instance (Monad m) => Monad (EffT es ps m) where
    EffT m >>= f = EffT \v -> m v >>= interpretAll v . f

instance (MonadIO m) => MonadIO (EffT es ps m) where
    liftIO m = EffT \_ -> liftIO m

instance (MonadUnliftIO m) => MonadUnliftIO (EffT es '[] m) where
    withRunInIO f = EffT \v -> withRunInIO \run -> f $ run . interpretAll v

instance (Unlift b f, Functor f) => Unlift b (EffT es '[] f) where
    withRunInBase f = EffT \v -> withRunInBase \run -> f $ run . interpretAll v

withEffToCtl :: ((forall x. EffT es ps m x -> CtlT ps m x) -> CtlT ps m a) -> EffT es ps m a
withEffToCtl f = EffT \v -> f (interpretAll v)

trans :: (Handlers es' m -> Handlers es m) -> EffT es ps m a -> EffT es' ps m a
trans f (EffT withHandlerVec) = EffT $ withHandlerVec . f

-- | A type-class for higher-order effects.
class HFunctor ff where
    hfmap :: (forall x. f x -> g x) -> ff f a -> ff g a

send ::
    forall e es ps psUnder m a.
    (psUnder < ps, HFunctor e, Monad m) =>
    Membership e es psUnder ->
    e (EffT es psUnder m) a ->
    EffT es ps m a
send ix e =
    EffT \v ->
        case getHandler ix v of
            Handler h -> embed $ h $ hfmap (interpretAll v) e

prompt :: (Monad m) => EffT es (ans : ps) m ans -> EffT es ps m ans
prompt (EffT m) = EffT \v -> C.prompt_ $ m v

interpret ::
    (HFunctor e, Monad m) =>
    (forall x. Proxy ps -> e (EffT es (ans : ps) m) x -> EffT es (ans : ps) m x) ->
    EffT ('E e (ans : ps) : es) (ans : ps) m ans ->
    EffT es ps m ans
interpret f m = EffT \v -> interpretAll v $ prompt $ trans (Handler (interpretAll v . f Proxy . hfmap liftEffT) !:) m

interpretTail ::
    (HFunctor e) =>
    (forall x. e (EffT es ps m) x -> EffT es ps m x) ->
    EffT ('E e ps : es) ps m a ->
    EffT es ps m a
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
    EffT ('E (Throw e) (Either e a : ps) : es) (Either e a : ps) m a ->
    EffT es ps m (Either e a)
runThrow m =
    Right <$> m & interpret \p -> \case
        Throw e -> liftEffT $ abort p $ Left e

runCatch ::
    forall e m a ps es ans r.
    (Member (Either e ans) r ps, Elem (Throw e) es (Either e ans ': r), Monad m) =>
    EffT ('E (Catch e) ps : es) ps m a ->
    EffT es ps m a
runCatch = interpretTail \case
    Catch m' hdl ->
        withEffToCtl \run ->
            let p = Proxy @r
             in delimitAbort p (run m') \case
                    Left e -> run $ hdl e
                    x -> abort p x

perform :: (Elem e es psUnder) => (Membership e es psUnder -> r) -> r
perform f = f membership

throw :: forall e es r ps m a. (r < ps, Monad m) => Membership (Throw e) es r -> e -> EffT es ps m a
throw i = send i . Throw

catch :: forall e es r ps m a. (r < ps, Monad m) => Membership (Catch e) es r -> EffT es r m a -> (e -> EffT es r m a) -> EffT es ps m a
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
