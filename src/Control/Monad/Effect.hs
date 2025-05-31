{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal (CtlT, Embed, Unlift (withRunInBase), abort, delimitAbort, embed')
import Control.Monad.MultiPrompt.Formal qualified as C
import Data.Data (Proxy (Proxy))
import Data.Function ((&))
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO, liftIO, withRunInIO)

type Effect = (Type -> Type) -> Type -> Type
data Frame = E Effect [Type]

-- | A effect handler.
data Handler e b where
    Handler :: (forall x. e (CtlT fs b) x -> CtlT fs b x) -> Handler ('E e fs) b

-- | Vector of handlers.
data Handlers (es :: [Frame]) b where
    Cons :: Handler e b -> Handlers es b -> Handlers (e : es) b
    Nil :: Handlers '[] b

-- | Type-level search over elements in a vector.
class Elem ff (es :: [Frame]) fs | ff es -> fs where
    getHandler :: Handlers es b -> Handler ('E ff fs) b
    updateHandler :: Handler ('E ff fs) b -> Handlers es b -> Handlers es b

instance Elem ff ('E ff fs : es) fs where
    getHandler (Cons h _) = h
    updateHandler h (Cons _ hs) = Cons h hs

instance {-# OVERLAPPABLE #-} (Elem ff es fs) => Elem ff ('E ff' fs' : es) fs where
    getHandler (Cons _ hs) = getHandler hs
    updateHandler h (Cons h' hs) = Cons h' $ updateHandler h hs

-- | Prepend to the handler vector.
(!:) :: Handler e b -> Handlers es b -> Handlers (e : es) b
(!:) = Cons

-- | An effect monad transformer built on top of a multi-prompt/control monad.
newtype EffT es fs b a
    = EffT {unEffT :: Handlers es b -> CtlT fs b a}
    deriving (Functor)

interpretAll :: Handlers es b -> EffT es fs b a -> CtlT fs b a
interpretAll = flip unEffT

runEffT :: (Functor b) => EffT '[] '[] b a -> b a
runEffT = C.runCtlT . interpretAll Nil

runPure :: EffT '[] '[] Identity a -> a
runPure = C.runPure . interpretAll Nil

liftEffT :: CtlT fs b a -> EffT es fs b a
liftEffT m = EffT $ const m

instance (Monad m) => Applicative (EffT es fs m) where
    pure x = EffT \_ -> pure x
    EffT ff <*> EffT fa = EffT \v -> ff v <*> fa v

instance (Monad m) => Monad (EffT es fs m) where
    EffT m >>= f = EffT \v -> m v >>= interpretAll v . f

instance (MonadIO m) => MonadIO (EffT es fs m) where
    liftIO m = EffT \_ -> liftIO m

instance (MonadUnliftIO m) => MonadUnliftIO (EffT es '[] m) where
    withRunInIO f = EffT \v -> withRunInIO \run -> f $ run . interpretAll v

instance (Unlift b f, Functor f) => Unlift b (EffT es '[] f) where
    withRunInBase f = EffT \v -> withRunInBase \run -> f $ run . interpretAll v

withEffToCtl :: ((forall x. EffT es fs b x -> CtlT fs b x) -> CtlT fs b a) -> EffT es fs b a
withEffToCtl f = EffT \v -> f (interpretAll v)

trans :: (Handlers es' b -> Handlers es b) -> EffT es fs b a -> EffT es' fs b a
trans f (EffT withHandlerVec) = EffT $ withHandlerVec . f

-- | A type-class for higher-order effects.
class HFunctor ff where
    hfmap :: (forall x. f x -> g x) -> ff f a -> ff g a

send :: forall ff es fs fsSend b a eq. (Elem ff es fsSend, Embed eq fs fsSend b, HFunctor ff) => ff (EffT es fsSend b) a -> EffT es fs b a
send e = EffT \v -> case getHandler @ff v of Handler h -> embed' $ h $ hfmap (interpretAll v) e

prompt :: (Monad b) => EffT es (ans : fs) b ans -> EffT es fs b ans
prompt (EffT m) = EffT \v -> C.prompt_ $ m v

interpret ::
    (HFunctor e, Monad b) =>
    (forall x. Proxy '(ans, fs) -> e (EffT es (ans : fs) b) x -> EffT es (ans : fs) b x) ->
    EffT ('E e (ans : fs) : es) (ans : fs) b ans ->
    EffT es fs b ans
interpret f m = EffT \v -> interpretAll v $ prompt $ trans (Handler (interpretAll v . f Proxy . hfmap liftEffT) !:) m

data Except e :: Effect where
    Throw :: e -> Except e f a
    Catch :: f a -> (e -> f a) -> Except e f a

instance HFunctor (Except e) where
    hfmap f = \case
        Throw e -> Throw e
        Catch m hdl -> Catch (f m) (f . hdl)

runExcept ::
    forall b e a ps es.
    (Monad b) =>
    EffT ('E (Except e) (Either e a : ps) : es) (Either e a : ps) b a ->
    EffT es ps b (Either e a)
runExcept m =
    Right <$> m & interpret \p -> \case
        Throw e -> liftEffT $ abort p $ Left e
        Catch m' hdl ->
            withEffToCtl \run ->
                delimitAbort p (run m') \case
                    Left e -> run $ hdl e
                    x -> abort p x

throw :: (Elem (Except e) es r, Embed eq fs r b) => e -> EffT es fs b a
throw = send . Throw

catch :: (Elem (Except e) es r, Embed eq fs r b) => EffT es r b a -> (e -> EffT es r b a) -> EffT es fs b a
catch m h = send $ Catch m h

test :: Either String (Either Char Int)
test = runPure . runExcept . runExcept $ do
    catch
        do
            catch (throw 'c') \(s :: Char) -> pure 0
        \(c :: String) -> undefined
