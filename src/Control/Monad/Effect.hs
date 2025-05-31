{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad.MultiPrompt.Formal (CtlT, Member, Unlift (withRunInBase))
import Control.Monad.MultiPrompt.Formal qualified as C
import Data.Kind (Type)
import UnliftIO (MonadIO, MonadUnliftIO, liftIO, withRunInIO)

type Effect' = (Type -> Type) -> Type -> Type
data Effect = E ((Type -> Type) -> Type -> Type) Resumption

{- | Types of resumption.

@NonTail ans r@: where @ans@ is the answer type and @r@ is the underlying prompt frame list.
-}
data Resumption = Tail | NonTail Type [Type]

-- | A effect handler.
data Handler e f b where
    TailResumptive :: (forall x. e f x -> CtlT fs b x) -> Handler ('E e Tail) f b
    NonTailResumptive :: (forall fs x. (Member ans r fs) => e f x -> CtlT fs b x) -> Handler ('E e (NonTail ans r)) f b

-- A contravariant map on handlers for higher-order effects.
hcmapHandler :: (HFunctor e) => (forall x. f x -> g x) -> Handler ('E e r) g b -> Handler ('E e r) f b
hcmapHandler phi = \case
    TailResumptive h -> TailResumptive $ h . hfmap phi
    NonTailResumptive h -> NonTailResumptive $ h . hfmap phi

-- | Vector of handlers.
data HandlerVec (es :: [Effect]) f b where
    Cons :: Handler e f b -> Handlers es f b -> HandlerVec (e : es) f b
    Nil :: HandlerVec '[] f b

-- | Type-level search over elements in a vector.
class (HFunctor ff) => Elem ff (es :: [Effect]) res | ff es -> res where
    getHandler :: Handlers es f b -> Handler ('E ff res) f b
    updateHandler :: Handler ('E ff res) f b -> Handlers es f b -> Handlers es f b

instance (HFunctor ff) => Elem ff ('E ff res : es) res where
    getHandler (Handlers (Cons h _) koi) = hcmapHandler koi h
    updateHandler h (Handlers (Cons _ hs) koi) = Handlers (Cons h (hcmapHandlers koi hs)) id

instance {-# OVERLAPPABLE #-} (Elem ff es res, HFunctor ff') => Elem ff ('E ff' res' : es) res where
    getHandler (Handlers (Cons _ hs) koi) = hcmapHandler koi $ getHandler hs
    updateHandler h (Handlers (Cons h' hs) koi) = Handlers (Cons (hcmapHandler koi h') (updateHandler h $ hcmapHandlers koi hs)) id

-- | Equip the handler vector with a free HFunctor structure.
data Handlers es f b = forall g. Handlers
    { handlers :: HandlerVec es g b
    , koi :: forall x. f x -> g x
    }

hcmapHandlers :: (forall x. f x -> g x) -> Handlers es g b -> Handlers es f b
hcmapHandlers phi (Handlers f koi) = Handlers f (koi . phi)

-- | A type-class for higher-order effects.
class HFunctor ff where
    hfmap :: (forall x. f x -> g x) -> ff f a -> ff g a

-- | Prepend to the handler vector.
(!:) :: Handler e f b -> Handlers es f b -> Handlers (e : es) f b
h !: hs = Handlers (Cons h hs) id

-- | An effect monad transformer built on top of a multi-prompt/control monad.
newtype EffT es fs b a
    = EffT {unEffT :: Handlers es (EffT es fs b) b -> CtlT fs b a}
    deriving (Functor)

runEffT :: Handlers es (EffT es fs b) b -> EffT es fs b a -> CtlT fs b a
runEffT = flip unEffT

instance (Monad m) => Applicative (EffT es fs m) where
    pure x = EffT \_ -> pure x
    EffT ff <*> EffT fa = EffT \v -> ff v <*> fa v

instance (Monad m) => Monad (EffT es fs m) where
    EffT m >>= f = EffT \v -> m v >>= runEffT v . f

instance (MonadIO m) => MonadIO (EffT es fs m) where
    liftIO m = EffT \_ -> liftIO m

instance (MonadUnliftIO m) => MonadUnliftIO (EffT es '[] m) where
    withRunInIO f = EffT \v -> withRunInIO \run -> f $ run . runEffT v

instance (Unlift b f, Functor f) => Unlift b (EffT es '[] f) where
    withRunInBase f = EffT \v -> withRunInBase \run -> f $ run . runEffT v

withEffToCtl :: ((forall x. EffT es fs b x -> CtlT fs b x) -> CtlT fs b a) -> EffT es fs b a
withEffToCtl f = EffT \v -> f (runEffT v)

trans :: (Handlers es' (EffT es' fs b) b -> Handlers es (EffT es' fs b) b) -> EffT es fs b a -> EffT es' fs b a
trans f (EffT withHandlerVec) = EffT $ withHandlerVec . hcmapHandlers (trans f) . f

-- | Interpret a tail-resumptive effect.
interpret ::
    (forall x. e (EffT es fs b) x -> EffT es fs b x) ->
    EffT ('E e 'Tail : es) fs b a ->
    EffT es fs b a
interpret f m = EffT \v -> runEffT v $ trans (TailResumptive (runEffT v . f) !:) m

data Except e :: Effect' where
    Throw :: e -> Except e f a
    Catch :: f a -> (e -> f a) -> Except e f a
instance HFunctor (Except e) where
    hfmap f = \case
        Throw e -> Throw e
        Catch m hdl -> Catch (f m) (f . hdl)

{-
runExcept :: (Monad b) => EffT ('E (Except e) 'Tail : es) (Either e a ': fs) b a -> EffT es fs b (Either e a)
runExcept m = withEffToCtl \run -> prompt \p -> undefined
-}

prompt :: (Monad b) => EffT es (ans : fs) b ans -> EffT es fs b ans
prompt (EffT m) = EffT \v -> C.prompt \p -> m $ undefined v

{-
interpretNT ::
    (Monad b) =>
    (forall x. e (EffT ('E e ('NonTail ans r) : es) fs b) x -> EffT es fs b x) ->
    EffT ('E e ('NonTail ans fs) : es) (ans : fs) b ans ->
    EffT es fs b ans
interpretNT f (EffT m) = EffT \v -> prompt \p -> undefined
-}

-- | A send that works with both kinds of resumption.
class (Elem ff es res) => Send res ff es fs where
    send :: ff (EffT es fs b) a -> EffT es fs b a

instance (Elem ff es 'Tail) => Send 'Tail ff es fs where
    send e = EffT \v -> case getHandler @ff v of TailResumptive h -> undefined $ h e

{-
instance (Elem ff es ('NonTail ans r), Member ans r fs) => Send ('NonTail ans r) ff es fs where
    send e = EffT \v -> case getHandler @ff v of NonTailResumptive h -> h e
-}
