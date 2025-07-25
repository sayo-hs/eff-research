{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad (join)
import Control.Monad.MultiPrompt.Formal (
    Control (..),
    CtlT (..),
    PromptFrame (..),
    StackUnion (..),
    Sub,
    cmapCtlT,
    control,
    control0,
    idSub,
    prompt,
    runCtlT,
    sub,
    under,
    weakenSub,
 )
import Control.Monad.MultiPrompt.Formal qualified as C
import Control.Monad.Trans.Freer
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.Coerce (Coercible, coerce)
import Data.Function (fix, (&))
import Data.Functor.Const (Const (Const), getConst)
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))

type Effect = Type -> Type

data Handler m ps (e :: Effect)
    = forall f r u. Handler (forall x. e x -> CtlT (Prompt f r : u) r m x) (Sub (Prompt f r : u) ps) r

data Handlers m ps es where
    Cons :: Handler m ps e -> Handlers m ps es -> Handlers m ps (e : es)
    Nil :: Handlers m ps '[]

weakenSubHandlers :: Handlers m ps es -> Handlers m (p : ps) es
weakenSubHandlers = \case
    Cons (Handler h s r) hs -> Cons (Handler h (weakenSub s) r) (weakenSubHandlers hs)
    Nil -> Nil

newtype EffT es m a = EffT {unEffT :: forall ps. CtlT ps (Handlers m ps es) m a}

deriving instance (Applicative m) => Functor (EffT es m)
instance (Monad m) => Applicative (EffT es m)
instance (Monad m) => Monad (EffT es m)

data Elem e es = Elem
    { extract :: forall m ps. Handlers m ps es -> Handler m ps e
    , update :: forall m ps. Handler m ps e -> Handlers m ps es -> Handlers m ps es
    }

withEnv :: (forall ps. Handlers m ps es -> CtlT ps (Handlers m ps es) m a) -> EffT es m a
withEnv f =
    EffT $ CtlT $ FreerT $ ReaderT \r -> runReaderT (runFreerT . unCtlT $ f r) r

send :: (Monad m) => Elem e es -> e a -> EffT es m a
send i e = withEnv \hs ->
    case extract i hs of
        Handler h s r -> under s undefined r $ h e

interpret ::
    (Monad m) =>
    (forall ps x. e x -> CtlT (Prompt f (Handlers m ps es) : ps) (Handlers m ps es) m x) ->
    EffT (e : es) m (f a) ->
    EffT es m (f a)
interpret hdl m =
    withEnv \hs -> prompt (Cons (Handler hdl idSub hs) . weakenSubHandlers) $ unEffT m

data Status a b es m c = Done c | Continue a (b -> EffT es m (Status a b es m c))

data Yield a b :: Effect where
    Yield :: a -> Yield a b b

runCoroutine :: (Monad m) => EffT (Yield a b : es) m c -> EffT es m (Status a b es m c)
runCoroutine m =
    interpret
        (\(Yield a) -> control0 idSub \k -> undefined)
        $ Done <$> m
