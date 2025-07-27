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

import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.Coerce (Coercible, coerce)
import Data.Function (fix)
import Data.Functor.Const (Const (Const), getConst)
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))

data StackUnion (xs :: [k]) (h :: k -> [k] -> l -> Type) (a :: l) where
    Here :: h x xs a -> StackUnion (x : xs) h a
    There :: StackUnion xs h a -> StackUnion (x : xs) h a

mapStackUnion :: (forall x r. h x r a -> i x r a) -> StackUnion xs h a -> StackUnion xs i a
mapStackUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapStackUnion f xs

forStackUnion :: StackUnion xs h a -> (forall x r. h x r a -> i x r a) -> StackUnion xs i a
forStackUnion u f = mapStackUnion f u

infix 4 <
class u < xs where
    sub :: Proxy u -> Sub u xs

data Sub (u :: [k]) (xs :: [k])
    = Sub
    { weaken :: forall l h (a :: l). StackUnion u h a -> StackUnion xs h a
    , strengthen :: forall l h (a :: l). StackUnion xs h a -> Maybe (StackUnion u h a)
    }

instance {-# INCOHERENT #-} (u < xs) => u < x : xs where
    sub p =
        Sub
            { weaken = There . weaken (sub p)
            , strengthen = \case
                Here _ -> Nothing
                There u -> strengthen (sub p) u
            }

instance xs < xs where
    sub _ = Sub{weaken = id, strengthen = Just}

type Effect = Type -> Type
type Prompt = Type -> Type

data Handler p e where
    Handler :: (forall w u es x. e x -> Sub (p : u) w -> Ctl w es x) -> Handler p e

data Handlers ps es where
    Cons :: Handler p e -> Handlers ps es -> Handlers (p : ps) (e : es)
    Nil :: Handlers ps '[]

newtype Eff ps es a = Eff {unEff :: Ctl ps es a}

instance Functor (Eff ps es)
instance Applicative (Eff ps es)
instance Monad (Eff ps es)

type Ctl (ps :: [Prompt]) (es :: [Effect]) a = Handlers ps es -> EffCtlF ps es a

data EffCtlF ps es a
    = Pure a
    | forall x. Freer (StackUnion ps Control x) (x -> Eff ps es a)

data Control (f :: Prompt) (u :: [Prompt]) a where
    Control :: (forall w u' es x. Sub (f : u') w -> (a -> Eff w es (f x)) -> Eff w es (f x)) -> Control f u a

data Membership e es p ps = forall u. Membership {getHandler :: Handlers ps es -> Handler p e, getPrompt :: Sub (p : u) ps}

send :: Membership e es p ps -> e a -> Eff ps es a
send (Membership getHandler p) e = Eff \hs -> let Handler h = getHandler hs in h e p hs

control :: Sub (p : u) ps -> (forall w u' es' x. Sub (p : u') w -> (a -> Eff w es' (p x)) -> Eff w es' (p x)) -> Ctl ps es a
control i f _ = Freer (weaken i $ Here $ Control f) pure

interpret :: (forall w es' x y. e x -> (x -> Eff w es' (p y)) -> Eff w es' (p y)) -> Eff (p : ps) (e : es) (p a) -> Eff ps es (p a)
interpret hdl (Eff f) =
    let h = Handler \e i -> control i \_ k -> hdl e k
     in Eff \hs ->
            case f (Cons h hs) of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unEff (interpret hdl $ ctl (Sub id Just) k) hs
                    There u -> Freer u $ interpret hdl . k
