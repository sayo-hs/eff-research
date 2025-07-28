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

import Control.Monad (ap, (>=>))
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
    sub p = weakenSub (sub p)

weakenSub :: Sub u xs -> Sub u (x : xs)
weakenSub s =
    Sub
        { weaken = There . weaken s
        , strengthen = \case
            Here _ -> Nothing
            There u -> strengthen s u
        }

instance xs < xs where
    sub _ = Sub{weaken = id, strengthen = Just}

type Effect = Type -> Type
type Prompt = Type -> Type

data Handler ps e where
    Handler :: (forall w u' es x. e x -> Sub (p : u') w -> Ctl w es x) -> Sub (p : u) ps -> Handler ps e

data Handlers ps es where
    Cons :: Handler (p : ps) e -> Handlers ps es -> Handlers (p : ps) (e : es)
    Nil :: Handlers '[] '[]

newtype Eff es a = Eff {unEff :: forall ps. Ctl ps es a}

instance Functor (Eff es) where
    fmap f = (>>= pure . f)

instance Applicative (Eff es) where
    pure x = Eff \_ -> Pure x
    (<*>) = ap

instance Monad (Eff es) where
    Eff m >>= f = Eff \hs -> case m hs of
        Pure x -> unEff (f x) hs
        Freer u k -> Freer u (k >=> f)

type Ctl (ps :: [Prompt]) (es :: [Effect]) a = Handlers ps es -> EffCtlF ps es a

data EffCtlF ps es a
    = Pure a
    | forall x. Freer (StackUnion ps Control x) (x -> Eff es a)

data Control (f :: Prompt) (u :: [Prompt]) a where
    Control :: (forall es x. (a -> Eff es (f x)) -> Eff es (f x)) -> Control f u a

newtype Membership e es = Membership {getHandler :: forall ps. Handlers ps es -> Handler ps e}

hereMembership :: Membership e (e : es)
hereMembership = Membership (\(Cons h _) -> h)

send :: Membership e es -> e a -> Eff es a
send (Membership getHandler) e = Eff \hs -> case getHandler hs of
    Handler h i -> h e i hs

control :: Sub (p : u) ps -> (forall es' x. (a -> Eff es' (p x)) -> Eff es' (p x)) -> Ctl ps es a
control i f _ = Freer (weaken i $ Here $ Control f) pure

interpret :: (forall es' x (y :: Type). e x -> (x -> Eff es' (p y)) -> Eff es' (p y)) -> Eff (e : es) (p a) -> Eff es (p a)
interpret hdl (Eff m) =
    Eff \hs ->
        let hs' = Cons (Handler (\e i -> control i \k -> hdl e k) $ Sub id Just) hs
         in case m hs' of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unEff (ctl $ interpret hdl . k) hs
                    There u -> Freer u $ interpret hdl . k

data NonDet :: Effect where
    Choose :: NonDet Bool

runNonDet :: Eff (NonDet : es) [a] -> Eff es [a]
runNonDet = interpret \Choose k -> do
    xs <- k False
    ys <- k True
    pure $ xs ++ ys

runPure :: Eff '[] a -> a
runPure (Eff m) = case m Nil of
    Pure x -> x
    Freer u _ -> case u of {}

-- >>> test
-- [(False,False),(False,True),(True,False),(True,True)]

test :: [(Bool, Bool)]
test = runPure $ runNonDet do
    b1 <- send hereMembership Choose
    b2 <- send hereMembership Choose
    pure [(b1, b2)]
