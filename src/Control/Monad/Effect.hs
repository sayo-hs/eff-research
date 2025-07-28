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

import Control.Monad (ap, join, (>=>))
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Kind (Type)

data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

data Rec (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Cons :: h x a -> Rec xs h a -> Rec (x : xs) h a
    Nil :: Rec '[] h a

data Membership x xs = Membership
    { inject :: forall l h (a :: l). h x a -> Union xs h a
    , project :: forall l h (a :: l). Union xs h a -> Maybe (h x a)
    , at :: forall l h (a :: l). Rec xs h a -> h x a
    , update :: forall l h (a :: l). h x a -> Rec xs h a -> Rec xs h a
    }

membership0 :: Membership x (x : xs)
membership0 =
    Membership
        Here
        \case
            Here x -> Just x
            _ -> Nothing
        (\(Cons h _) -> h)
        (\h (Cons _ hs) -> Cons h hs)

weakenMembership :: Membership x xs -> Membership x (x' : xs)
weakenMembership i =
    Membership
        (There . inject i)
        \case
            Here _ -> Nothing
            There u -> project i u
        (\(Cons _ hs) -> at i hs)
        (\h (Cons h' hs) -> Cons h' $ update i h hs)

class Member x xs where
    membership :: Membership x xs

instance Member x (x : xs) where
    membership = membership0

instance {-# OVERLAPPABLE #-} (Member x xs) => Member x (x' : xs) where
    membership = weakenMembership membership

type Effect = Type -> Type
type data Prompt = P (Type -> Type) [Effect]

data Handler ps e where
    Handler :: (forall w es x. e x -> Membership p w -> Ctl w es x) -> Membership p ps -> Handler ps e

data Handlers ps es where
    ConsHandler :: Handler ps e -> Handlers ps es -> Handlers ps (e : es)
    ConsPrompt :: Handlers ps es -> Handlers (p : ps) es
    NilHandler :: Handlers '[] '[]

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
    | forall x. Freer (Union ps Control x) (x -> Eff es a)

data Control (f :: Prompt) a where
    Control :: (forall x. (a -> Eff u (f x)) -> Eff u (f x)) -> Control (P f u) a

newtype HandlerMembership e es
    = HandlerMembership
    { atHandler :: forall ps. Handlers ps es -> Handler ps e
    }

handlerMembership0 :: HandlerMembership e (e : es)
handlerMembership0 = HandlerMembership \case
    ConsHandler h _ -> h
    ConsPrompt hs -> weakenPrompt $ atHandler handlerMembership0 hs

weakenHandlerMembership :: HandlerMembership e es -> HandlerMembership e (e' : es)
weakenHandlerMembership i = HandlerMembership \case
    ConsHandler _ hs -> atHandler i hs
    ConsPrompt hs -> weakenPrompt $ atHandler (weakenHandlerMembership i) hs

weakenPrompt :: Handler ps e -> Handler (p : ps) e
weakenPrompt (Handler h i) = Handler h (weakenMembership i)

class e :> es where
    handlerMembership :: HandlerMembership e es

instance e :> (e : es) where
    handlerMembership = handlerMembership0

instance {-# OVERLAPPABLE #-} (e :> es) => e :> (e' : es) where
    handlerMembership = weakenHandlerMembership handlerMembership

send :: HandlerMembership e es -> e a -> Eff es a
send i e = Eff \hs -> case atHandler i hs of
    Handler h i' -> h e i' hs

perform :: (e :> es) => e a -> Eff es a
perform = send handlerMembership

control :: Membership (P f u) ps -> (forall x. (a -> Eff u (f x)) -> Eff u (f x)) -> Ctl ps es a
control i f _ = Freer (inject i $ Control f) pure

interpret :: (forall x (y :: Type). e x -> (x -> Eff es (f y)) -> Eff es (f y)) -> Eff (e : es) (f a) -> Eff es (f a)
interpret hdl (Eff m) =
    Eff \hs ->
        let hs' = ConsHandler (Handler (\e i -> control i \k -> hdl e k) membership0) (ConsPrompt hs)
         in case m hs' of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unEff (ctl $ interpret hdl . k) hs
                    There u -> Freer u $ interpret hdl . k

runPure :: Eff '[] a -> a
runPure (Eff m) = case m NilHandler of
    Pure x -> x
    Freer u _ -> case u of {}

data NonDet :: Effect where
    Choose :: NonDet Bool

runNonDet :: Eff (NonDet : es) [a] -> Eff es [a]
runNonDet = interpret \Choose k -> do
    xs <- k False
    ys <- k True
    pure $ xs ++ ys

-- >>> test
-- [(False,False),(False,True),(True,False),(True,True)]

test :: [(Bool, Bool)]
test = runPure $ runNonDet do
    b1 <- send handlerMembership0 Choose
    b2 <- send handlerMembership0 Choose
    pure [(b1, b2)]

data Reader r :: Effect where
    Ask :: Reader r r

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = fmap runIdentity . interpret (\Ask k -> k r) . fmap Identity

data Evil :: Effect where
    Evil :: Evil ()

runEvil :: Eff (Evil : es) a -> Eff es (Eff es a)
runEvil = interpret (\Evil k -> pure $ join $ k ()) . fmap pure

-- >>> testNSR
-- (1,2)

testNSR :: (Int, Int)
testNSR = runPure do
    let prog = do
            x :: Int <- perform Ask
            perform Evil
            y :: Int <- perform Ask
            pure (x, y)

    k <- runReader @Int 1 $ runEvil prog

    runReader @Int 2 k
