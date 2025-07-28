{-# LANGUAGE TypeData #-}

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
    Handler ::
        (forall w es' x. Membership (P f es) w -> e x -> Ctl w es' x) ->
        Membership (P f es) ps ->
        Handler ps e

data Handlers ps es where
    ConsHandler :: Handler ps e -> Handlers ps es -> Handlers ps (e : es)
    NilHandler :: Handlers '[] '[]
    ConsPrompt :: Handlers ps '[] -> Handlers (p : ps) '[]

newtype Eff es a = Eff {unEff :: forall ps. Ctl ps es a}

instance Functor (Eff es) where
    fmap f = (>>= pure . f)

instance Applicative (Eff es) where
    pure x = Eff $ Ctl \_ -> Pure x
    (<*>) = ap

instance Monad (Eff es) where
    Eff m >>= f = Eff $ Ctl \hs -> case unCtl m hs of
        Pure x -> unCtl (unEff (f x)) hs
        Freer u k -> Freer u (k >=> f)

trans :: (forall ps. Handlers ps es' -> Handlers ps es) -> Eff es a -> Eff es' a
trans f (Eff m) =
    Eff $ Ctl \hs ->
        case unCtl m (f hs) of
            Pure x -> Pure x
            Freer u k -> Freer u $ trans f . k

transCtl :: (forall ps'. Handlers ps' es' -> Handlers ps' es) -> Ctl ps es a -> Ctl ps es' a
transCtl f (Ctl m) =
    Ctl \hs -> case m (f hs) of
        Pure x -> Pure x
        Freer u k -> Freer u $ trans f . k

raise :: Eff es a -> Eff (e : es) a
raise = trans \(ConsHandler _ hs) -> hs

swap :: Handlers ps (e1 : e2 : es) -> Handlers ps (e2 : e1 : es)
swap (ConsHandler h1 (ConsHandler h2 es)) = ConsHandler h2 (ConsHandler h1 es)

newtype Ctl (ps :: [Prompt]) (es :: [Effect]) a = Ctl {unCtl :: Handlers ps es -> EffCtlF ps es a}

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

weakenHandlerMembership :: HandlerMembership e es -> HandlerMembership e (e' : es)
weakenHandlerMembership i = HandlerMembership \case
    ConsHandler _ hs -> atHandler i hs

weakenPrompt :: Handler ps e -> Handler (p : ps) e
weakenPrompt (Handler h i) = Handler h (weakenMembership i)

liftPrompt :: forall p ps es. Handlers ps es -> Handlers (p : ps) es
liftPrompt = \case
    ConsHandler h hs -> ConsHandler (weakenPrompt h) (liftPrompt hs)
    NilHandler -> ConsPrompt NilHandler
    ConsPrompt hs -> ConsPrompt $ ConsPrompt hs

class e :> es where
    handlerMembership :: HandlerMembership e es

instance e :> (e : es) where
    handlerMembership = handlerMembership0

instance {-# OVERLAPPABLE #-} (e :> es) => e :> (e' : es) where
    handlerMembership = weakenHandlerMembership handlerMembership

send :: HandlerMembership e es -> e a -> Eff es a
send i e = Eff $ Ctl \hs -> case atHandler i hs of
    Handler h i' -> unCtl (h i' e) hs

perform :: (e :> es) => e a -> Eff es a
perform = send handlerMembership

control :: Membership (P f u) ps -> (forall x. (a -> Eff u (f x)) -> Eff u (f x)) -> Ctl ps es a
control i f = Ctl \_ -> Freer (inject i $ Control f) pure

pureCtl :: a -> Ctl ps es a
pureCtl x = Ctl \_ -> Pure x

bindCtl :: Ctl ps es a -> (a -> Eff es b) -> Ctl ps es b
bindCtl (Ctl m) f = Ctl \hs -> case m hs of
    Pure x -> unCtl (unEff $ f x) hs
    Freer u k -> Freer u (k >=> f)

fmapCtl :: (a -> b) -> Ctl ps es a -> Ctl ps es b
fmapCtl f m = m `bindCtl` (pure . f)

delimit :: Membership (P f u) ps -> Ctl ps u (f a) -> Ctl ps u (f a)
delimit i (Ctl m) = Ctl \hs ->
    case m hs of
        Pure x -> Pure x
        Freer ctls k -> case project i ctls of
            Just (Control ctl) -> unCtl (unEff $ ctl k) hs
            Nothing -> Freer ctls k

interpretShallow ::
    (forall w esSend x. Membership (P f (e : es)) w -> e x -> Ctl w esSend x) ->
    Eff (e : es) (f a) ->
    Eff es (f a)
interpretShallow h (Eff m) =
    Eff $ Ctl \hs ->
        let hs' = ConsHandler (Handler h membership0) (liftPrompt hs)
         in case unCtl m hs' of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unCtl (unEff $ interpretShallow h $ ctl k) hs
                    There u -> Freer u $ interpretShallow h . k

interpret ::
    (forall w esSend x. Membership (P f es) w -> e x -> Ctl w esSend x) ->
    Eff (e : es) (f a) ->
    Eff es (f a)
interpret h (Eff m) =
    Eff $ Ctl \hs ->
        let hs' = ConsHandler (Handler h membership0) (liftPrompt hs)
         in case unCtl m hs' of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unCtl (unEff $ ctl $ interpret h . k) hs
                    There u -> Freer u $ interpret h . k

runPure :: Eff '[] a -> a
runPure (Eff m) = case unCtl m NilHandler of
    Pure x -> x
    Freer u _ -> case u of {}

data NonDet :: Effect where
    Choose :: NonDet Bool
    Dummy :: NonDet [Int]

runNonDet :: Eff (NonDet : es) [a] -> Eff es [a]
runNonDet = interpret \i -> \case
    Choose ->
        control i \k -> do
            xs <- k False
            ys <- k True
            pure $ xs ++ ys
    Dummy -> transCtl undefined $ delimit i undefined

-- >>> test
-- [(False,False),(False,True),(True,False),(True,True)]

test :: [(Bool, Bool)]
test = runPure $ runNonDet do
    b1 <- perform Choose
    b2 <- perform Choose
    pure [(b1, b2)]

data Reader r :: Effect where
    Ask :: Reader r r

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = fmap runIdentity . interpret (\_ Ask -> pureCtl r) . fmap Identity

data Evil :: Effect where
    Evil :: Evil ()

runEvil :: Eff (Evil : es) a -> Eff es (Eff es a)
runEvil = interpret (\i Evil -> control i \k -> pure $ join $ k ()) . fmap pure

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
