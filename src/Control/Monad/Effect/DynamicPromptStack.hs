-- SPDX-License-Identifier: MPL-2.0
{-# LANGUAGE TypeData #-}

module Control.Monad.Effect.DynamicPromptStack where

import Control.Monad (ap, join, (>=>))
import Control.Monad.Effect
import Data.Extensible (
    ExtConst (..),
    Membership (inject, project),
    Rec (..),
    Union (..),
    at,
    mapRec,
    membership,
    membership0,
    nil,
    update,
    weakenMembership,
    (:>),
 )
import Data.Function ((&))
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Kind (Type)

type data Prompt = P (Type -> Type) [Effect]

data Handler ps e where
    Handler ::
        (forall w esSend x. Membership e esSend -> Membership (P f u) w -> e (Eff esSend) x -> Ctl w esSend x) ->
        Membership (P f u) ps ->
        Handler ps e

type Handlers ps es = Rec es (ExtConst (Handler ps)) '()

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
raise = trans \(Cons _ hs) -> hs

raiseUnder :: Eff (e : es) a -> Eff (e : e' : es) a
raiseUnder = trans \(Cons h (Cons _ hs)) -> Cons h hs

swap :: Handlers ps (e1 : e2 : es) -> Handlers ps (e2 : e1 : es)
swap (Cons h1 (Cons h2 es)) = Cons h2 (Cons h1 es)

newtype Ctl (ps :: [Prompt]) (es :: [Effect]) a = Ctl {unCtl :: Handlers ps es -> CtlF ps es a}

data CtlF ps es a
    = Pure a
    | forall x. Freer (Union ps Control x) (x -> Eff es a)

data Control (f :: Prompt) a where
    Control :: (forall es x. (a -> Eff es (f x)) -> Eff es (f x)) -> Control (P f u) a
    Control0 :: (forall x. (a -> Eff u (f x)) -> Eff u (f x)) -> Control (P f u) a

weakenPrompt :: Handler ps e -> Handler (p : ps) e
weakenPrompt (Handler h i) = Handler h (weakenMembership i)

liftPrompt :: forall p ps es. Handlers ps es -> Handlers (p : ps) es
liftPrompt = mapRec $ ExtConst . weakenPrompt . getExtConst

send :: Membership e es -> e (Eff es) a -> Eff es a
send i e = Eff $ Ctl \hs -> case at i hs of
    ExtConst (Handler h i') -> unCtl (h i i' e) hs

perform :: (e :> es) => e (Eff es) a -> Eff es a
perform = send membership

control :: Membership (P f u) ps -> (forall es x. (a -> Eff es (f x)) -> Eff es (f x)) -> Ctl ps esSend a
control i f = Ctl \_ -> Freer (inject i $ Control f) pure

control0 :: Membership (P f u) ps -> (forall x. (a -> Eff u (f x)) -> Eff u (f x)) -> Ctl ps es a
control0 i f = Ctl \_ -> Freer (inject i $ Control0 f) pure

pureCtl :: a -> Ctl ps es a
pureCtl x = Ctl \_ -> Pure x

bindCtl :: Ctl ps es a -> (a -> Eff es b) -> Ctl ps es b
bindCtl (Ctl m) f = Ctl \hs -> case m hs of
    Pure x -> unCtl (unEff $ f x) hs
    Freer u k -> Freer u (k >=> f)

fmapCtl :: (a -> b) -> Ctl ps es a -> Ctl ps es b
fmapCtl f m = m `bindCtl` (pure . f)

delimit :: Membership (P f u) ps -> Ctl ps es (f a) -> Ctl ps es (f a)
delimit i (Ctl m) = Ctl \hs ->
    case m hs of
        Pure x -> Pure x
        Freer ctls k -> case project i ctls of
            Just (Control ctl) -> unCtl (unEff $ ctl k) hs
            _ -> Freer ctls k

interpretShallow ::
    (forall w esSend x. Membership e esSend -> Membership (P f (e : es)) w -> e (Eff esSend) x -> Ctl w esSend x) ->
    Eff (e : es) (f a) ->
    Eff es (f a)
interpretShallow h (Eff m) =
    Eff $ Ctl \hs ->
        let hs' = Cons (ExtConst $ Handler h membership0) (liftPrompt hs)
         in case unCtl m hs' of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unCtl (unEff $ interpretShallow h $ ctl k) hs
                    Here (Control0 ctl) -> unCtl (unEff $ interpretShallow h $ ctl k) hs
                    There u -> Freer u $ interpretShallow h . k

interpret ::
    (forall w esSend x. Membership e esSend -> Membership (P f es) w -> e (Eff esSend) x -> Ctl w esSend x) ->
    Eff (e : es) (f a) ->
    Eff es (f a)
interpret h (Eff m) =
    Eff $ Ctl \hs ->
        let hs' = Cons (ExtConst $ Handler h membership0) (liftPrompt hs)
         in case unCtl m hs' of
                Pure x -> Pure x
                Freer ctls k -> case ctls of
                    Here (Control ctl) -> unCtl (unEff $ ctl $ interpret h . k) hs
                    Here (Control0 ctl) -> unCtl (unEff $ ctl $ interpret h . k) hs
                    There u -> Freer u $ interpret h . k

runPure :: Eff '[] a -> a
runPure (Eff m) = case unCtl m Nil of
    Pure x -> x
    Freer u _ -> nil u

runExcept :: Eff (Except e : es) a -> Eff es (Either e a)
runExcept m =
    Right <$> m & interpret \_ i -> \case
        Throw e -> control i \_ -> pure $ Left e
        Try n -> delimit i $ unEff $ Right <$> n

catch :: (Except e :> es) => Eff es a -> (e -> Eff es a) -> Eff es a
catch m hdl =
    perform (Try m) >>= \case
        Left e -> hdl e
        Right x -> pure x

-- >>> testE
-- Left "uncaught"

testE :: Either String Int
testE = runPure $ runExcept $ runSomeEff do
    catch @String
        (perform SomeEff)
        (pure . length)

runSomeEff :: (Except String :> es) => Eff (SomeEff : es) a -> Eff es a
runSomeEff = fmap runIdentity . interpret (\_ i SomeEff -> control0 i \_ -> perform $ Throw "uncaught") . fmap Identity

runNonDet :: Eff (NonDet : es) [a] -> Eff es [a]
runNonDet = interpret \_ i -> \case
    Choose ->
        control i \k -> do
            xs <- k False
            ys <- k True
            pure $ xs ++ ys
    Observe m -> delimit i $ unEff m

-- >>> test
-- [Identity [(False,False),(True,False)],Identity [(False,False),(True,True)],Identity [(False,True),(True,False)],Identity [(False,True),(True,True)]]

test :: [Identity [(Bool, Bool)]]
test = runPure $ runNonDet do
    xs <- perform $ Observe do
        b1 <- perform Choose
        b2 <- perform Choose
        pure [(b1, b2)]
    pure [Identity xs]

data Reader r :: Effect where
    Ask :: Reader r f r

-- Local :: (r -> r) -> f a -> Reader r f a

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r =
    fmap runIdentity
        . interpret
            ( \i _ -> \case
                Ask -> pureCtl r
                -- Local f m -> unEff $ runReader (f r) (pull i m)
            )
        . fmap Identity

{-
runReader2 :: r -> Eff (Reader r : es) a -> Eff es a
runReader2 r m = do
    runReader @Int 10 do
        fmap runIdentity
            . interpret
                ( \i ip -> \case
                    Ask -> pureCtl r
                    Local f m' -> do
                        (control ip \k -> undefined)
                            `bindCtl` (\_ -> runReader (f r) (pull i m'))
                )
            . fmap Identity
            $ raiseUnder m
-}

runEvil :: Eff (Evil : es) a -> Eff es (Eff es a)
runEvil = interpret (\_ i Evil -> control0 i \k -> pure $ join $ k ()) . fmap pure

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
