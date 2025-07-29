{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Effect.StaticPromptStack where

import Control.Monad (ap, (>=>))
import Control.Monad.Effect (Effect, Except (..), NonDet (..), SomeEff (..))
import Data.Extensible (
    ExtConst (..),
    Membership (at, inject),
    Rec (..),
    Union (..),
    mapRec,
    membership,
    membership0,
    nil,
    project,
    weakenMembership,
    (:>),
 )
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Type)

newtype Eff es a = Eff {unEff :: forall ps. Ctl ps es a}
    deriving (Functor)

type data Prompt = P (Type -> Type) [Prompt] [Effect]

newtype Ctl (ps :: [Prompt]) (es :: [Effect]) a = Ctl {unCtl :: Handlers ps es -> CtlF ps es a}

type Handlers ps es = Rec es (ExtConst (Handler ps)) '()

data Handler ps e where
    Handler ::
        (forall w esSend x. Membership e esSend -> Membership (P f u es) w -> e (Eff esSend) x -> Ctl w esSend x) ->
        Membership (P f u es) ps ->
        Handler ps e

data CtlF ps es a
    = Pure a
    | forall x. Freer (Union ps Control x) (x -> Ctl ps es a)

data Control (f :: Prompt) a where
    Control :: (forall ps es' x. Membership (P f u es) ps -> (a -> Ctl ps es' (f x)) -> Ctl ps es' (f x)) -> Control (P f u es) a
    Control0 :: (forall x. (a -> Ctl u es (f x)) -> Ctl u es (f x)) -> Control (P f u es) a

instance Functor (Ctl ps es) where
    fmap f = (>>= pure . f)

instance Applicative (Ctl ps es) where
    pure x = Ctl \_ -> Pure x
    (<*>) = ap

instance Monad (Ctl ps es) where
    Ctl m >>= f = Ctl \hs -> case m hs of
        Pure x -> unCtl (f x) hs
        Freer u k -> Freer u (k >=> f)

instance Applicative (Eff es) where
    pure x = Eff $ pure x
    Eff ff <*> Eff fm = Eff $ ff <*> fm

instance Monad (Eff es) where
    Eff m >>= f = Eff $ m >>= \x -> unEff $ f x

freezeEnv :: Handlers ps es -> Ctl ps es a -> Ctl ps '[] a
freezeEnv hs (Ctl m) = case m hs of
    Pure x -> pure x
    Freer u k -> Ctl \Nil -> Freer u $ freezeEnv hs . k

raisesEnv :: Ctl ps '[] a -> Ctl ps es a
raisesEnv = undefined

send :: Membership e es -> e (Eff es) a -> Eff es a
send i e = Eff $ Ctl \hs -> case at i hs of
    ExtConst (Handler h i') -> unCtl (h i i' e) hs

perform :: (e :> es) => e (Eff es) a -> Eff es a
perform = send membership

control ::
    Membership (P f u ues) ps ->
    (forall ps' es' x. Membership (P f u ues) ps' -> (a -> Ctl ps' es' (f x)) -> Ctl ps' es' (f x)) ->
    Ctl ps es a
control i f = Ctl \_ -> Freer (inject i $ Control f) pure

control0 ::
    Membership (P f u es') ps ->
    (forall x. (a -> Ctl u es' (f x)) -> Ctl u es' (f x)) ->
    Ctl ps es a
control0 i f = Ctl \_ -> Freer (inject i $ Control0 f) pure

weakenPrompt :: Handler ps e -> Handler (p : ps) e
weakenPrompt (Handler h i) = Handler h (weakenMembership i)

liftPrompt :: Handlers ps es -> Handlers (p : ps) es
liftPrompt = mapRec $ ExtConst . weakenPrompt . getExtConst

interpretCtl ::
    (forall w esSend x. Membership e esSend -> Membership (P f ps es) w -> e (Eff esSend) x -> Ctl w esSend x) ->
    Ctl (P f ps es : ps) (e : es) (f a) ->
    Ctl ps es (f a)
interpretCtl h m = Ctl \hs ->
    let hs' = Cons (ExtConst $ Handler h membership0) (liftPrompt hs)
     in case unCtl m hs' of
            Pure x -> Pure x
            Freer ctls k -> case ctls of
                Here (Control ctl) -> unCtl (interpretCtl h $ ctl membership0 k) hs
                Here (Control0 ctl) -> unCtl (ctl $ interpretCtl h . k) hs
                There u -> Freer u $ interpretCtl h . k

interpret ::
    (forall w ps esSend x. Membership e esSend -> Membership (P f ps es) w -> Handlers ps es -> e (Eff esSend) x -> Ctl w esSend x) ->
    Eff (e : es) (f a) ->
    Eff es (f a)
interpret h (Eff m) = Eff $ Ctl \hs -> unCtl (interpretCtl (\ih ip -> h ih ip hs) m) hs

delimit :: Membership (P f u ues) ps -> Ctl ps es (f a) -> Ctl ps es (f a)
delimit i (Ctl m) = Ctl \hs ->
    case m hs of
        Pure x -> Pure x
        Freer ctls k -> case project i ctls of
            Just (Control ctl) -> unCtl (ctl i k) hs
            _ -> Freer ctls k

runPure :: Eff '[] a -> a
runPure (Eff (Ctl m)) = case m Nil of
    Pure x -> x
    Freer u _ -> nil u

runNonDet :: Eff (NonDet : es) [a] -> Eff es [a]
runNonDet =
    interpret \_ i _ -> \case
        Choose -> control i \i' k -> do
            xs <- delimit i' $ k True
            ys <- delimit i' $ k False
            pure $ xs ++ ys
        Observe m -> delimit i $ unEff m

-- >>> test
-- [Identity [(True,True),(True,False),(False,True),(False,False)]]

test :: [Identity [(Bool, Bool)]]
test = runPure $ runNonDet do
    xs <- perform $ Observe do
        x <- perform Choose
        y <- perform Choose
        pure [(x, y)]
    pure [Identity xs]

runExcept :: Eff (Except e : es) (Either e a) -> Eff es (Either e a)
runExcept = interpret \_ i _ -> \case
    Throw e -> control i \_ _ -> pure $ Left e
    Try m -> delimit i $ Right <$> unEff m

runSomeEff :: (Except String :> es) => Eff (SomeEff : es) a -> Eff es a
runSomeEff = fmap runIdentity . interpret (\_ i _ SomeEff -> control0 i \_ -> unEff $ perform $ Throw "uncaught") . fmap Identity

catch :: (Except e :> es) => Eff es a -> (e -> Eff es a) -> Eff es a
catch m hdl =
    perform (Try m) >>= \case
        Left e -> hdl e
        Right x -> pure x

-- >>> testE
-- Left "uncaught"

testE :: Either String Int
testE = runPure $ runExcept $ runSomeEff do
    Right
        <$> catch @String
            (perform SomeEff)
            (pure . length)
