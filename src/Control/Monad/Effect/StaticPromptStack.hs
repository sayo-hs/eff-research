{-# LANGUAGE TypeData #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect.StaticPromptStack where

import Control.Monad (ap, (>=>))
import Data.Extensible
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Type)
import Data.List (singleton)

type Effect = (Type -> Type) -> Type -> Type

data Evil :: Effect where
    Evil :: Evil f ()

data NonDet :: Effect where
    Choose :: NonDet f Bool
    Observe :: f a -> NonDet f [a]

data State s :: Effect where
    Get :: State s f s
    Put :: s -> State s f ()

data Except e :: Effect where
    Throw :: e -> Except e f a
    Try :: f a -> Except e f (Either e a)

data SomeEff :: Effect where
    SomeEff :: SomeEff f Int

newtype Eff es a = Eff {unEff :: forall ps. Ctl ps es a}
    deriving (Functor)

type data Prompt = P (Type -> Type) [Prompt] [Effect] Effect [Effect]

newtype Ctl (ps :: [Prompt]) (es :: [Effect]) a = Ctl {unCtl :: Handlers ps es -> CtlF ps es a}

type Handlers ps es = Rec es (ExtConst (Handler ps)) ()

data Handler ps e where
    Handler ::
        (forall w esSend x. Membership w (P f u ue e d) -> Handlers w d -> Handlers u d -> e (Eff esSend) x -> Ctl w esSend x) ->
        Membership ps (P f u ue e d) ->
        Handlers ps d ->
        Handlers u d ->
        Handler ps e

data CtlF ps es a
    = Pure a
    | forall x. Freer (Union ps ControlPrim x) (x -> Ctl ps es a)

data ControlPrim (p :: Prompt) a where
    Control :: (forall ps es x. Membership ps (P f u ue e d) -> (a -> Ctl ps es (f x)) -> Ctl ps es (f x)) -> ControlPrim (P f u ue e d) a
    Control0 :: (forall x. (a -> Ctl (P f u ue e d : u) ue (f x)) -> Ctl (P f u ue e d : u) ue (f x)) -> ControlPrim (P f u ue e d) a

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

trans :: (Handlers ps es' -> Handlers ps es) -> Ctl ps es a -> Ctl ps es' a
trans f (Ctl m) = Ctl \hs -> case m (f hs) of
    Pure x -> Pure x
    Freer u k -> Freer u $ trans f . k

raise :: Ctl ps es a -> Ctl ps (e : es) a
raise = trans dropRec

{-
override :: Membership es e -> (forall w esSend x. e (Eff esSend) x -> Ctl w esSend x) -> Ctl ps es a -> Ctl ps es a
override i h = trans \hs -> update i (ExtConst . (\(Handler _ i' d d') -> Handler (\_ _ _ -> h) i' d d') . getExtConst $ at i hs) hs
-}

freezeEnv :: Handlers ps es -> Ctl ps es a -> Ctl ps '[] a
freezeEnv hs (Ctl m) = case m hs of
    Pure x -> pure x
    Freer u k -> Ctl \Nil -> Freer u $ freezeEnv hs . k

raisesEnv :: Ctl ps '[] a -> Ctl ps es a
raisesEnv = undefined

send :: Membership es e -> e (Eff es) a -> Eff es a
send i e = Eff $ Ctl \hs -> case at i hs of
    ExtConst (Handler h i' d d') -> unCtl (h i' d d' e) hs

sendWith :: Handlers ps es -> Membership es e -> e (Eff es') a -> Ctl ps es' a
sendWith hs ie e = case at ie hs of
    ExtConst (Handler h i' d d') -> h i' d d' e

perform :: (e :> es) => e (Eff es) a -> Eff es a
perform = send membership

control ::
    Membership ps (P f u ue e d) ->
    (forall ps' es' x. Membership ps' (P f u ue e d) -> (a -> Ctl ps' es' (f x)) -> Ctl ps' es' (f x)) ->
    Ctl ps es a
control i f = Ctl \_ -> Freer (inject i $ Control f) pure

shift ::
    Membership ps (P f u ue e d) ->
    (forall ps' es' x. Membership ps' (P f u ue e d) -> (a -> Ctl ps' es' (f x)) -> Ctl ps' es' (f x)) ->
    Ctl ps es a
shift i f = control i \i' k -> f i' $ delimit i' . k

control0 ::
    Membership ps (P f u ue e d) ->
    (forall x. (a -> Ctl (P f u ue e d : u) ue (f x)) -> Ctl (P f u ue e d : u) ue (f x)) ->
    Ctl ps es a
control0 i f = Ctl \_ -> Freer (inject i $ Control0 f) pure

weakenPrompt :: Handler ps e -> Handler (p : ps) e
weakenPrompt (Handler h i d d') = Handler h (weakenMembership i) (liftPrompt d) d'

liftPrompt :: Handlers ps es -> Handlers (p : ps) es
liftPrompt = mapRec $ ExtConst . weakenPrompt . getExtConst

interpretCtl ::
    (d < es) =>
    (forall w esSend x. Membership w (P f ps (e : es) e d) -> Handlers w d -> Handlers ps d -> e (Eff esSend) x -> Ctl w esSend x) ->
    Ctl (P f ps (e : es) e d : ps) (e : es) (f a) ->
    Ctl ps es (f a)
interpretCtl h m = Ctl \hs ->
    let hs' = ExtConst (Handler h membership0 (subset memberships $ liftPrompt hs) (subset memberships hs)) :* liftPrompt hs
     in case unCtl m hs' of
            Pure x -> Pure x
            Freer ctls k -> case ctls of
                Here (Control ctl) -> unCtl (interpretCtl h $ ctl membership0 k) hs
                Here (Control0 ctl) -> unCtl (interpretCtl h $ ctl k) hs
                There u -> Freer u $ interpretCtl h . k

interpret ::
    (d < es) =>
    (forall ps w esSend x. Membership w (P f ps (e : es) e d) -> Handlers w d -> Handlers ps d -> e (Eff esSend) x -> Ctl w esSend x) ->
    Eff (e : es) (f a) ->
    Eff es (f a)
interpret h (Eff m) = Eff $ interpretCtl h m

{-
handleShallow :: (forall ps esSend x (y :: Type). e (Eff esSend) x -> (x -> Ctl ps (e : es) (f y)) -> Ctl ps (e : es) (f y)) -> Eff (e : es) (f a) -> Eff es (f a)
handleShallow h = interpret @'[] \i Nil e -> control0 i $ h e
-}

delimit :: Membership ps (P f u ue e d) -> Ctl ps es (f a) -> Ctl ps es (f a)
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
    interpret @'[] \i _ _ -> \case
        Choose -> shift i \_ k -> do
            xs <- k False
            ys <- k True
            pure $ xs ++ ys
        Observe m -> delimit i $ unEff $ singleton <$> m

-- >>> test
-- [Identity [(False,False),(False,True),(True,False),(True,True)]]

test :: [Identity [(Bool, Bool)]]
test = runPure $ runNonDet do
    xs <- perform $ Observe do
        x <- perform Choose
        y <- perform Choose
        pure (x, y)
    pure [Identity xs]

{-
runState :: s -> Eff (State s : es) a -> Eff es a
runState s0 =
    fmap runIdentity
        . ( handleShallow \case
                Get -> \k -> k s0
                Put s -> \k -> undefined
          )
        . fmap Identity
-}

runExcept :: Eff (Except e : es) (Either e a) -> Eff es (Either e a)
runExcept = interpret @'[] \i _ _ -> \case
    Throw e -> control i \_ _ -> pure $ Left e
    Try m -> delimit i $ Right <$> unEff m

runSomeEff :: (Except String :> es) => Eff (SomeEff : es) a -> Eff es a
runSomeEff = fmap runIdentity . interpret @'[Except String] (\_ hs _ SomeEff -> sendWith hs membership $ Throw "uncaught") . fmap Identity

runSomeEff2 :: (Except String :> es) => Eff (SomeEff : es) a -> Eff es a
runSomeEff2 =
    fmap runIdentity
        . interpret @'[Except String]
            ( \i _ hs SomeEff -> control0 i \k -> do
                undefined
                sendWith (liftPrompt hs) membership $ Throw "uncaught"
            )
        . fmap Identity

catch :: (Except e :> es) => Eff es a -> (e -> Eff es a) -> Eff es a
catch m hdl =
    perform (Try m) >>= \case
        Left e -> hdl e
        Right x -> pure x

-- >>> testE
-- Right 8

testE :: Either String Int
testE = runPure $ runExcept $ runSomeEff do
    Right
        <$> catch @String
            (perform SomeEff)
            (pure . length)

data Test :: Effect where
    Test :: f a -> Test f a

runTest :: (Except String :> es) => Eff (Test : es) (Identity a) -> Eff es (Identity a)
runTest = interpret @'[Except String] \_ hs _ (Test m) -> do
    sendWith hs membership $ Throw "error"
    unEff m
    sendWith hs membership $ Throw "error"
