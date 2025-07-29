{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Monad.Effect.StaticPromptStack where

import Control.Monad (ap, (>=>))
import Control.Monad.Effect (Effect)
import Data.Extensible (
    ExtConst (..),
    Membership (at, inject),
    Rec (..),
    Union (..),
    mapRec,
    membership0,
    weakenMembership,
 )
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
