{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Effect.Simple where

import Control.Arrow (first)
import Control.Monad ((>=>))
import Control.Monad.Trans.Freer (FreerF (..), FreerT (FreerT), qApp, runFreerT, transFreerT)
import Data.FTCQueue (tsingleton)
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Type)
import Data.List (singleton)

type Effect = Type -> Type

type Eff es = FreerT (Union es App) Identity

newtype App f a = App {getApp :: f a}

data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

data Membership h x xs = Membership
    { inject :: forall a. h x a -> Union xs h a
    , project :: forall a. Union xs h a -> Maybe (h x a)
    }

type Member = Membership App :: Effect -> [Effect] -> Type

class x :> xs where
    membership :: Membership h x xs

instance e :> (e : es) where
    membership = Membership Here \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (e :> es) => e :> (e' : es) where
    membership = Membership (There . inject membership) \case
        Here _ -> Nothing
        There u -> project membership u

interpret ::
    (a -> Eff es b) ->
    (forall x. e x -> (x -> Eff es b) -> Eff es b) ->
    Eff (e : es) a ->
    Eff es b
interpret ret hdl (FreerT (Identity m)) =
    FreerT . Identity $ case m of
        Pure x -> runIdentity . runFreerT $ ret x
        Freer f q ->
            let k = interpret ret hdl . qApp q
             in case f of
                    Here e -> runIdentity . runFreerT $ hdl (getApp e) k
                    There u -> Freer u (tsingleton k)

interpretShallow ::
    (a -> Eff es b) ->
    (forall x. e x -> (x -> Eff (e : es) b) -> Eff es b) ->
    Eff (e : es) a ->
    Eff es b
interpretShallow ret hdl (FreerT (Identity m)) =
    FreerT . Identity $ case m of
        Pure x -> runIdentity . runFreerT $ ret x
        Freer f q ->
            let k = qApp q
             in case f of
                    Here e -> runIdentity . runFreerT $ hdl (getApp e) (k >=> raise . ret)
                    There u -> Freer u (tsingleton $ interpretShallow ret hdl . k)

pull :: Member e es -> Eff es a -> Eff (e : es) a
pull i = transFreerT \u -> case project i u of
    Just e -> Here e
    Nothing -> There u

rewrite :: Member e es -> (forall x. e x -> e x) -> Eff es a -> Eff es a
rewrite i f = transFreerT \u -> case project i u of
    Just e -> inject i $ App $ f $ getApp e
    Nothing -> u

raise :: Eff es a -> Eff (e : es) a
raise = transFreerT There

send :: Member e es -> e a -> Eff es a
send i op = FreerT $ Identity $ Freer (inject i $ App op) (tsingleton pure)

perform :: (e :> es) => e a -> Eff es a
perform op = FreerT $ Identity $ Freer (inject membership $ App op) (tsingleton pure)

performWith :: (e :> es) => e a -> (a -> Eff es b) -> Eff es b
performWith op k = FreerT $ Identity $ Freer (inject membership $ App op) (tsingleton k)

performH :: (e :> es) => e (Eff es a) -> Eff es a
performH op = FreerT $ Identity $ Freer (inject membership $ App op) (tsingleton id)

runEff :: (Monad m) => Eff '[m] a -> m a
runEff (FreerT m) = case runIdentity m of
    Pure x -> pure x
    Freer (Here (App n)) q -> n >>= runEff . qApp q
    Freer (There u) _ -> case u of {}

runPure :: Eff '[] a -> a
runPure (FreerT m) = case runIdentity m of
    Pure x -> x
    Freer u _ -> case u of {}

data Reader r :: Effect where
    Ask :: Reader r r
    Local :: Member (Reader r) es -> (r -> r) -> Eff es a -> Reader r (Eff es a)

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = interpret pure \case
    Ask -> \k -> k r
    Local i f m -> \k -> k $ runReader (f r) (pull i m)

local :: (Reader r :> es) => (r -> r) -> Eff es a -> Eff es a
local f m = performH $ Local membership f m

data Yield i o :: Effect where
    Yield :: i -> Yield i o o

data Status f i o a = Done a | Continue i (o -> f (Status f i o a))

runCoroutine :: Eff (Yield i o : es) a -> Eff es (Status (Eff es) i o a)
runCoroutine = interpret (pure . Done) \(Yield i) k -> pure $ Continue i k

data Except e :: Effect where
    Throw :: e -> Except e a
    Catch :: Member (Except e) es -> Eff es a -> (e -> Eff es a) -> Except e (Eff es a)

catch :: (Except e :> es) => Eff es a -> (e -> Eff es a) -> Eff es a
catch m hdl = performH $ Catch membership m hdl

runExcept :: Eff (Except e : es) a -> Eff es (Either e a)
runExcept = interpret (pure . Right) \case
    Throw e -> \_ -> pure $ Left e
    Catch i m hdl -> \k -> k do
        runExcept (pull i m) >>= \case
            Left e -> hdl e
            Right x -> pure x

data Writer w :: Effect where
    Tell :: w -> Writer w ()
    Listen :: Member (Writer w) es -> Eff es a -> Writer w (Eff es (w, a))
    Censor :: Member (Writer w) es -> (w -> w) -> Eff es a -> Writer w (Eff es a)

listen :: (Writer w :> es) => Eff es a -> Eff es (w, a)
listen m = performH $ Listen membership m

censor :: (Writer w :> es) => (w -> w) -> Eff es a -> Eff es a
censor f m = performH $ Censor membership f m

runWriter :: (Monoid w) => Eff (Writer w : es) a -> Eff es (w, a)
runWriter = interpret (pure . (mempty,)) \case
    Tell w -> \k -> first (w <>) <$> k ()
    Listen i m -> \k -> k $ runWriter (pull i m)
    Censor i f m -> \k -> k do
        (w, x) <- runWriter (pull i m)
        send i $ Tell $ f w
        pure x

runWriterPre :: (Monoid w) => Eff (Writer w : es) a -> Eff es (w, a)
runWriterPre = interpret (pure . (mempty,)) \case
    Tell w -> \k -> first (w <>) <$> k ()
    Listen i m -> \k -> k $ runWriter (pull i m)
    Censor i f m -> \k ->
        k $
            rewrite
                i
                \case
                    Tell w -> Tell $ f w
                    Listen i' m' -> Listen i' m'
                    Censor i' f' m' -> Censor i' f' m'
                m

data NonDet :: Effect where
    Empty :: NonDet a
    Choose :: NonDet Bool
    ObserveAll :: Member NonDet es -> Eff es a -> NonDet (Eff es [a])

runNonDet :: Eff (NonDet : es) a -> Eff es [a]
runNonDet = interpret (pure . singleton) \case
    Empty -> \_ -> pure []
    Choose -> \k -> liftA2 (++) (k False) (k True)
    ObserveAll i m -> \k -> k $ runNonDet $ pull i m

observeAll :: (NonDet :> es) => Eff es a -> Eff es [a]
observeAll m = performH $ ObserveAll membership m

choice :: (NonDet :> es) => [a] -> Eff es a
choice [] = perform Empty
choice (x : xs) =
    perform Choose >>= \case
        False -> pure x
        True -> choice xs

-- >>> testNonDet
-- [[1,2,3,0],[1,2,3,1]]

testNonDet :: [[Int]]
testNonDet = runPure $ runNonDet do
    b <- perform Choose
    observeAll do
        choice [1, 2, 3, if b then 1 else 0]

-- >>> testNSR
-- (1,1,42)

testNSR :: (Int, Int, Int)
testNSR = runPure do
    s <- runReader @Int 0 $ runCoroutine @() @() do
        (x, y) <- local @Int (+ 1) do
            x <- perform $ Ask @Int
            perform $ Yield @() @() ()
            y <- perform $ Ask @Int
            pure (x, y)

        z <- perform $ Ask @Int

        pure (x, y, z)

    case s of
        Continue () k -> do
            s' <- runReader @Int 42 $ k ()
            case s' of
                Done r -> pure r
                Continue _ _ -> error "unreachable"
        Done _ -> error "unreachable"

-- >>> testWriter
-- ("goodbye world",())

testWriter :: (String, ())
testWriter = runPure $ runWriterPre do
    censor (\s -> if s == "hello" then "goodbye" else s) do
        perform $ Tell "hello"
        perform $ Tell " world"
