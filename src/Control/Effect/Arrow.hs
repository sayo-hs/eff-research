{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Effect.Arrow where

import Control.Monad.Trans.Freer (FreerF (..), FreerT (FreerT), qApp, runFreerT, transFreerT)
import Data.FTCQueue (tsingleton)
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Type)

data family In e :: Type -> Type
type family Out e a :: Type

data Op e a where
    Op :: In e a -> Op e (Out e a)

type Eff es = FreerT (Union es Op) Identity

data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

data Membership h x xs = Membership
    { inject :: forall a. h x a -> Union xs h a
    , project :: forall a. Union xs h a -> Maybe (h x a)
    }

type Member = Membership Op

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

suspendWith :: In e a -> (Out e a -> Eff es a) -> Eff (e : es) a
suspendWith op k = FreerT $ Identity $ Freer (Here $ Op op) (tsingleton $ transFreerT There . k)

{-
suspend :: (e :> es) => In e a -> (Out e a -> Eff es a) -> Eff es a
suspend op k = FreerT $ Identity $ Freer (inject membership $ Op op) (tsingleton k)
-}

interpret ::
    (a -> Eff es b) ->
    (forall x. In e x -> (Out e x -> Eff es b) -> Eff es b) ->
    Eff (e : es) a ->
    Eff es b
interpret ret hdl (FreerT (Identity m)) =
    FreerT . Identity $ case m of
        Pure x -> runIdentity . runFreerT $ ret x
        Freer f q ->
            let k = interpret ret hdl . qApp q
             in case f of
                    Here (Op e) -> runIdentity . runFreerT $ hdl e k
                    There u -> Freer u (tsingleton k)

data Reader r

data instance In (Reader r) a where
    Ask :: In (Reader r) r
    Local :: Member (Reader r) es -> (r -> r) -> Eff es a -> In (Reader r) (Eff es a)

type instance Out (Reader r) a = a

pull :: Member e es -> Eff es a -> Eff (e : es) a
pull i = transFreerT \u -> case project i u of
    Just e -> Here e
    Nothing -> There u

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = interpret pure \case
    Ask -> \k -> k r
    Local i f m -> \k -> k $ runReader (f r) (pull i m)

runPure :: Eff '[] a -> a
runPure (FreerT m) = case runIdentity m of
    Pure x -> x
    Freer u _ -> case u of {}

send :: (e :> es) => In e a -> Eff es (Out e a)
send op = FreerT $ Identity $ Freer (inject membership $ Op op) (tsingleton pure)

sendWith :: (e :> es) => In e a -> (Out e a -> Eff es b) -> Eff es b
sendWith op k = FreerT $ Identity $ Freer (inject membership $ Op op) (tsingleton k)

local :: (Reader r :> es) => (r -> r) -> Eff es a -> Eff es a
local f m = sendWith (Local membership f m) id

-- >>> test
-- 1

test :: Int
test = runPure $ runReader @Int 0 do
    local @Int (+ 1) do
        send Ask
