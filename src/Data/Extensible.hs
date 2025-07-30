module Data.Extensible where

import Data.Kind (Type)
import Data.Type.Equality ((:~:))

data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

data Rec (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    (:*) :: h x a -> Rec xs h a -> Rec (x : xs) h a
    Nil :: Rec '[] h a

infixr 9 :*

newtype ExtConst (h :: k -> Type) (x :: k) (a :: l) = ExtConst {getExtConst :: h x}

data Membership xs x = Membership
    { inject :: forall l h (a :: l). h x a -> Union xs h a
    , project :: forall l h (a :: l). Union xs h a -> Maybe (h x a)
    , at :: forall l h (a :: l). Rec xs h a -> h x a
    , update :: forall l h (a :: l). h x a -> Rec xs h a -> Rec xs h a
    }

membership0 :: Membership (x : xs) x
membership0 =
    Membership
        Here
        \case
            Here x -> Just x
            _ -> Nothing
        (\(h :* _) -> h)
        (\h (_ :* hs) -> h :* hs)

weakenMembership :: Membership xs x -> Membership (x' : xs) x
weakenMembership i =
    Membership
        (There . inject i)
        \case
            Here _ -> Nothing
            There u -> project i u
        (\(_ :* hs) -> at i hs)
        (\h (h' :* hs) -> h' :* update i h hs)

class x :> xs where
    membership :: Membership xs x

instance x :> (x : xs) where
    membership = membership0

instance {-# OVERLAPPABLE #-} (x :> xs) => x :> (x' : xs) where
    membership = weakenMembership membership

mapRec :: (forall x. h x a -> i x b) -> Rec xs h a -> Rec xs i b
mapRec f = \case
    x :* xs -> f x :* mapRec f xs
    Nil -> Nil

zipRec :: (forall x. h x a -> i x b -> j x c) -> Rec xs h a -> Rec xs i b -> Rec xs j c
zipRec f = \cases
    (x :* xs) (y :* ys) -> f x y :* zipRec f xs ys
    Nil Nil -> Nil

nil :: Union '[] h a -> r
nil = \case {}

type Memberships xs ys = Rec xs (ExtConst (Membership ys)) ()

class xs < ys where
    memberships :: Memberships xs ys

instance '[] < ys where
    memberships = Nil

instance (x :> ys, xs < ys) => (x : xs) < ys where
    memberships = ExtConst membership :* memberships

subset :: Memberships xs ys -> Rec ys h a -> Rec xs h a
subset is ys = mapRec (\(ExtConst i) -> at i ys) is

dropRec :: Rec (x : xs) h a -> Rec xs h a
dropRec (_ :* xs) = xs

infixr 9 +:
(+:) :: (h x a -> r) -> (Union xs h a -> r) -> Union (x : xs) h a -> r
f +: g = \case
    Here x -> f x
    There u -> g u

infixr 9 *:
(*:) :: (r -> h x a) -> (r -> Rec xs h a) -> r -> Rec (x : xs) h a
(f *: g) r = f r :* g r
