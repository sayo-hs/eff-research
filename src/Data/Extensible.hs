module Data.Extensible where

import Data.Kind (Type)

data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

data Rec (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Cons :: h x a -> Rec xs h a -> Rec (x : xs) h a
    Nil :: Rec '[] h a

newtype ExtConst (h :: k -> Type) (x :: k) (a :: l) = ExtConst {getExtConst :: h x}

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

class x :> xs where
    membership :: Membership x xs

instance x :> (x : xs) where
    membership = membership0

instance {-# OVERLAPPABLE #-} (x :> xs) => x :> (x' : xs) where
    membership = weakenMembership membership

mapRec :: (forall x. h x a -> i x b) -> Rec xs h a -> Rec xs i b
mapRec f = \case
    Cons x xs -> Cons (f x) (mapRec f xs)
    Nil -> Nil

nil :: Union '[] h a -> r
nil = \case {}
