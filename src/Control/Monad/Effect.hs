{-# LANGUAGE TypeData #-}

module Control.Monad.Effect where

import Data.Kind (Type)

type Effect = (Type -> Type) -> Type -> Type

data Evil :: Effect where
    Evil :: Evil f ()

data NonDet :: Effect where
    Choose :: NonDet f Bool
    Observe :: f [a] -> NonDet f [a]

data Except e :: Effect where
    Throw :: e -> Except e f a
    Try :: f a -> Except e f (Either e a)

data SomeEff :: Effect where
    SomeEff :: SomeEff f Int
