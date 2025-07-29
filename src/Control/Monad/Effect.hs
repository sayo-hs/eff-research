{-# LANGUAGE TypeData #-}

module Control.Monad.Effect where

import Data.Kind (Type)

type Effect = (Type -> Type) -> Type -> Type

data Evil :: Effect where
    Evil :: Evil f ()
