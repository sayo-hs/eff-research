module Control.Monad.MultiPrompt.Formal2 where

import Data.Kind (Type)
import Data.Unique.Tag (Tag)

data Union (h :: k -> l -> Type) (a :: l)
    = forall x. Union (Tag x) (h x a)
