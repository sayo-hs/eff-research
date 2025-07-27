{-# LANGUAGE RoleAnnotations #-}

module Data.Unique.Tag (Tag (tagID), newTag) where

import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Type.Equality (TestEquality (testEquality), (:~:) (Refl))
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

globalCounter :: IORef Integer
globalCounter = unsafePerformIO $ newIORef 0
{-# NOINLINE globalCounter #-}

genUnique :: () -> Integer
genUnique () = unsafePerformIO do
    atomicModifyIORef' globalCounter \x -> (x + 1, x)

newtype Tag a = Tag {tagID :: Integer} deriving (Eq, Ord, Show)

instance TestEquality Tag where
    testEquality (Tag m) (Tag n)
        | m == n = Just (unsafeCoerce Refl)
        | otherwise = Nothing

newTag :: () -> Tag a
newTag = Tag . genUnique
