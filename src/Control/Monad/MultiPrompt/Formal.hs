-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff).
-}
module Control.Monad.MultiPrompt.Formal where

import Control.Monad (ap, liftM)
import Data.FTCQueue (FTCQueue (..), ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))

data Union (xs :: [k]) (h :: k -> Type) where
    Here :: h x -> Union (x ': xs) h
    There :: Union xs h -> Union (x ': xs) h

mapUnion :: (forall x. h x -> i x) -> Union xs h -> Union xs i
mapUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapUnion f xs

forUnion :: Union xs h -> (forall x. h x -> i x) -> Union xs i
forUnion u f = mapUnion f u

class Member x xs where
    inj :: h x -> Union xs h
    prj :: Union xs h -> Maybe (h x)

instance Member x (x ': xs) where
    inj = Here
    prj = \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (Member x xs) => Member x (x' ': xs) where
    inj = There . inj
    prj = \case
        Here _ -> Nothing
        There xs -> prj xs

data Ctl fs a
    = Pure a
    | Ctl (Ctls fs a)

type Ctls fs a = Union fs (CtlFrame fs a)

data Frame = Frame [Frame] Type

data CtlFrame (fs :: [Frame]) (a :: Type) (f :: Frame) where
    CtlFrame :: ((b -> Ctl fs' r) -> Ctl fs' r) -> FTCQueue (Ctl fs) b a -> CtlFrame fs a ('Frame fs' r)
    AbortFrame :: r -> CtlFrame fs a ('Frame fs' r)

hoistCtlFrame :: (forall x. Ctl fs x -> Ctl fs' x) -> CtlFrame fs a f -> CtlFrame fs' a f
hoistCtlFrame phi = \case
    CtlFrame ctl q -> CtlFrame ctl $ hoistFQ phi q
    AbortFrame r -> AbortFrame r

hoistFQ :: (forall x. m x -> n x) -> FTCQueue m a b -> FTCQueue n a b
hoistFQ phi = \case
    Leaf f -> Leaf $ phi . f
    Node l r -> Node (hoistFQ phi l) (hoistFQ phi r)

composeFrame :: (a -> Ctl fs b) -> CtlFrame fs a f -> CtlFrame fs b f
composeFrame f = \case
    CtlFrame ctl k -> CtlFrame ctl $ k |> f
    AbortFrame r -> AbortFrame r

composeFrames :: (a -> Ctl fs b) -> Ctls fs a -> Ctls fs b
composeFrames f = mapUnion (composeFrame f)

instance Functor (Ctl fs) where
    fmap = liftM

instance Applicative (Ctl fs) where
    pure = Pure
    (<*>) = ap

instance Monad (Ctl fs) where
    m >>= f = case m of
        Pure x -> f x
        Ctl ctls -> Ctl $ composeFrames f ctls

runCtl :: Ctl '[] r -> r
runCtl = \case
    Pure x -> x
    Ctl ctls -> case ctls of {}

prompt_ :: Ctl ('Frame fs r ': fs) r -> Ctl fs r
prompt_ = \case
    Pure x -> pure x
    Ctl ctls -> case ctls of
        Here (CtlFrame ctl q) -> ctl $ prompt_ . qApp q
        Here (AbortFrame r) -> pure r
        There ctls' -> Ctl $ forUnion ctls' \case
            (CtlFrame ctl q) -> CtlFrame ctl (tsingleton $ prompt_ . qApp q)
            AbortFrame r -> AbortFrame r

prompt :: (Proxy ('Frame fs r) -> Ctl ('Frame fs r ': fs) r) -> Ctl fs r
prompt f = prompt_ $ f Proxy

delimitAbort ::
    forall fs a fs' r.
    (Member ('Frame fs' r) fs) =>
    Proxy ('Frame fs' r) ->
    Ctl fs a ->
    (r -> Ctl fs a) ->
    Ctl fs a
delimitAbort Proxy m k = case m of
    Pure x -> pure x
    Ctl ctls -> case prj @('Frame fs' r) ctls of
        Just (AbortFrame r) -> k r
        _ -> Ctl ctls

control :: forall fs a fs' r. (Member ('Frame fs' r) fs) => Proxy ('Frame fs' r) -> ((a -> Ctl fs' r) -> Ctl fs' r) -> Ctl fs a
control Proxy f = Ctl $ inj $ CtlFrame f (tsingleton pure)

abort :: forall fs a fs' r. (Member ('Frame fs' r) fs) => Proxy ('Frame fs' r) -> r -> Ctl fs a
abort Proxy r = Ctl $ inj @('Frame fs' r) $ AbortFrame r

embed :: (Member ('Frame fs' r) fs) => Proxy ('Frame fs' r) -> Ctl fs' a -> Ctl fs a
embed p m = control p (m >>=)

qApp :: FTCQueue (Ctl fs) a b -> a -> Ctl fs b
qApp q x = case tviewl q of
    TOne k -> k x
    k :| t -> case k x of
        Pure y -> qApp t y
        Ctl ctls -> Ctl $ forUnion ctls \case
            CtlFrame ctl q' -> CtlFrame ctl $ q' >< t
            AbortFrame r -> AbortFrame r

mapCtl :: (Ctls fs a -> Ctls fs' a) -> Ctl fs a -> Ctl fs' a
mapCtl f = \case
    Pure x -> Pure x
    Ctl ctls -> Ctl $ f ctls

raise :: Ctl fs a -> Ctl (f ': fs) a
raise = mapCtl $ There . mapUnion (hoistCtlFrame raise)

try :: (Proxy ('Frame fs (Either e a)) -> Ctl ('Frame fs (Either e a) ': fs) a) -> Ctl fs (Either e a)
try m = prompt_ $ Right <$> m Proxy

throw :: (Member ('Frame fs' (Either e r)) fs) => Proxy ('Frame fs' (Either e r)) -> e -> Ctl fs a
throw p e = abort p $ Left e

catch :: (Member ('Frame fs' (Either e r)) fs) => Proxy ('Frame fs' (Either e r)) -> Ctl fs a -> (e -> Ctl fs a) -> Ctl fs a
catch p m hdl =
    delimitAbort p m \case
        Left e -> hdl e
        x -> abort p x

test :: Either String Int
test = runCtl do
    try \p -> do
        catch p (throw p "BOOM") \s -> pure $ length s

-- >>> test
-- Right 4
