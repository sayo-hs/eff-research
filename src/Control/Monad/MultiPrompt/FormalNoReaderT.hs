{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# HLINT ignore "Use fmap" #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff).
-}
module Control.Monad.MultiPrompt.FormalNoReaderT where

import Control.Monad (ap)
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.FTCQueue (FTCQueue (..), ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import UnliftIO (MonadIO, MonadUnliftIO (withRunInIO), liftIO)

import Control.Monad.MultiPrompt.Formal hiding (Control, Ctl, CtlFrame, CtlResult, CtlT, Ctls, PrimOp, Pure, Under, forCtls, mapCtls, unCtlT)
import Control.Monad.MultiPrompt.Formal qualified as R
import Data.Function (fix, (&))

newtype CtlT (ps :: [PromptFrame]) m a = CtlT {unCtlT :: m (CtlResult ps m a)}

data CtlResult ps m a
    = Pure a
    | Ctl (Ctls ps m a)

type Ctls ps m a = Union ps (CtlFrame ps m a)

data CtlFrame (ps :: [PromptFrame]) (m :: Type -> Type) (a :: Type) (p :: PromptFrame) where
    PrimOp :: PrimOp ps m a p -> CtlFrame ps m a p
    Under :: Union u (CtlFrame ps m a) -> CtlFrame ps m a (Prompt ans u)

data PrimOp (ps :: [PromptFrame]) (m :: Type -> Type) (a :: Type) (p :: PromptFrame) where
    Control :: ((b -> CtlT u m ans) -> CtlT u m ans) -> FTCQueue (CtlT ps m) b a -> PrimOp ps m a (Prompt ans u)

toReaderT :: (Monad m) => CtlT ps (ReaderT r m) a -> R.CtlT ps r m a
toReaderT (CtlT (ReaderT m)) = R.CtlT \v ->
    m v <&> \case
        Pure x -> R.Pure x
        Ctl ctls -> R.Ctl $ goCtls ctls
  where
    goCtls :: (Monad m) => Union xs (CtlFrame ps (ReaderT r m) a) -> Union xs (R.CtlFrame ps r m a)
    goCtls = mapUnion \case
        PrimOp (Control ctl q) -> R.PrimOp $ R.Control (toReaderT . ctl . (fromReaderT .)) (hoistFQ toReaderT q)
        Under u -> R.Under $ goCtls u

fromReaderT :: (Monad m) => R.CtlT ps r m a -> CtlT ps (ReaderT r m) a
fromReaderT (R.CtlT m) = CtlT $ ReaderT \v ->
    m v <&> \case
        R.Pure x -> Pure x
        R.Ctl ctls -> Ctl $ goCtls ctls
  where
    goCtls :: (Monad m) => Union xs (R.CtlFrame ps r m a) -> Union xs (CtlFrame ps (ReaderT r m) a)
    goCtls = mapUnion \case
        R.PrimOp (R.Control ctl q) -> PrimOp $ Control (fromReaderT . ctl . (toReaderT .)) (hoistFQ fromReaderT q)
        R.Under u -> Under $ goCtls u

hoistFQ :: (forall x. f x -> g x) -> FTCQueue f a b -> FTCQueue g a b
hoistFQ phi = \case
    Leaf f -> Leaf $ phi . f
    Node l r -> Node (hoistFQ phi l) (hoistFQ phi r)
