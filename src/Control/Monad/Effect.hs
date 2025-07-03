{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

module Control.Monad.Effect where

import Control.Monad (join)
import Control.Monad.MultiPrompt.Formal (
    CtlT (..),
    FreerT (FreerT),
    PromptFrame (..),
    Sub,
    cmapCtlT,
    runCtlT,
    runFreerT,
    under,
 )
import Control.Monad.MultiPrompt.Formal qualified as C
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))

type Effect = Type -> Type

infixr 6 :+
infixr 6 :/

type data Frames = Effect :+ Frames | Type :/ Frames | Nil

type data Frame = E Effect | P Type

type family ConsFrame e = r | r -> e where
    ConsFrame (E e) = (:+) e
    ConsFrame (P ans) = (:/) ans

type family Prompts m es where
    Prompts m (_ :+ es) = Prompts m es
    Prompts m (ans :/ es) = Prompt ans (Handlers m es) : Prompts m (DropToPromptBase es)
    Prompts _ Nil = '[]

type family Effects es where
    Effects (e :+ es) = e : Effects es
    Effects (_ :/ es) = Effects es
    Effects Nil = '[]

type family FrameList es where
    FrameList (e :+ es) = E e : FrameList es
    FrameList (ans :/ es) = P ans : FrameList es
    FrameList Nil = '[]

-- | A effect handler.
data Handler (m :: Type -> Type) (e :: Effect) (u :: Frames)
    = Handler
    { handler :: forall x. e x -> EffCtlT (Prompts m u) u m x
    , envOnHandler :: Handlers m u
    }

-- | Vector of handlers.
data Handlers (m :: Type -> Type) (es :: Frames) where
    ConsHandler :: Handler m e (DropToPromptBase es) -> Handlers m es -> Handlers m (e :+ es)
    ConsPrompt :: Handlers m es -> Handlers m (ans :/ es)
    Nil :: Handlers m Nil

-- | An effect monad built on top of a multi-prompt/control monad.
newtype EffT es m a = EffT {unEffT :: CtlT (Prompts m (DropToPromptBase es)) (Handlers m es) m a}
    deriving (Functor, Applicative, Monad)

newtype EffCtlT ps es m a = EffCtlT {unEffCtlT :: CtlT ps (Handlers m es) m a}
    deriving (Functor, Applicative, Monad)

(!:) :: Handler m e (DropToPromptBase es) -> Handlers m es -> Handlers m (ConsFrame (E e) es)
(!:) = ConsHandler

class IsFrame e where
    dropHandler :: (Monad m) => Handlers m (ConsFrame e es) -> Handlers m es

instance IsFrame (E e) where
    dropHandler (ConsHandler _ hs) = hs

instance IsFrame (P ans) where
    dropHandler (ConsPrompt hs) = hs

type family a == b where
    a == a = 'True
    _ == _ = 'False

-- | Type-level search over elements in a vector.
class (Monad m) => Elem e (es :: Frames) m u | e es -> u where
    membership :: Membership e es m u

data Membership e es m u = Membership
    { getHandler :: Handlers m es -> Handler m e u
    , promptEvidence :: Sub (Prompts m u) (Prompts m (DropToPromptBase es))
    }

instance (u ~ DropToPromptBase es, Monad m) => Elem e (e :+ es) m u where
    membership =
        Membership
            { getHandler = \(ConsHandler h _) -> h
            , promptEvidence = C.sub
            }

instance {-# OVERLAPPABLE #-} (Elem e es m u) => Elem e (e' :+ es) m u where
    membership =
        let ms = membership @e @es @m @u
         in Membership
                { getHandler = \(ConsHandler _ hs) -> getHandler membership hs
                , promptEvidence = promptEvidence ms
                }

instance (Elem e es m u) => Elem e (ans :/ es) m u where
    membership =
        Membership
            { getHandler = \(ConsPrompt hs) -> getHandler membership hs
            , promptEvidence = C.Sub $ C.There . C.embed (promptEvidence $ membership @e @es @m @u)
            }

sendCtl ::
    forall e ps es m u a.
    (Monad m) =>
    Sub (Prompts m u) ps ->
    Membership e es m u ->
    e a ->
    EffCtlT ps es m a
sendCtl sub i e =
    EffCtlT $ CtlT $ FreerT $ ReaderT \r@hs ->
        let Handler h r' = getHandler i hs
         in (`runReaderT` r)
                . runFreerT
                . unCtlT
                . under sub (envOnHandler . getHandler i) r'
                . unEffCtlT
                $ h e

send :: forall e es m u a. (Monad m) => Membership e es m u -> e a -> EffT es m a
send i e = EffT . unEffCtlT $ sendCtl (promptEvidence i) i e

type family DropToPromptBase es where
    DropToPromptBase (_ :+ es) = DropToPromptBase es
    DropToPromptBase (ans :/ es) = ans :/ es
    DropToPromptBase Nil = Nil

class PromptBase m es where
    promptBaseEquality :: Prompts m es :~: Prompts m (DropToPromptBase es)
    dropHandlersToPromptBase :: (Monad m) => Handlers m es -> Handlers m (DropToPromptBase es)
    extendPromptBase :: (Monad m) => Handlers m es -> Handlers m (DropToPromptBase es) -> Handlers m es

instance (PromptBase m es) => PromptBase m (e :+ es) where
    promptBaseEquality = case promptBaseEquality @m @es of
        Refl -> Refl

    dropHandlersToPromptBase = dropHandlersToPromptBase . dropHandler

    extendPromptBase (ConsHandler h hs) hs' = ConsHandler h $ extendPromptBase hs hs'

instance PromptBase m (ans :/ es) where
    promptBaseEquality = Refl
    dropHandlersToPromptBase = id
    extendPromptBase _ = id

instance PromptBase m Nil where
    promptBaseEquality = Refl
    dropHandlersToPromptBase = id
    extendPromptBase _ = id

interpret ::
    (PromptBase m es, Monad m) =>
    (forall x. e x -> EffT es m x) ->
    EffT (e :+ es) m a ->
    EffT es m a
interpret f (EffT m) =
    EffT $ cmapCtlT (\r -> Handler (EffCtlT . cmapCtlT (extendPromptBase r) . unEffT . f) (dropHandlersToPromptBase r) !: r) m

prompt :: (Monad m) => EffT (a :/ es) m a -> EffT es m a
prompt (EffT m) = EffT $ C.prompt ConsPrompt $ const m

interpretBy ::
    forall e a b es m.
    (Monad m) =>
    (a -> EffT es m b) ->
    (forall x. e x -> (x -> EffT es m b) -> EffT es m b) ->
    EffT (e :+ b :/ es) m a ->
    EffT es m b
interpretBy ret hdl m =
    prompt $ interpret (\e -> control C.membership \k -> hdl e k) (m >>= raiseEP . ret)

raise :: (Monad m) => EffT es m a -> EffT (e :+ es) m a
raise = EffT . cmapCtlT dropHandler . unEffT

raisePrompt :: (Monad m) => EffT es m a -> EffT (a' :/ es) m a
raisePrompt = EffT . cmapCtlT dropHandler . C.raise . unEffT

raiseEP :: (Monad m) => EffT es m a -> EffT (e :+ a' :/ es) m a
raiseEP = EffT . cmapCtlT (dropHandler . dropHandler) . C.raise . unEffT

control ::
    forall ans u es m a.
    (Monad m) =>
    C.Membership
        (Prompts m (DropToPromptBase u))
        (Prompts m (DropToPromptBase es))
        (Prompt ans (Handlers m u)) ->
    ((a -> EffT u m ans) -> EffT u m ans) ->
    EffT es m a
control i f = EffT $ C.control i \k -> unEffT $ f $ EffT . k

runPure :: EffT Nil Identity a -> a
runPure = C.runPure Nil . unEffT

runEffT :: (Functor f) => EffT Nil f a -> f a
runEffT = runCtlT Nil . unEffT

data Throw e :: Effect where
    Throw :: e -> Throw e a

runExc :: (Monad m) => EffT (Throw e :+ Either e a :/ es) m a -> EffT es m (Either e a)
runExc = interpretBy (pure . Right) (\(Throw e) _ -> pure $ Left e)

perform :: (Elem e es m u) => e a -> EffT es m a
perform = send membership

-- >>> test
-- Left 3

test :: Either Int ()
test = runPure . runExc $ perform $ Throw @Int 3

data Reader r :: Effect where
    Ask :: Reader r r

runReader1 :: (Monad m, PromptBase m es) => EffT (Reader Int :+ es) m a -> EffT es m a
runReader1 = interpret \Ask -> pure 1

runReader2 :: (Monad m, PromptBase m es) => EffT (Reader Int :+ es) m a -> EffT es m a
runReader2 = interpret \Ask -> pure 2

data Evil :: Effect where
    Evil :: Evil ()

runEvil :: (Monad m) => EffT (Evil :+ EffT es m a :/ es) m a -> EffT es m (EffT es m a)
runEvil = interpretBy (pure . pure) \Evil k -> pure $ join $ k ()

-- >>> evilTest
-- 2

evilTest :: Int
evilTest = runPure do
    m <- runReader1 $ runEvil do
        _ <- perform $ Ask @Int
        perform Evil
        perform $ Ask @Int
    runReader2 m
