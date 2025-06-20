{-# LANGUAGE AllowAmbiguousTypes #-}
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
module Control.Monad.MultiPrompt.Formal where

import Control.Monad (ap)
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.FTCQueue (FTCQueue (..), ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import UnliftIO (MonadIO, MonadUnliftIO (withRunInIO), liftIO)

-- | An type-safe open union.
data Union (xs :: [k]) (h :: k -> Type) where
    Here :: h x -> Union (x : xs) h
    There :: Union xs h -> Union (x : xs) h

mapUnion :: (forall x. h x -> i x) -> Union xs h -> Union xs i
mapUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapUnion f xs

forUnion :: Union xs h -> (forall x. h x -> i x) -> Union xs i
forUnion u f = mapUnion f u

class Member x xs where
    inj :: h x -> Union xs h
    prj :: Union xs h -> Maybe (h x)

inject :: (Member x xs) => x :~: y -> h x -> Union xs h
inject _ = inj

project :: (Member x xs) => x :~: y -> Union xs h -> Maybe (h x)
project _ = prj

instance Member x (x : xs) where
    inj = Here
    prj = \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (Member x xs) => Member x (x' : xs) where
    inj = There . inj
    prj = \case
        Here _ -> Nothing
        There xs -> prj xs

type data PromptFrame = Prompt Type [PromptFrame]

{- | A type-safe multi-prompt/control monad transformer with reader environment.

    @ps@: A list of the current prompt stack frames.

    @r@: The reader environment.

    @m@: The base monad.
-}
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

mapCtls :: (forall x. PrimOp ps m a x -> PrimOp ps' m' a' x) -> Union xs (CtlFrame ps m a) -> Union xs (CtlFrame ps' m' a')
mapCtls f = mapUnion \case
    PrimOp op -> PrimOp $ f op
    Under u -> Under $ mapCtls f u

forCtls :: Union xs (CtlFrame ps m a) -> (forall x. PrimOp ps m a x -> PrimOp ps' m' a' x) -> Union xs (CtlFrame ps' m' a')
forCtls u f = mapCtls f u

instance (Applicative f) => Functor (CtlResult frames f) where
    fmap f = \case
        Pure x -> Pure $ f x
        Ctl ctls -> Ctl $ forCtls ctls \case
            Control ctl q -> Control ctl $ q |> (CtlT . pure . Pure . f)

instance (Applicative f) => Functor (CtlT fs f) where
    fmap f (CtlT m) = CtlT $ fmap (fmap f) m

instance (Monad m) => Applicative (CtlT fs m) where
    pure = CtlT . pure . Pure
    (<*>) = ap

instance (Monad m) => Monad (CtlT fs m) where
    CtlT m >>= f =
        CtlT $
            m >>= \case
                Pure x -> unCtlT (f x)
                Ctl ctls -> pure $ Ctl $ forCtls ctls \case
                    Control ctl q -> Control ctl $ q |> f

instance (MonadIO m) => MonadIO (CtlT fs m) where
    liftIO m = CtlT $ liftIO $ Pure <$> m

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] m) where
    withRunInIO f = CtlT $ withRunInIO \run -> Pure <$> f (run . runCtlT)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f) => Unlift b (ReaderT r f) where
    withRunInBase f = ReaderT \v -> withRunInBase \run -> f $ run . flip runReaderT v

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] f) where
    withRunInBase f = CtlT $ Pure <$> withRunInBase \run -> f (run . runCtlT)

prompt :: (Monad m) => (forall p. p :~: Prompt ans ps -> CtlT (p : ps) m ans) -> CtlT ps m ans
prompt f =
    CtlT $
        unCtlT (f Refl) >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case ctls of
                Here (PrimOp (Control ctl q)) -> unCtlT (ctl \x -> prompt $ \Refl -> qApp q x)
                Here (Under u) -> promptUnder u
                There u -> promptUnder u
  where
    promptUnder :: (Monad m) => Union ps (CtlFrame (Prompt ans ps : ps) m ans) -> m (CtlResult ps m ans)
    promptUnder u =
        pure $ Ctl $ forCtls u \case
            Control ctl q -> Control ctl $ tsingleton \x -> prompt \Refl -> qApp q x

control :: forall p ans u ps m a. (Member p ps, Applicative m) => p :~: Prompt ans u -> ((a -> CtlT u m ans) -> CtlT u m ans) -> CtlT ps m a
control p@Refl f = CtlT . pure . Ctl . inject p $ PrimOp $ Control f (tsingleton $ CtlT . pure . Pure)

abort :: forall p ans u ps m a. (Member p ps, Monad m) => p :~: Prompt ans u -> ans -> CtlT ps m a
abort p ans = control p \_ -> pure ans

under :: (Member p ps, Monad m) => p :~: Prompt ans u -> CtlT u m a -> CtlT ps m a
under p@Refl (CtlT m) =
    CtlT $
        m <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ inject p $ Under $ forCtls ctls \case
                Control ctl q -> Control ctl (tsingleton $ under p . qApp q)

qApp :: (Monad m) => FTCQueue (CtlT ps m) a b -> a -> CtlT ps m b
qApp q x = CtlT $ case tviewl q of
    TOne k -> unCtlT (k x)
    k :| t ->
        unCtlT (k x) >>= \case
            Pure y -> unCtlT (qApp t y)
            Ctl ctls -> pure $ Ctl $ forCtls ctls \case
                Control ctl q' -> Control ctl $ q' >< t

liftCtlT :: (Functor f) => f a -> CtlT fs f a
liftCtlT a = CtlT $ Pure <$> a

runCtlT :: (Functor f) => CtlT '[] f a -> f a
runCtlT (CtlT m) =
    m <&> \case
        Pure x -> x
        Ctl ctls -> case ctls of {}

runPure :: CtlT '[] Identity a -> a
runPure (CtlT m) = case runIdentity m of
    Pure x -> x
    Ctl ctls -> case ctls of {}

data Status a b ps m r = Done r | Continue a (b -> CtlT ps m (Status a b ps m r))

yield :: (Member p ps, Monad m) => p :~: Prompt (Status a b u m r) u -> a -> CtlT ps m b
yield p x = control p \k -> pure $ Continue x k

runCoroutine ::
    (Monad m) =>
    (forall p. p :~: Prompt (Status a b ps m r) ps -> CtlT (p : ps) m r) ->
    CtlT ps m (Status a b ps m r)
runCoroutine f = prompt \p -> Done <$> f p

test :: IO ()
test = runCtlT do
    s <- runCoroutine \c -> do
        liftIO $ putStrLn "a"
        i <- yield c 0
        liftIO $ print i
    case s of
        Continue (x :: Int) resume -> do
            _ <- resume $ x + 1
            pure ()
        Done () -> pure ()
