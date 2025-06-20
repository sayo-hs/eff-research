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
newtype CtlT (ps :: [PromptFrame]) r m a = CtlT {unCtlT :: r -> m (CtlResult ps r m a)}

{-
mapEnv :: (Monad m) => (r -> r') -> CtlT ps r' m a -> CtlT ps r m a
mapEnv f (CtlT m) = CtlT \v ->
    m (f v) <&> \case
        Pure x -> Pure x
        Ctl ctls -> Ctl $ forCtls ctls \case
            Abort r -> Abort r
            Control ctl q -> Control ctl (tsingleton $ mapEnv f . qApp q)
-}

data CtlResult ps r m a
    = Pure a
    | Ctl (Ctls ps r m a)

type Ctls ps r m a = Union ps (CtlFrame ps r m a)

data CtlFrame (ps :: [PromptFrame]) r (m :: Type -> Type) (a :: Type) (p :: PromptFrame) where
    PrimOp :: PrimOp ps r m a p -> CtlFrame ps r m a p
    Under :: Union u (CtlFrame ps r m a) -> CtlFrame ps r m a (Prompt ans u)

data PrimOp (ps :: [PromptFrame]) r (m :: Type -> Type) (a :: Type) (p :: PromptFrame) where
    Control :: ((b -> CtlT u r m ans) -> CtlT u r m ans) -> FTCQueue (CtlT ps r m) b a -> PrimOp ps r m a (Prompt ans u)

mapCtls :: (forall x. PrimOp ps r m a x -> PrimOp ps' r' m' a' x) -> Union xs (CtlFrame ps r m a) -> Union xs (CtlFrame ps' r' m' a')
mapCtls f = mapUnion \case
    PrimOp op -> PrimOp $ f op
    Under u -> Under $ mapCtls f u

forCtls :: Union xs (CtlFrame ps r m a) -> (forall x. PrimOp ps r m a x -> PrimOp ps' r' m' a' x) -> Union xs (CtlFrame ps' r' m' a')
forCtls u f = mapCtls f u

{-
under :: (Member p ps, Monad m) => p :~: Prompt ans u -> (r -> r') -> r' -> CtlT u r' m a -> CtlT ps r m a
under p@Refl f v (CtlT m) =
    CtlT \_ ->
        m v <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ inject p $ Under $ forCtls ctls \case
                Abort ans -> Abort ans
                Control ctl q -> Control ctl (tsingleton $ resumeUnder p f $ qApp q)

resumeUnder :: (Member p ps, Monad m) => p :~: Prompt ans r' u -> (r -> r') -> (b -> CtlT u r' m a) -> (b -> CtlT ps r m a)
resumeUnder p@Refl f k x =
    CtlT \v -> unCtlT (under p f (f v) (k x)) v

instance (Applicative f) => Functor (CtlResult frames r f) where
    fmap f = \case
        Pure x -> Pure $ f x
        Ctl ctls -> Ctl $ forCtls ctls \case
            Abort ans -> Abort ans
            Control ctl q -> Control ctl $ q |> (CtlT . const . pure . Pure . f)

instance (Applicative f) => Functor (CtlT fs r f) where
    fmap f (CtlT m) = CtlT $ fmap (fmap f) . m

instance (Monad m) => Applicative (CtlT fs r m) where
    pure = CtlT . const . pure . Pure
    (<*>) = ap

instance (Monad m) => Monad (CtlT fs r m) where
    CtlT m >>= f =
        CtlT \v ->
            m v >>= \case
                Pure x -> unCtlT (f x) v
                Ctl ctls -> pure $ Ctl $ forCtls ctls \case
                    Abort a -> Abort a
                    Control ctl q -> Control ctl $ q |> f

instance (MonadIO m) => MonadIO (CtlT fs r m) where
    liftIO m = CtlT $ const $ liftIO $ Pure <$> m

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] r m) where
    withRunInIO f = CtlT \v -> withRunInIO \run -> Pure <$> f (run . runCtlT v)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f) => Unlift b (ReaderT r f) where
    withRunInBase f = ReaderT \v -> withRunInBase \run -> f $ run . flip runReaderT v

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] r f) where
    withRunInBase f = CtlT \v -> Pure <$> withRunInBase \run -> f (run . runCtlT v)

prompt :: (Monad m) => (forall p. p :~: Prompt ans r ps -> CtlT (p : ps) r m ans) -> CtlT ps r m ans
prompt f =
    CtlT \v ->
        unCtlT (f Refl) v >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case ctls of
                Here (PrimOp (Control ctl q)) -> unCtlT (ctl \x -> prompt $ \Refl -> qApp q x) v
                Here (PrimOp (Abort ans)) -> pure $ Pure ans
                Here (Under u) -> promptUnder u
                There u -> promptUnder u
  where
    promptUnder :: (Monad m) => Union ps (CtlFrame (Prompt ans r ps : ps) r m ans) -> m (CtlResult ps r m ans)
    promptUnder u =
        pure $ Ctl $ forCtls u \case
            Control ctl q -> Control ctl $ tsingleton \x -> prompt \Refl -> qApp q x
            Abort r -> Abort r

control :: forall p ans r' u ps r m a. (Member p ps, Applicative m) => p :~: Prompt ans r' u -> ((a -> CtlT u r' m ans) -> CtlT u r' m ans) -> CtlT ps r m a
control p@Refl f = CtlT . const . pure . Ctl . inject p $ PrimOp $ Control f (tsingleton $ CtlT . const . pure . Pure)

abort :: forall p ans r' u ps r f a. (Member p ps, Applicative f) => p :~: Prompt ans r' u -> ans -> CtlT ps r f a
abort p@Refl = CtlT . const . pure . Ctl . inject p . PrimOp . Abort

qApp :: (Monad m) => FTCQueue (CtlT ps r m) a b -> a -> CtlT ps r m b
qApp q x = CtlT \v -> case tviewl q of
    TOne k -> unCtlT (k x) v
    k :| t ->
        unCtlT (k x) v >>= \case
            Pure y -> unCtlT (qApp t y) v
            Ctl ctls -> pure $ Ctl $ forCtls ctls \case
                Control ctl q' -> Control ctl $ q' >< t
                Abort r -> Abort r

liftCtlT :: (Functor f) => f a -> CtlT fs r f a
liftCtlT a = CtlT $ const $ Pure <$> a

runCtlT :: (Functor f) => r -> CtlT '[] r f a -> f a
runCtlT v (CtlT m) =
    m v <&> \case
        Pure x -> x
        Ctl ctls -> case ctls of {}

runPure :: r -> CtlT '[] r Identity a -> a
runPure v (CtlT m) = case runIdentity $ m v of
    Pure x -> x
    Ctl ctls -> case ctls of {}

data Status a b ps v m r = Done r | Continue a (b -> CtlT ps v m (Status a b ps v m r))

yield :: (Member p ps, Monad m) => p :~: Prompt (Status a b u v' m r) v' u -> a -> CtlT ps v m b
yield p x = control p \k -> pure $ Continue x k

runCoroutine ::
    (Monad m) =>
    (forall p. p :~: Prompt (Status a b ps v m r) v ps -> CtlT (p : ps) v m r) ->
    CtlT ps v m (Status a b ps v m r)
runCoroutine f = prompt \p -> Done <$> f p

test :: IO ()
test = runCtlT () do
    s <- runCoroutine \c -> do
        liftIO $ putStrLn "a"
        i <- yield c 0
        liftIO $ print i
    case s of
        Continue (x :: Int) resume -> do
            _ <- resume $ x + 1
            pure ()
        Done () -> pure ()
-}
