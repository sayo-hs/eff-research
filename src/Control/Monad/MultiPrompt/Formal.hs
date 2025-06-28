{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
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
import Data.Proxy (Proxy (Proxy))
import UnliftIO (MonadIO, MonadUnliftIO (withRunInIO), liftIO)

{- | An type-safe open union (extensible sum) that does not support permutation of the list, and
    behaves in a stack-like manner.

    The implementation itself is possible with the usual open-union, but in that case the type-level
    list of prompt stack frames becomes recursive and its size explodes exponentially, so this
    approach prevents that.
-}
data StackUnion (xs :: [k]) (h :: k -> [k] -> Type) where
    Here :: h x xs -> StackUnion (x : xs) h
    There :: StackUnion xs h -> StackUnion (x : xs) h

mapStackUnion :: (forall x r. h x r -> i x r) -> StackUnion xs h -> StackUnion xs i
mapStackUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapStackUnion f xs

forStackUnion :: StackUnion xs h -> (forall x r. h x r -> i x r) -> StackUnion xs i
forStackUnion u f = mapStackUnion f u

class Member r xs x | r xs -> x where
    inj :: h x r -> StackUnion xs h
    prj :: StackUnion xs h -> Maybe (h x r)

inject :: (Member r xs x) => Proxy r -> h x r -> StackUnion xs h
inject _ = inj

project :: (Member r xs x) => Proxy r -> StackUnion xs h -> Maybe (h x r)
project _ = prj

instance Member xs (x : xs) x where
    inj = Here
    prj = \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (Member r xs x) => Member r (x' : xs) x where
    inj = There . inj
    prj = \case
        Here _ -> Nothing
        There xs -> prj xs

type data PromptFrame = Prompt Type Type

{- | A type-safe multi-prompt/control monad transformer with reader environment.

    @ps@: A list of the current prompt stack frames.

    @r@: The reader environment.

    @m@: The base monad.
-}
newtype CtlT (ps :: [PromptFrame]) r m a = CtlT {unCtlT :: r -> m (CtlResult ps r m a)}

cmapCtlT :: (Monad m) => (r1 -> r2) -> CtlT ps r2 m a -> CtlT ps r1 m a
cmapCtlT f (CtlT m) = CtlT \r ->
    m (f r) <&> \case
        Pure x -> Pure x
        Ctl ctls -> Ctl $ forCtls ctls \case
            Control ctl q -> Control ctl (tsingleton $ cmapCtlT f . qApp q)

data CtlResult ps r m a
    = Pure a
    | Ctl (Ctls ps r m a)

type Ctls ps r m a = StackUnion ps (CtlFrame ps r m a)

data CtlFrame (ps :: [PromptFrame]) r (m :: Type -> Type) (a :: Type) (p :: PromptFrame) (u :: [PromptFrame]) where
    PrimOp :: PrimOp ps r m a p u -> CtlFrame ps r m a p u
    Under :: StackUnion u (CtlFrame ps r m a) -> CtlFrame ps r m a (Prompt ans r') u

data PrimOp (ps :: [PromptFrame]) r (m :: Type -> Type) (a :: Type) (p :: PromptFrame) (u :: [PromptFrame]) where
    Control :: ((b -> CtlT u r' m ans) -> CtlT u r' m ans) -> FTCQueue (CtlT ps r m) b a -> PrimOp ps r m a (Prompt ans r') u

mapCtls :: (forall x u. PrimOp ps r m a x u -> PrimOp ps' r' m' a' x u) -> StackUnion xs (CtlFrame ps r m a) -> StackUnion xs (CtlFrame ps' r' m' a')
mapCtls f = mapStackUnion \case
    PrimOp op -> PrimOp $ f op
    Under u -> Under $ mapCtls f u

forCtls :: StackUnion xs (CtlFrame ps r m a) -> (forall x u. PrimOp ps r m a x u -> PrimOp ps' r' m' a' x u) -> StackUnion xs (CtlFrame ps' r' m' a')
forCtls u f = mapCtls f u

instance (Applicative f) => Functor (CtlResult ps r f) where
    fmap f = \case
        Pure x -> Pure $ f x
        Ctl ctls -> Ctl $ forCtls ctls \case
            Control ctl q -> Control ctl $ q |> (CtlT . const . pure . Pure . f)

instance (Applicative f) => Functor (CtlT ps r f) where
    fmap f (CtlT m) = CtlT $ fmap (fmap f) . m

instance (Monad m) => Applicative (CtlT ps r m) where
    pure = CtlT . const . pure . Pure
    (<*>) = ap

instance (Monad m) => Monad (CtlT ps r m) where
    CtlT m >>= f =
        CtlT \r ->
            m r >>= \case
                Pure x -> unCtlT (f x) r
                Ctl ctls -> pure $ Ctl $ forCtls ctls \case
                    Control ctl q -> Control ctl $ q |> f

instance (MonadIO m) => MonadIO (CtlT ps r m) where
    liftIO m = CtlT \_ -> liftIO $ Pure <$> m

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] r m) where
    withRunInIO f = CtlT \r -> withRunInIO \run -> Pure <$> f (run . runCtlT r)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f) => Unlift b (ReaderT r f) where
    withRunInBase f = ReaderT \r -> withRunInBase \run -> f $ run . flip runReaderT r

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] r f) where
    withRunInBase f = CtlT \r -> Pure <$> withRunInBase \run -> f (run . runCtlT r)

prompt ::
    forall r r' ps m ans.
    (Monad m) =>
    (r' -> r) ->
    (Proxy ps -> CtlT (Prompt ans r' : ps) r m ans) ->
    CtlT ps r' m ans
prompt f m =
    CtlT \r ->
        unCtlT (m Proxy) (f r) >>= \case
            Pure x -> pure $ Pure x
            Ctl ctls -> case ctls of
                Here (PrimOp (Control ctl q)) -> unCtlT (ctl \x -> prompt f \_ -> qApp q x) r
                Here (Under u) -> promptUnder u
                There u -> promptUnder u
  where
    promptUnder :: StackUnion ps (CtlFrame (Prompt ans r' : ps) r m ans) -> m (CtlResult ps r' m ans)
    promptUnder u =
        pure $ Ctl $ forCtls u \case
            Control ctl q -> Control ctl $ tsingleton \x -> prompt f \_ -> qApp q x

control :: (Member u ps (Prompt ans r'), Applicative m) => Proxy u -> ((a -> CtlT u r' m ans) -> CtlT u r' m ans) -> CtlT ps r m a
control p f = CtlT . const . pure . Ctl . inject p $ PrimOp $ Control f (tsingleton $ CtlT . const . pure . Pure)

abort :: (Member u ps (Prompt ans r'), Monad m) => Proxy u -> ans -> CtlT ps r m a
abort p ans = control p \_ -> pure ans

under :: (Member u ps (Prompt ans r'), Monad m) => Proxy u -> (r -> r') -> r' -> CtlT (Prompt ans r' : u) r' m a -> CtlT ps r m a
under p f r (CtlT m) =
    CtlT \_ ->
        m r <&> \case
            Pure x -> Pure x
            Ctl ctls -> Ctl $ inject p $ case ctls of
                Here (PrimOp (Control ctl q)) -> PrimOp $ Control ctl (tsingleton $ under p f r . qApp q)
                Here (Under u) -> mkUnder u
                There u -> mkUnder u
  where
    mkUnder ctls = Under $ forCtls ctls \case
        Control ctl q -> Control ctl (tsingleton $ underk p f $ qApp q)

underk :: (Member u ps (Prompt ans r'), Monad m) => Proxy u -> (r -> r') -> (b -> CtlT (Prompt ans r' : u) r' m a) -> (b -> CtlT ps r m a)
underk p f k x = CtlT \r -> unCtlT (under p f (f r) $ k x) r

qApp :: (Monad m) => FTCQueue (CtlT ps r m) a b -> a -> CtlT ps r m b
qApp q x = CtlT \r -> case tviewl q of
    TOne k -> unCtlT (k x) r
    k :| t ->
        unCtlT (k x) r >>= \case
            Pure y -> unCtlT (qApp t y) r
            Ctl ctls -> pure $ Ctl $ forCtls ctls \case
                Control ctl q' -> Control ctl $ q' >< t

liftCtlT :: (Functor f) => f a -> CtlT fs r f a
liftCtlT a = CtlT \_ -> Pure <$> a

runCtlT :: (Functor f) => r -> CtlT '[] r f a -> f a
runCtlT r (CtlT m) =
    m r <&> \case
        Pure x -> x
        Ctl ctls -> case ctls of {}

runPure :: r -> CtlT '[] r Identity a -> a
runPure r (CtlT m) = case runIdentity (m r) of
    Pure x -> x
    Ctl ctls -> case ctls of {}

data Status a b ps v m r = Done r | Continue a (b -> CtlT ps v m (Status a b ps v m r))

yield :: (Member u ps (Prompt (Status a b u v m r) v), Monad m) => Proxy u -> a -> CtlT ps v m b
yield p x = control p \k -> pure $ Continue x k

runCoroutine ::
    (Monad m) =>
    (Proxy ps -> CtlT (Prompt (Status a b ps v m r) v : ps) v m r) ->
    CtlT ps v m (Status a b ps v m r)
runCoroutine f = prompt id \p -> Done <$> f p

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
