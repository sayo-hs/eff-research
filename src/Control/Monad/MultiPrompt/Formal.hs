{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# HLINT ignore "Use fmap" #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use >=>" #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff).
-}
module Control.Monad.MultiPrompt.Formal where

import Control.Monad.Trans.Freer
import Control.Monad.Trans.Reader (ReaderT (ReaderT), runReaderT)
import Data.FTCQueue (tsingleton)
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
data StackUnion (xs :: [k]) (h :: k -> [k] -> l -> Type) (a :: l) where
    Here :: h x xs a -> StackUnion (x : xs) h a
    There :: StackUnion xs h a -> StackUnion (x : xs) h a

mapStackUnion :: (forall x r. h x r a -> i x r a) -> StackUnion xs h a -> StackUnion xs i a
mapStackUnion f = \case
    Here x -> Here $ f x
    There xs -> There $ mapStackUnion f xs

forStackUnion :: StackUnion xs h a -> (forall x r. h x r a -> i x r a) -> StackUnion xs i a
forStackUnion u f = mapStackUnion f u

class Member r xs x | r xs -> x where
    membership :: Membership r xs x

data Membership (r :: [k]) (xs :: [k]) (x :: k)
    = Membership
    { inject :: forall l h (a :: l). h x r a -> StackUnion xs h a
    , project :: forall l h (a :: l). StackUnion xs h a -> Maybe (h x r a)
    }

instance Member xs (x : xs) x where
    membership =
        Membership
            Here
            \case
                Here x -> Just x
                There _ -> Nothing

member :: (Member r xs x) => Proxy r -> Membership r xs x
member _ = membership

instance {-# OVERLAPPABLE #-} (Member r xs x) => Member r (x' : xs) x where
    membership =
        Membership
            (There . inject membership)
            \case
                Here _ -> Nothing
                There xs -> project membership xs

infix 4 <
class r < xs where
    sub :: Sub r xs

newtype Sub (r :: [k]) (xs :: [k])
    = Sub
    { embed ::
        forall l h (a :: l).
        StackUnion r h a ->
        StackUnion xs h a
    }

instance xs < x : xs where
    sub = Sub There

instance {-# OVERLAPPABLE #-} (r < xs) => r < x : xs where
    sub = Sub $ There . embed sub

instance {-# INCOHERENT #-} xs < xs where
    sub = Sub id

instance '[] < xs where
    sub = Sub \case {}

type data PromptFrame = Prompt Type Type

{- | A type-safe multi-prompt/control monad transformer with reader environment.

    @ps@: A list of the current prompt stack frames.

    @r@: The reader environment.

    @m@: The base monad.
-}
newtype CtlT (ps :: [PromptFrame]) r m a = CtlT {unCtlT :: FreerT (StackUnion ps (Control m)) (ReaderT r m) a}
    deriving (Functor, Applicative, Monad, MonadIO)

data Control (m :: Type -> Type) (p :: PromptFrame) (u :: [PromptFrame]) (a :: Type) where
    Control :: ((a -> CtlT u r' m ans) -> CtlT u r' m ans) -> Control m (Prompt ans r') u a

cmapCtlT :: (Monad m) => (r -> r') -> CtlT ps r' m a -> CtlT ps r m a
cmapCtlT f = CtlT . hoistFreerT (ReaderT . (. f) . runReaderT) . unCtlT

runCtlT :: (Functor f) => r -> CtlT '[] r f a -> f a
runCtlT r (CtlT (FreerT m)) =
    runReaderT m r <&> \case
        Pure x -> x
        Freer f _ -> case f of {}

runPure :: r -> CtlT '[] r Identity a -> a
runPure r (CtlT (FreerT (ReaderT m))) = case runIdentity (m r) of
    Pure x -> x
    Freer u _ -> case u of {}

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] r m) where
    withRunInIO f = CtlT $ FreerT $ withRunInIO \run -> Pure <$> f (run . ReaderT . flip runCtlT)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f) => Unlift b (ReaderT r f) where
    withRunInBase f = ReaderT \r -> withRunInBase \run -> f $ run . flip runReaderT r

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] r f) where
    withRunInBase f = CtlT $ FreerT $ ReaderT \r -> Pure <$> withRunInBase \run -> f (run . runCtlT r)

prompt ::
    forall r r' ps m ans.
    (Monad m) =>
    (r' -> r) ->
    CtlT (Prompt ans r' : ps) r m ans ->
    CtlT ps r' m ans
prompt f m =
    CtlT $ FreerT $ ReaderT \r ->
        runReaderT (runFreerT $ unCtlT m) (f r) >>= \case
            Pure x -> pure $ Pure x
            Freer ctls q ->
                let k x = prompt f $ CtlT $ qApp q x
                 in case ctls of
                        Here (Control ctl) -> runReaderT (runFreerT $ unCtlT $ ctl k) r
                        There u -> pure $ Freer u (tsingleton $ unCtlT . k)

control ::
    (Applicative m) =>
    Membership u ps (Prompt ans r') ->
    ((a -> CtlT u r' m ans) -> CtlT u r' m ans) ->
    CtlT ps r m a
control i = CtlT . liftF . inject i . Control

abort :: (Monad m) => Membership u ps (Prompt ans r') -> ans -> CtlT ps r m a
abort i ans = control i \_ -> pure ans

under :: (Monad m) => Sub u ps -> (r -> r') -> r' -> CtlT u r' m a -> CtlT ps r m a
under s f r (CtlT (FreerT (ReaderT m))) =
    CtlT $ FreerT $ ReaderT \_ ->
        m r <&> \case
            Pure x -> Pure x
            Freer u q -> Freer (embed s u) (tsingleton $ unCtlT . underk s f (CtlT . qApp q))

underk ::
    (Monad m) =>
    Sub u ps ->
    (r -> r') ->
    (b -> CtlT u r' m a) ->
    (b -> CtlT ps r m a)
underk s f k x = CtlT $ FreerT $ ReaderT \r -> runReaderT (runFreerT $ unCtlT $ under s f (f r) (k x)) r

liftCtlT :: (Functor f) => f a -> CtlT ps r f a
liftCtlT f = CtlT . liftFreerT $ ReaderT $ const f

raise :: (Monad m) => CtlT ps r m a -> CtlT (p : ps) r m a
raise = CtlT . transFreerT There . unCtlT

data Status a b ps v m r = Done r | Continue a (b -> CtlT ps v m (Status a b ps v m r))

yield :: (Monad m) => Membership u ps (Prompt (Status a b u v m r) v) -> a -> CtlT ps v m b
yield p x = control p \k -> pure $ Continue x k

runCoroutine ::
    (Monad m) =>
    (Proxy ps -> CtlT (Prompt (Status a b ps v m r) v : ps) v m r) ->
    CtlT ps v m (Status a b ps v m r)
runCoroutine f = prompt id $ Done <$> f Proxy

test :: IO ()
test = runCtlT () do
    s <- runCoroutine \c -> do
        liftIO $ putStrLn "a"
        i <- yield (member c) 0
        liftIO $ print i
    case s of
        Continue (x :: Int) resume -> do
            _ <- resume $ x + 1
            pure ()
        Done () -> pure ()
