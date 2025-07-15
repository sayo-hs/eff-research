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
import Data.List (singleton)
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

type Elem u xs x = (Member u xs x, u < xs)

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
class u < xs where
    sub :: Proxy u -> Sub u xs

newtype Sub (r :: [k]) (xs :: [k])
    = Sub
    { embed ::
        forall l h (a :: l).
        StackUnion r h a ->
        StackUnion xs h a
    }

instance xs < x : xs where
    sub _ = Sub There

instance {-# OVERLAPPABLE #-} (r < xs) => r < x : xs where
    sub _ = Sub $ There . embed (sub Proxy)

instance {-# INCOHERENT #-} xs < xs where
    sub _ = Sub id

type data PromptFrame = Prompt (Type -> Type)

{- | A type-safe multi-prompt/control monad transformer with reader environment.

    @ps@: A list of the current prompt stack frames.

    @r@: The reader environment.

    @m@: The base monad.
-}
newtype CtlT (ps :: [PromptFrame]) m a = CtlT {unCtlT :: FreerT (StackUnion ps (Control m)) m a}
    deriving (Functor, Applicative, Monad, MonadIO)

data Control (m :: Type -> Type) (p :: PromptFrame) (u :: [PromptFrame]) (a :: Type) where
    Control :: (forall w x. Sub (Prompt f : u) w -> Membership u w (Prompt f) -> (a -> CtlT w m (f x)) -> CtlT w m (f x)) -> Control m (Prompt f) u a
    Control0 :: (forall x. (a -> CtlT u m (f x)) -> CtlT u m (f x)) -> Control m (Prompt f) u a

runCtlT :: (Functor f) => CtlT '[] f a -> f a
runCtlT (CtlT (FreerT m)) =
    m <&> \case
        Pure x -> x
        Freer f _ -> case f of {}

runPure :: CtlT '[] Identity a -> a
runPure (CtlT (FreerT m)) = case runIdentity m of
    Pure x -> x
    Freer u _ -> case u of {}

instance (MonadUnliftIO m) => MonadUnliftIO (CtlT '[] m) where
    withRunInIO f = CtlT $ FreerT $ withRunInIO \run -> Pure <$> f (run . runCtlT)

class Unlift b m where
    withRunInBase :: ((forall x. m x -> b x) -> b a) -> m a

instance (Unlift b f) => Unlift b (ReaderT r f) where
    withRunInBase f = ReaderT \r -> withRunInBase \run -> f $ run . flip runReaderT r

instance (Unlift b f, Functor f) => Unlift b (CtlT '[] f) where
    withRunInBase f = CtlT $ FreerT $ Pure <$> withRunInBase \run -> f (run . runCtlT)

prompt ::
    forall f ps m a.
    (Monad m) =>
    CtlT (Prompt f : ps) m (f a) ->
    CtlT ps m (f a)
prompt m =
    CtlT . FreerT $
        runFreerT (unCtlT m) >>= \case
            Pure x -> pure $ Pure x
            Freer ctls q ->
                let k x = CtlT $ qApp q x
                 in case ctls of
                        Here (Control ctl) -> runFreerT $ unCtlT $ prompt $ ctl (Sub id) membership k
                        Here (Control0 ctl) -> runFreerT $ unCtlT $ ctl $ prompt . k
                        There u -> pure $ Freer u (tsingleton $ unCtlT . prompt . k)

delimit ::
    forall f u ps m a.
    (Monad m) =>
    Sub (Prompt f : u) ps ->
    Membership u ps (Prompt f) ->
    CtlT ps m (f a) ->
    CtlT ps m (f a)
delimit s i m =
    CtlT . FreerT $
        runFreerT (unCtlT m) >>= \case
            Pure x -> pure $ Pure x
            Freer ctls q ->
                let k x = delimit s i $ CtlT $ qApp q x
                 in case project i ctls of
                        Just (Control ctl) -> runFreerT . unCtlT $ ctl s i k
                        _ -> pure $ Freer ctls q

control ::
    (Applicative m) =>
    Membership u ps (Prompt f) ->
    (forall w x. Sub (Prompt f : u) w -> Membership u w (Prompt f) -> (a -> CtlT w m (f x)) -> CtlT w m (f x)) ->
    CtlT ps m a
control i f = CtlT . liftF . inject i $ Control f

control0 ::
    (Applicative m) =>
    Membership u ps (Prompt f) ->
    (forall x. (a -> CtlT u m (f x)) -> CtlT u m (f x)) ->
    CtlT ps m a
control0 i f = CtlT . liftF . inject i $ Control0 f

abort :: (Monad m) => Membership u ps (Prompt f) -> (forall x. f x) -> CtlT ps m a
abort i ans = control i \_ _ _ -> pure ans

under :: (Monad m) => Sub u ps -> CtlT u m a -> CtlT ps m a
under s (CtlT (FreerT m)) =
    CtlT $
        FreerT $
            m <&> \case
                Pure x -> Pure x
                Freer u q -> Freer (embed s u) (tsingleton $ unCtlT . underk s (CtlT . qApp q))

underk ::
    (Monad m) =>
    Sub u ps ->
    (b -> CtlT u m a) ->
    (b -> CtlT ps m a)
underk s k x = CtlT $ FreerT $ runFreerT $ unCtlT $ under s (k x)

raise :: (Monad m) => CtlT ps m a -> CtlT (p : ps) m a
raise = CtlT . transFreerT There . unCtlT

data Status a b ps m r = Done r | Continue a (b -> CtlT ps m (Status a b ps m r))

yield :: (Monad m, Member u ps (Prompt (Status a b u m))) => Proxy u -> a -> CtlT ps m b
yield p x = control0 (member p) \k -> pure $ Continue x k

runCoroutine ::
    (Monad m) =>
    (Proxy ps -> CtlT (Prompt (Status a b ps m) : ps) m r) ->
    CtlT ps m (Status a b ps m r)
runCoroutine f = prompt $ Done <$> f Proxy

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

runExc ::
    (Monad m) =>
    (Proxy ps -> CtlT (Prompt (Either e) : ps) m a) ->
    CtlT ps m (Either e a)
runExc f = prompt $ Right <$> f Proxy

throw :: (Monad m, Member u ps (Prompt (Either e))) => Proxy u -> e -> CtlT ps m a
throw p e = abort (member p) $ Left e

try :: (Monad m, Member u ps (Prompt (Either e))) => Sub (Prompt (Either e) : u) ps -> CtlT ps m a -> CtlT ps m (Either e a)
try s m = delimit s (member Proxy) $ Right <$> m

catch :: (Monad m, Member u ps (Prompt (Either e))) => Sub (Prompt (Either e) : u) ps -> CtlT ps m a -> (e -> CtlT ps m a) -> CtlT ps m a
catch s m hdl = try s m >>= either hdl pure

-- >>> test2
-- Right 3

test2 :: Either String Int
test2 = runPure $ runExc \exc -> do
    catch
        (Sub id)
        (throw exc "abc")
        \e -> pure $ length e

runNonDet :: (Monad m) => (Proxy ps -> CtlT (Prompt [] : ps) m a) -> CtlT ps m [a]
runNonDet f = prompt $ singleton <$> f Proxy

empty :: (Monad m, Member u ps (Prompt [])) => Proxy u -> CtlT ps m a
empty p = abort (member p) []

choice :: forall m u ps a. (Monad m, Member u ps (Prompt [])) => Sub (Prompt [] : u) ps -> [CtlT ps m a] -> CtlT ps m a
choice s ms = do
    xs <- concat <$> mapM (delimit s membership . fmap singleton) ms
    control (membership @u) \s' i' k -> concat <$> mapM (delimit s' i' . k) xs

-- >>> test3
-- [0,4]

test3 :: [Int]
test3 = runPure $ runNonDet \nd -> do
    x <- runExc \exc -> do
        x :: Int <- choice (Sub There) [pure 0, pure 1]
        if x == 1
            then throw exc "test"
            else pure x
    pure $ either length id x
