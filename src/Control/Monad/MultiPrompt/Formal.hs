{-# LANGUAGE TypeData #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Copyright   :  (c) 2025 Sayo contributors
License     :  MPL-2.0 (see the LICENSE file)
Maintainer  :  ymdfield@outlook.jp

A fully type-safe multi-prompt/control monad, inspired by [speff](https://github.com/re-xyr/speff) and [turbolift](https://marcinzh.github.io/turbolift/).
-}
module Control.Monad.MultiPrompt.Formal where

import Control.Monad.Trans.Freer (FreerF (Freer, Pure), FreerT (..), hoistFreerT, liftF, qApp, transFreerT)
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

infix 4 <
class u < xs where
    sub :: Proxy u -> Sub u xs

data Sub (u :: [k]) (xs :: [k])
    = Sub
    { weaken :: forall l h (a :: l). StackUnion u h a -> StackUnion xs h a
    , strengthen :: forall l h (a :: l). StackUnion xs h a -> Maybe (StackUnion u h a)
    }

instance {-# INCOHERENT #-} (u < xs) => u < x : xs where
    sub p =
        Sub
            { weaken = There . weaken (sub p)
            , strengthen = \case
                Here _ -> Nothing
                There u -> strengthen (sub p) u
            }

instance xs < xs where
    sub _ = Sub{weaken = id, strengthen = Just}

type data PromptFrame = Prompt (Type -> Type) Type [PromptFrame]

{- | A type-safe multi-prompt/control monad transformer with reader environment.

    @ps@: A list of the current prompt stack frames.

    @r@: The reader environment.

    @m@: The base monad.
-}
newtype CtlT (ps :: [PromptFrame]) r m a = CtlT {unCtlT :: FreerT (StackUnion ps (Control m)) (ReaderT r m) a}
    deriving (Functor, Applicative, Monad, MonadIO)

data Control (m :: Type -> Type) (p :: PromptFrame) (u :: [PromptFrame]) (a :: Type) where
    Control :: (forall w u x. Sub (Prompt f r u' : u) w -> (a -> CtlT w r m (f x)) -> CtlT w r m (f x)) -> Control m (Prompt f r u') u a
    Control0 :: (forall x. (a -> CtlT u' r m (f x)) -> CtlT u' r m (f x)) -> Control m (Prompt f r u') u a

cmapCtlT :: (Monad m) => (r -> r') -> CtlT ps r' m a -> CtlT ps r m a
cmapCtlT f = CtlT . hoistFreerT (ReaderT . (. f) . runReaderT) . unCtlT

runCtlT :: (Functor f) => r -> CtlT '[] r f a -> f a
runCtlT r (CtlT (FreerT (ReaderT m))) =
    m r <&> \case
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
    withRunInBase f = CtlT $ FreerT $ Pure <$> withRunInBase \run -> f (run . ReaderT . flip runCtlT)

prompt ::
    forall f r' u' r ps m a.
    (Monad m) =>
    (r' -> r) ->
    CtlT (Prompt f r' ps : ps) r m (f a) ->
    CtlT ps r' m (f a)
prompt f m =
    CtlT . FreerT $ ReaderT \r ->
        runReaderT (runFreerT (unCtlT m)) (f r) >>= \case
            Pure x -> pure $ Pure x
            Freer ctls q ->
                let k x = CtlT $ qApp q x
                 in case ctls of
                        Here (Control ctl) -> runReaderT (runFreerT $ unCtlT $ prompt id $ ctl (Sub id Just) $ cmapCtlT f . k) r
                        Here (Control0 ctl) -> runReaderT (runFreerT $ unCtlT $ ctl $ prompt f . k) r
                        There u -> pure $ Freer u (tsingleton $ unCtlT . prompt f . k)

delimit ::
    forall f r r' u' u ps m a.
    (Monad m) =>
    Sub (Prompt f r' u' : u) ps ->
    (r -> r') ->
    CtlT ps r m (f a) ->
    CtlT ps r m (f a)
delimit i f m =
    CtlT . FreerT $ ReaderT \r ->
        runReaderT (runFreerT (unCtlT m)) r >>= \case
            Pure x -> pure $ Pure x
            Freer ctls q ->
                let k x = delimit i f $ CtlT $ qApp q x
                 in case strengthen i ctls of
                        Just (Here (Control ctl)) -> runReaderT (runFreerT . unCtlT $ cmapCtlT f $ ctl i $ cmapCtlT (const r) . k) r
                        _ -> pure $ Freer ctls q

control ::
    (Applicative m) =>
    Sub (Prompt f r' u' : u) ps ->
    (forall w u x. Sub (Prompt f r' u' : u) w -> (a -> CtlT w r' m (f x)) -> CtlT w r' m (f x)) ->
    CtlT ps r m a
control i f = CtlT . liftF . weaken i $ Here $ Control f

control0 ::
    (Applicative m) =>
    Sub (Prompt f r' u' : u) ps ->
    (forall x. (a -> CtlT u' r' m (f x)) -> CtlT u' r' m (f x)) ->
    CtlT ps r m a
control0 i f = CtlT . liftF . weaken i $ Here $ Control0 f

abort :: (Monad m) => Sub (Prompt f r' u' : u) ps -> (forall x. f x) -> CtlT ps r m a
abort i ans = control i \_ _ -> pure ans

under :: (Monad m) => Sub u ps -> (r -> r') -> r' -> CtlT u r' m a -> CtlT ps r m a
under i f r (CtlT (FreerT (ReaderT m))) =
    CtlT . FreerT $ ReaderT \_ ->
        m r <&> \case
            Pure x -> Pure x
            Freer u q -> Freer (weaken i u) (tsingleton $ unCtlT . underk i f (CtlT . qApp q))

underk ::
    (Monad m) =>
    Sub u ps ->
    (r -> r') ->
    (b -> CtlT u r' m a) ->
    (b -> CtlT ps r m a)
underk i f k x = CtlT . FreerT $ ReaderT \r -> runReaderT (runFreerT $ unCtlT $ under i f (f r) (k x)) r

raise :: (Monad m) => CtlT ps r m a -> CtlT (p : ps) r m a
raise = CtlT . transFreerT There . unCtlT

data Status a b ps r m c = Done c | Continue a (b -> CtlT ps r m (Status a b ps r m c))

yield :: (Monad m) => Sub (Prompt (Status a b u' r' m) r' u' : u) ps -> a -> CtlT ps r m b
yield i x = control0 i \k -> pure $ Continue x $ undefined . k

runCoroutine ::
    (Monad m) =>
    (Proxy (Prompt (Status a b ps r m) r ps : ps) -> CtlT (Prompt (Status a b ps r m) r ps : ps) r m c) ->
    CtlT ps r m (Status a b ps r m c)
runCoroutine f = prompt id $ Done <$> f Proxy

{-
test :: IO ()
test = runCtlT () do
    s <- runCoroutine \c -> do
        liftIO $ putStrLn "a"
        i <- yield (sub c) 0
        liftIO $ print i
    case s of
        Continue (x :: Int) resume -> do
            _ <- resume $ x + 1
            pure ()
        Done () -> pure ()

runExc ::
    (Monad m) =>
    (Proxy (Prompt (Either e) r : ps) -> CtlT (Prompt (Either e) r : ps) r m a) ->
    CtlT ps r m (Either e a)
runExc f = prompt id $ Right <$> f Proxy

throw :: (Monad m) => Sub (Prompt (Either e) r' : u) ps -> e -> CtlT ps r m a
throw i e = abort i $ Left e

try :: (Monad m) => Sub (Prompt (Either e) r : u) ps -> CtlT ps r m a -> CtlT ps r m (Either e a)
try i m = delimit i id $ Right <$> m

catch :: (Monad m) => Sub (Prompt (Either e) r : u) ps -> CtlT ps r m a -> (e -> CtlT ps r m a) -> CtlT ps r m a
catch i m hdl = try i m >>= either hdl pure

-- >>> test2
-- Right 3

test2 :: Either String Int
test2 = runPure () $ runExc \exc -> do
    catch
        (sub exc)
        (throw (sub exc) "abc")
        \e -> pure $ length e

runNonDet :: (Monad m) => (Proxy (Prompt [] r : ps) -> CtlT (Prompt [] r : ps) r m a) -> CtlT ps r m [a]
runNonDet f = prompt id $ singleton <$> f Proxy

empty :: (Monad m) => Sub (Prompt [] r' : u) ps -> CtlT ps r m a
empty i = abort i []

choice :: forall r m u ps a. (Monad m) => Sub (Prompt [] r : u) ps -> [CtlT ps r m a] -> CtlT ps r m a
choice i ms = do
    xs <- concat <$> mapM (delimit i id . fmap singleton) ms
    control i \i' k -> concat <$> mapM (delimit i' id . k) xs

-- >>> test3
-- [0,4]

test3 :: [Int]
test3 = runPure () $ runNonDet \nd -> do
    x <- runExc \exc -> do
        x :: Int <- choice (sub nd) [pure 0, pure 1]
        if x == 1
            then throw (sub exc) "test"
            else pure x
    pure $ either length id x
-}
