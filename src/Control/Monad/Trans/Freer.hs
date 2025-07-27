{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Control.Monad.Trans.Freer where

import Control.Monad (ap)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.FTCQueue (FTCQueue, ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Functor ((<&>))
import Data.Kind (Type)

-- | The base functor for a freer monad.
data FreerF f a g
    = Pure a
    | forall x. Freer (f x) (FTCQueue g x a)

-- | The freer monad transformer for a type constructor @f@
newtype FreerT (f :: k -> Type -> Type) (m :: k -> Type -> Type) a = FreerT {runFreerT :: forall s. m s (FreerF (f s) a (FreerT f m))}

instance (forall s. Applicative (g s)) => Functor (FreerT f g) where
    fmap f (FreerT m) =
        FreerT $
            m <&> \case
                Pure x -> Pure $ f x
                Freer g q -> Freer g $ q |> \x -> FreerT $ pure . Pure . f $ x

instance (forall s. Monad (m s)) => Applicative (FreerT f m) where
    pure x = FreerT $ pure $ Pure x
    (<*>) = ap

instance (forall s. Monad (m s)) => Monad (FreerT f m) where
    FreerT m >>= f =
        FreerT $
            m >>= \case
                Pure x -> runFreerT $ f x
                Freer g k -> pure $ Freer g $ k |> f

instance (forall s. MonadIO (m s)) => MonadIO (FreerT f m) where
    liftIO m = FreerT $ liftIO $ Pure <$> m

liftF :: (forall s. Applicative (g s)) => (forall s. f s a) -> FreerT f g a
liftF f = FreerT $ pure $ Freer f (tsingleton \x -> FreerT $ pure $ Pure x)

transFreerT :: (forall s. Monad (m s)) => (forall s x. f s x -> g s x) -> FreerT f m a -> FreerT g m a
transFreerT phi (FreerT m) =
    FreerT $
        m <&> \case
            Pure x -> Pure x
            Freer f q -> Freer (phi f) (tsingleton $ transFreerT phi . qApp q)

hoistFreerT :: (forall s. Monad (m s)) => (forall s x. m s x -> n s x) -> FreerT f m a -> FreerT f n a
hoistFreerT phi (FreerT m) =
    FreerT $
        phi $
            m <&> \case
                Pure x -> Pure x
                Freer f q -> Freer f (tsingleton $ hoistFreerT phi . qApp q)

qApp :: (forall s. Monad (m s)) => FTCQueue (FreerT f m) a b -> a -> FreerT f m b
qApp q x = FreerT case tviewl q of
    TOne k -> runFreerT $ k x
    k :| t ->
        runFreerT (k x) >>= \case
            Pure y -> runFreerT $ qApp t y
            Freer f q' -> pure $ Freer f $ q' >< t

liftFreerT :: (forall s. Functor (g s)) => (forall s. g s a) -> FreerT f g a
liftFreerT a = FreerT $ Pure <$> a
