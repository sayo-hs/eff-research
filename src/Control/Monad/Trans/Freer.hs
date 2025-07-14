module Control.Monad.Trans.Freer where

import Control.Monad (ap)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.FTCQueue (FTCQueue, ViewL (TOne, (:|)), tsingleton, tviewl, (><), (|>))
import Data.Functor ((<&>))

-- | The base functor for a freer monad.
data FreerF f a g
    = Pure a
    | forall x. Freer (f x) (FTCQueue g x a)

-- | The freer monad transformer for a type constructor @f@
newtype FreerT f m a = FreerT {runFreerT :: m (FreerF f a (FreerT f m))}

instance (Applicative g) => Functor (FreerT f g) where
    fmap f (FreerT m) =
        FreerT $
            m <&> \case
                Pure x -> Pure $ f x
                Freer g q -> Freer g $ q |> (FreerT . pure . Pure . f)

instance (Monad m) => Applicative (FreerT f m) where
    pure = FreerT . pure . Pure
    (<*>) = ap

instance (Monad m) => Monad (FreerT f m) where
    FreerT m >>= f =
        FreerT $
            m >>= \case
                Pure x -> runFreerT $ f x
                Freer g k -> pure $ Freer g $ k |> f

instance (MonadIO m) => MonadIO (FreerT f m) where
    liftIO m = FreerT $ liftIO $ Pure <$> m

liftF :: (Applicative g) => f a -> FreerT f g a
liftF f = FreerT $ pure $ Freer f (tsingleton $ FreerT . pure . Pure)

transFreerT :: (Monad m) => (forall x. f x -> g x) -> FreerT f m a -> FreerT g m a
transFreerT phi (FreerT m) =
    FreerT $
        m <&> \case
            Pure x -> Pure x
            Freer f q -> Freer (phi f) (tsingleton $ transFreerT phi . qApp q)

hoistFreerT :: (Monad m) => (forall x. m x -> n x) -> FreerT f m a -> FreerT f n a
hoistFreerT phi (FreerT m) =
    FreerT . phi $
        m <&> \case
            Pure x -> Pure x
            Freer f q -> Freer f (tsingleton $ hoistFreerT phi . qApp q)

qApp :: (Monad m) => FTCQueue (FreerT f m) a b -> a -> FreerT f m b
qApp q x = FreerT case tviewl q of
    TOne k -> runFreerT $ k x
    k :| t ->
        runFreerT (k x) >>= \case
            Pure y -> runFreerT $ qApp t y
            Freer f q' -> pure $ Freer f $ q' >< t

liftFreerT :: (Functor g) => g a -> FreerT f g a
liftFreerT a = FreerT $ Pure <$> a
