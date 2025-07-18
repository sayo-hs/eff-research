{-
data Provider e i dep f :: Effect where
    Provide :: dep es -> i -> Eff (e : es) a -> Provider e dep i f (Eff es (f a))

provide :: (Provider e dep i f :> es) => dep es -> i -> Eff (e : es) a -> Eff es (f a)
provide dep i m = performH $ Provide dep i m

data ShallowHandler e es a b = Handler
    { valueHandler :: a -> Eff es b
    , effectHandler :: forall x. e x -> (x -> Eff (e : es) b) -> Eff es b
    }

data DeepHandler e es a b = DeepHandler
    { valueHandlerDeep :: a -> Eff es b
    , effectHandlerDeep :: forall x. e x -> (x -> Eff es b) -> Eff es b
    }

type Handler e es = forall a b. ShallowHandler e es a b

deep :: DeepHandler e es a b -> ShallowHandler e es a b
deep (DeepHandler ret hdl) = Handler ret \e k -> hdl e (interpret pure hdl . k)

runProvider :: (Applicative f) => (forall es'. dep es' -> i -> Handler e es') -> Eff (Provider e dep i f : es) a -> Eff es (f a)
runProvider h =
    interpret (pure . pure) \(Provide dep i m) k ->
        let Handler ret hdl = h dep i in k $ interpretShallow ret hdl m
-}
