{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Inspired by Kyo's method for handling higher‑order effects, this is a pure, well‑typed
implementation of the major effects.

The effect system (the "Eff" monad) defined and used here is itself equivalent to
freer‑simple (https://hackage.haskell.org/package/freer-simple), a simple, pure, first‑order
effect system implemented with a plain Freer monad (unlike Polysemy, it isn't generalized to
higher‑order) and an open‑union. Up to this point, there's nothing novel from the standpoint of
algebraic effects in Haskell.

What's new here is the `pull` function, a very simple yet previously elusive technique that makes
everything click.  See the `pull` function's doc for details.

It was Kyo's realization of higher‑order effects that showed how to handle them elegantly. In
particular, I finally understood it by experimenting with the Reader effect example in the reply
on X: https://x.com/fbrasisil/status/1945476793814925429

In Kyo, running the equivalent of the following Haskell-style pseudo‑code prints `0`, whereas a
typical Haskell effect system would print `42`.

( It may look like the type of `modifyZero` doesn’t line up with `runReader`, but that mismatch is
the essential insight.
See this Scala snippet for details: https://scastie.scala-lang.org/EmUHdYHzRcyPTmAfyiq7HQ )

@
modifyZero :: forall es a. Eff es a -> Eff es a
modifyZero = runReader 0

do
    x :: Int <- runReader 42 $ modifyZero $ ask
    print x
@

This is quite surprising if you're used to Haskell ('s effect systems), because the type variable
`es` in `modifyZero` is completely unconstrained, and using the fact that `Reader Int` lives in that
list to alter behavior violates parametricity.

In Kyo, this behavior is achieved not by type-level computation but by using Scala's runtime type
information to decide effect (tag) equality at runtime. In Haskell terms, it's like having an
implicit `Typeable (e :: Effect)` for every effect and using that to match effects.

Thanks to this, Kyo naturally adopts a completely different approach to realizing higher‑order
effects. Even if the effect system doesn't natively support higher‑order effects, you can encode
them in a formally first‑order shape. I call this technique **first‑order embedding of higher‑order effects**,
and the code in this file is meant to demonstrate that clever trick.

The `pull` function lets you emulate this behavior without breaking parametricity by taking a
membership argument. By carrying that membership evidence inside the operation data when you
encode a higher‑order effect, the `pull` function is given proof that the effect indeed appears in
the list. This novel technique makes it possible to implement Kyo's higher‑order‑effect handling
strategy in Haskell as well.
-}
module Control.Effect.Simple where

import Control.Arrow (first)
import Control.Monad ((>=>))
import Control.Monad.Trans.Freer (FreerF (..), FreerT (FreerT), qApp, runFreerT, transFreerT)
import Data.FTCQueue (tsingleton)
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Type)
import Data.List (singleton)

-- ====================================================================================================
--  * Effect system implementation
-- ====================================================================================================

-- | Kind of effects.
type Effect = Type -> Type

-- | The Eff monad.
type Eff es = FreerT (Union es App) Identity

-------------------- ** Open union

-- | Generic open union
data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

-- | Membership of an element in the open union (evidence).
data Membership h x xs = Membership
    { inject :: forall a. h x a -> Union xs h a
    , project :: forall a. Union xs h a -> Maybe (h x a)
    }

class x :> xs where
    membership :: Membership h x xs

instance e :> (e : es) where
    membership = Membership Here \case
        Here x -> Just x
        There _ -> Nothing

instance {-# OVERLAPPABLE #-} (e :> es) => e :> (e' : es) where
    membership = Membership (There . inject membership) \case
        Here _ -> Nothing
        There u -> project membership u

-- | Helper type to specialize an open union for effect lists.
newtype App f a = App {getApp :: f a}

-- | Membership within the effect list.
type Member = Membership App :: Effect -> [Effect] -> Type

-------------------- ** Handling effects

-- | A "deep handler" in the terminology of algebraic effects.
interpret ::
    -- | Value handler
    (a -> Eff es b) ->
    -- | Effect handler
    (forall x. e x -> (x -> Eff es b) -> Eff es b) ->
    Eff (e : es) a ->
    Eff es b
interpret ret hdl (FreerT (Identity m)) =
    FreerT . Identity $ case m of
        Pure x -> runIdentity . runFreerT $ ret x
        Freer f q ->
            let k = interpret ret hdl . qApp q
             in case f of
                    Here e -> runIdentity . runFreerT $ hdl (getApp e) k
                    There u -> Freer u (tsingleton k)

{- |
A version of `interpret` in which the interpretation is not automatically recursive in the
continuation passed to the handler. In algebraic-effects terminology, this is called a "shallow handler."
-}
interpretShallow ::
    (a -> Eff es b) ->
    (forall x. e x -> (x -> Eff (e : es) b) -> Eff es b) ->
    Eff (e : es) a ->
    Eff es b
interpretShallow ret hdl (FreerT (Identity m)) =
    FreerT . Identity $ case m of
        Pure x -> runIdentity . runFreerT $ ret x
        Freer f q ->
            let k = qApp q
             in case f of
                    Here e -> runIdentity . runFreerT $ hdl (getApp e) (k >=> raise . ret)
                    There u -> Freer u (tsingleton $ interpretShallow ret hdl . k)

-------------------- ** Miscellaneous functions

{- |
This function provides the core technique for **first‑order embedding of higher‑order effects**.
It 'digs up' an effect @e@ that's buried somewhere in the polymorphic effect list @es@ using the
membership evidence, and 'pulls' it all the way to the front of the list.

After pulling, type-level @es@ still contains @e@ (now duplicated at the head), but at the value
level all operations for @e@ are sucked out of their original slot and moved to the top.
In other words, it moves (not copies) operations between slots, like pumping water up from below.
-}
pull :: Member e es -> Eff es a -> Eff (e : es) a
pull i = transFreerT \u -> case project i u of
    Just e -> Here e
    Nothing -> There u

-- | Rewrite the operations of effect @e@ stored in the effect list @es@.
rewrite :: Member e es -> (forall x. e x -> e x) -> Eff es a -> Eff es a
rewrite i f = transFreerT \u -> case project i u of
    Just e -> inject i $ App $ f $ getApp e
    Nothing -> u

-- | Extend the effect list as a set (i.e. introduce a new effect to the front).
raise :: Eff es a -> Eff (e : es) a
raise = transFreerT There

-------------------- ** Performing effects

-- | Perform an effect.
perform :: (e :> es) => e a -> Eff es a
perform = send membership

-- | Perform a higher-order effect.
performH :: (e :> es) => e (Eff es a) -> Eff es a
performH op = performWith op id

-- | Perform an effect with a continuation.
performWith :: (e :> es) => e a -> (a -> Eff es b) -> Eff es b
performWith = sendWith membership

-- | Perform an effect in the slot specified by the given membership.
send :: Member e es -> e a -> Eff es a
send i op = sendWith i op pure

-- | Perform an effect with a continuation in the slot specified by the given membership.
sendWith :: Member e es -> e a -> (a -> Eff es b) -> Eff es b
sendWith i op k = FreerT $ Identity $ Freer (inject i $ App op) (tsingleton k)

-------------------- ** Eliminating the Eff monad

-- | Treat the last remaining effect as a monad and drop into it to eliminate the Eff monad.
runEff :: (Monad m) => Eff '[m] a -> m a
runEff (FreerT m) = case runIdentity m of
    Pure x -> pure x
    Freer (Here (App n)) q -> n >>= runEff . qApp q
    Freer (There u) _ -> case u of {}

-- | Extract a pure result value when all effects have been handled.
runPure :: Eff '[] a -> a
runPure (FreerT m) = case runIdentity m of
    Pure x -> x
    Freer u _ -> case u of {}

-- ====================================================================================================
--  * Definitions of various effects
-- ====================================================================================================

-------------------- ** Reader effect

data Reader r :: Effect where
    Ask :: Reader r r
    Local :: Member (Reader r) es -> (r -> r) -> Eff es a -> Reader r (Eff es a)

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = interpret pure \case
    Ask -> \k -> k r
    Local i f m -> \k -> k $ runReader (f r) (pull i m)

local :: (Reader r :> es) => (r -> r) -> Eff es a -> Eff es a
local f m = performH $ Local membership f m

-------------------- ** Coroutine effect

data Yield i o :: Effect where
    Yield :: i -> Yield i o o

data Status f i o a = Done a | Continue i (o -> f (Status f i o a))

runCoroutine :: Eff (Yield i o : es) a -> Eff es (Status (Eff es) i o a)
runCoroutine = interpret (pure . Done) \(Yield i) k -> pure $ Continue i k

-------------------- ** Exception effect

data Except e :: Effect where
    Throw :: e -> Except e a
    Catch :: Member (Except e) es -> Eff es a -> (e -> Eff es a) -> Except e (Eff es a)

catch :: (Except e :> es) => Eff es a -> (e -> Eff es a) -> Eff es a
catch m hdl = performH $ Catch membership m hdl

runExcept :: Eff (Except e : es) a -> Eff es (Either e a)
runExcept = interpret (pure . Right) \case
    Throw e -> \_ -> pure $ Left e
    Catch i m hdl -> \k -> k do
        runExcept (pull i m) >>= \case
            Left e -> hdl e
            Right x -> pure x

-------------------- ** Writer effect

data Writer w :: Effect where
    Tell :: w -> Writer w ()
    Listen :: Member (Writer w) es -> Eff es a -> Writer w (Eff es (w, a))
    Censor :: Member (Writer w) es -> (w -> w) -> Eff es a -> Writer w (Eff es a)

listen :: (Writer w :> es) => Eff es a -> Eff es (w, a)
listen m = performH $ Listen membership m

censor :: (Writer w :> es) => (w -> w) -> Eff es a -> Eff es a
censor f m = performH $ Censor membership f m

runWriter :: (Monoid w) => Eff (Writer w : es) a -> Eff es (w, a)
runWriter = interpret (pure . (mempty,)) \case
    Tell w -> \k -> first (w <>) <$> k ()
    Listen i m -> \k -> k $ runWriter (pull i m)
    Censor i f m -> \k -> k do
        (w, x) <- runWriter (pull i m)
        send i $ Tell $ f w
        pure x

runWriterPre :: (Monoid w) => Eff (Writer w : es) a -> Eff es (w, a)
runWriterPre = interpret (pure . (mempty,)) \case
    Tell w -> \k -> first (w <>) <$> k ()
    Listen i m -> \k -> k $ runWriter (pull i m)
    Censor i f m -> \k ->
        k $
            rewrite
                i
                \case
                    Tell w -> Tell $ f w
                    Listen i' m' -> Listen i' m'
                    Censor i' f' m' -> Censor i' f' m'
                m

-------------------- ** Non-deterministic computation effect

data NonDet :: Effect where
    Empty :: NonDet a
    Choose :: NonDet Bool
    ObserveAll :: Member NonDet es -> Eff es a -> NonDet (Eff es [a])

runNonDet :: Eff (NonDet : es) a -> Eff es [a]
runNonDet = interpret (pure . singleton) \case
    Empty -> \_ -> pure []
    Choose -> \k -> liftA2 (++) (k False) (k True)
    ObserveAll i m -> \k -> k $ runNonDet $ pull i m

observeAll :: (NonDet :> es) => Eff es a -> Eff es [a]
observeAll m = performH $ ObserveAll membership m

choice :: (NonDet :> es) => [a] -> Eff es a
choice [] = perform Empty
choice (x : xs) =
    perform Choose >>= \case
        False -> pure x
        True -> choice xs

-- ====================================================================================================
--  * Tests
-- ====================================================================================================

-------------------- ** Example semantics-checking problems using [SemanticsZoo](https://github.com/lexi-lambda/eff/blob/master/notes/semantics-zoo.md)

-- Work in progress

-------------------- ** Miscellaneous run examples

-- >>> testNonDet
-- [[1,2,3,0],[1,2,3,1]]

testNonDet :: [[Int]]
testNonDet = runPure $ runNonDet do
    b <- perform Choose
    observeAll do
        choice [1, 2, 3, if b then 1 else 0]

-- >>> testNSR
-- (1,1,42)

testNSR :: (Int, Int, Int)
testNSR = runPure do
    s <- runReader @Int 0 $ runCoroutine @() @() do
        (x, y) <- local @Int (+ 1) do
            x <- perform $ Ask @Int
            perform $ Yield @() @() ()
            y <- perform $ Ask @Int
            pure (x, y)

        z <- perform $ Ask @Int

        pure (x, y, z)

    case s of
        Continue () k -> do
            s' <- runReader @Int 42 $ k ()
            case s' of
                Done r -> pure r
                Continue _ _ -> error "unreachable"
        Done _ -> error "unreachable"

-- >>> testWriter
-- ("goodbye world",())

testWriter :: (String, ())
testWriter = runPure $ runWriterPre do
    censor (\s -> if s == "hello" then "goodbye" else s) do
        perform $ Tell "hello"
        perform $ Tell " world"
