{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- SPDX-License-Identifier: MPL-2.0

{- |
Kyoによる高階エフェクトのハンドリング方法にインスパイアされた、主要なエフェクトのwell-typedで純粋な実装です。

ここで定義して使用しているエフェクトシステム (Effモナド) 自体は[freer-simple](https://hackage.haskell.org/package/freer-simple)と等価な、
（polysemyのように高階へは一般化されていない、プレーンな一階の）Freerモナドとopen-unionによるシンプルかつwell-typedで純粋な一階エフェクトシステム実装です。
ここまでの部分については、Haskellの代数的エフェクトにおける新規な点は特ありません。

今回新規な、実現のための本質的な部分は、@pull@関数という非常にシンプルな、しかし気付くまでは決してわからなかったテクニックです。
詳細は@pull@関数のドキュメントを参照してください。

高階エフェクトがをうまくハンドリングする方法があると気付かせてくれたのが、Kyoによる高階エフェクトの実現方法でした。
具体的には、このXでのリプライ中のReaderエフェクトのコード例を見て、弄って、それでようやく理解したのです。
https://x.com/fbrasisil/status/1945476793814925429

Kyoでは、以下のHaskell風の疑似コードに相当するものを実行すると、典型的なHaskellのエフェクトシステムが42を出力するのとは異なり、0を出力します。

@
modifyZero :: forall es a. Eff es a -> Eff es a
modifyZero = runReader 0

do
    x :: Int <- runReader 42 $ modifyZero $ ask
    print x
@

これは、Haskell（のエフェクトシステム）に慣れた人々にとってはかなり驚くべき挙動だと思います。
というのも、@modifyZero@関数における型引数@es@は一切の制約なしに多相化されており、そのリスト内に@Reader Int@が含まれているという知識を利用してその挙動を変更するのはparametricityを破っているからです。

Kyoでは、エフェクトのハンドル時におけるエフェクト（タグ）間の等価性判定を、型レベル計算ではなく、代わりにScalaにより提供される実行時型表現を一部利用することで、この動作を実現しています。
Haskellの言葉で言うと、すべてのエフェクトについて、暗黙的に提供される@Typeable (e :: Effect)@を利用してエフェクトのマッチングをしているようなものです。

しかし、この動作のおかげで、Kyoでは高階エフェクトを実現するためにHaskellの常識とは全く異なる方法を自然に取ることができました。
この方法では、エフェクトシステムが特別な高階エフェクトサポートを提供していなくても、形式的には一階エフェクトの形をとるようにして高階エフェクトをエンコードすることができます。
ここではそれを、**高階エフェクトの一階化埋め込み**という言葉で呼びたいと思います。
本ファイルのコードは、その巧妙なやり方を示すことを目的としています。

@pull@関数は、引数で渡されるmembershipを利用することで、parametricityを破らない形でこの動作を擬似的にエミュレートすることを可能にします。
そして、高階エフェクトのエンコーディングの際、membershipもオペレーションのデータ内部に保持するようにすることで、@pull@関数にリスト中に当該エフェクトが存在していることのエビデンスを伝達します。
この新規なテクニックにより、Kyoにおける高階エフェクトのハンドリング手法をHaskellでも実現できます。
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
--  * エフェクトシステム実装
-- ====================================================================================================

-- | エフェクトのカインド。
type Effect = Type -> Type

-- | Effモナド。
type Eff es = FreerT (Union es App) Identity

-------------------- ** オープンユニオン

-- | 汎用的なオープンユニオン。
data Union (xs :: [k]) (h :: k -> l -> Type) (a :: l) where
    Here :: h x a -> Union (x : xs) h a
    There :: Union xs h a -> Union (x : xs) h a

-- | オープンユニオン内の要素のメンバーシップ（エビデンス）。
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

-- | オープンユニオンをエフェクトリスト用に特殊化するためのヘルパー型。
newtype App f a = App {getApp :: f a}

-- | エフェクトリスト内のメンバーシップ。
type Member = Membership App :: Effect -> [Effect] -> Type

-------------------- ** エフェクトのハンドル

{- |
代数的エフェクトの用語における「ディープハンドラ」。
-}
interpret ::
    -- | 値ハンドラ
    (a -> Eff es b) ->
    -- | エフェクトハンドラ
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

-- | ハンドラに渡される継続において解釈が自動で再帰的にされないバージョンの@interpret@。代数的エフェクトの用語における「シャローハンドラ」。
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

-------------------- ** 雑多な操作

{- |
ここでの高階エフェクトの「一階化」の核を構成しているテクニックを提供する関数です。
多相化されたエフェクトリスト@es@の「下に埋もれている」エフェクト@e@を、membershipを使って「掘り起こし」てきて、
エフェクトリストの先頭にまで「引っ張って」きます。
@es@内には依然として（型レベルにおいては）@e@が残ったままになります（つまりてっぺんの@e@と重複した形になる）が、
値レベルでは何が起こるかというと、@es@内の@e@のスロットからはオペレーションがすべて「吸い取られてなくなり」、
一番上にすべて移動されます。
つまり、オペレーションをスロット間移動（コピーではなく）する操作であり、水をポンプで組み上げるようなものです。
-}
pull :: Member e es -> Eff es a -> Eff (e : es) a
pull i = transFreerT \u -> case project i u of
    Just e -> Here e
    Nothing -> There u

-- | エフェクトリスト@es@内に保持されているエフェクト@e@のオペレーションを書き換える。
rewrite :: Member e es -> (forall x. e x -> e x) -> Eff es a -> Eff es a
rewrite i f = transFreerT \u -> case project i u of
    Just e -> inject i $ App $ f $ getApp e
    Nothing -> u

-- | エフェクトリストを集合として拡張する。
raise :: Eff es a -> Eff (e : es) a
raise = transFreerT There

-------------------- ** エフェクト実行

-- | エフェクトを実行する。
perform :: (e :> es) => e a -> Eff es a
perform = send membership

-- | 高階エフェクトを実行する。
performH :: (e :> es) => e (Eff es a) -> Eff es a
performH op = performWith op id

-- | エフェクトを継続付きで実行する。
performWith :: (e :> es) => e a -> (a -> Eff es b) -> Eff es b
performWith = sendWith membership

-- | 指定されたメンバーシップのスロットにおいてエフェクトを実行する。
send :: Member e es -> e a -> Eff es a
send i op = sendWith i op pure

-- | 指定されたメンバーシップのスロットにおいて、エフェクトを継続付きで実行する。
sendWith :: Member e es -> e a -> (a -> Eff es b) -> Eff es b
sendWith i op k = FreerT $ Identity $ Freer (inject i $ App op) (tsingleton k)

-------------------- ** Effモナド除去

-- | 最後に残ったエフェクトをモナドとして扱い、そこに落とすことで、Effモナドを除去する。
runEff :: (Monad m) => Eff '[m] a -> m a
runEff (FreerT m) = case runIdentity m of
    Pure x -> pure x
    Freer (Here (App n)) q -> n >>= runEff . qApp q
    Freer (There u) _ -> case u of {}

-- | エフェクトがすべてハンドルされた状況下で、純粋な結果値を取り出す。
runPure :: Eff '[] a -> a
runPure (FreerT m) = case runIdentity m of
    Pure x -> x
    Freer u _ -> case u of {}

-- ====================================================================================================
--  * 各種エフェクト定義
-- ====================================================================================================

-------------------- ** Readerエフェクト

data Reader r :: Effect where
    Ask :: Reader r r
    Local :: Member (Reader r) es -> (r -> r) -> Eff es a -> Reader r (Eff es a)

runReader :: r -> Eff (Reader r : es) a -> Eff es a
runReader r = interpret pure \case
    Ask -> \k -> k r
    Local i f m -> \k -> k $ runReader (f r) (pull i m)

local :: (Reader r :> es) => (r -> r) -> Eff es a -> Eff es a
local f m = performH $ Local membership f m

-------------------- ** Coroutineエフェクト

data Yield i o :: Effect where
    Yield :: i -> Yield i o o

data Status f i o a = Done a | Continue i (o -> f (Status f i o a))

runCoroutine :: Eff (Yield i o : es) a -> Eff es (Status (Eff es) i o a)
runCoroutine = interpret (pure . Done) \(Yield i) k -> pure $ Continue i k

-------------------- ** 例外エフェクト

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

-------------------- ** Writerエフェクト

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

-------------------- ** 非決定論計算エフェクト

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
--  * テスト
-- ====================================================================================================

-------------------- ** 雑多な実行例

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

-------------------- ** [SemanticsZoo](https://github.com/lexi-lambda/eff/blob/master/notes/semantics-zoo.md)によるセマンティクス検査問題例

-- 作業中
