{-# LANGUAGE DeriveGeneric #-}

import GHC.Generics
import Show
import Read

data NatMy = Zs |
             Ss NatMy |
             Ps {} |
             Qs {es :: NatMy} |
             CEs Int |
             NatMy :*- NatMy |
             Hs Int NatMy Int |
             Ws {ws1 :: Int, ws2 :: Int, ws3 :: Int, ws4 :: Int, ws5 :: Int} deriving (Show, Generic, Eq)

data ExprPrim = Cc Int |
                ExprPrim :++- ExprPrim |
                ExprPrim :**- ExprPrim |
                ExprPrim :^^- ExprPrim |
                ExprPrim :--- ExprPrim |
                ExprPrim ://- ExprPrim |
                ExprPrim :%%- ExprPrim deriving (Show, Generic, Eq)

infixl 3 :++-
infixr 3 :**-
infixr 9 :^^-
infixr 9 :---
infix 3 ://-
infix 7 :%%-

data TestData a = Z |
                  S (TestData a) |
                  P {} |
                  Q {e :: (TestData a)} |
                  CE a |
                  (TestData a) :* (TestData a) |
                  H Int a (TestData a) |
                  W {w1 :: a, w2 :: a, w3 :: a} deriving (Show, Generic1, Eq)

data Expr a = C a |
              (Expr a) :++: (Expr a) |
              (Expr a) :**: (Expr a) |
              (Expr a) :^^: (Expr a) |
              (Expr a) :--: (Expr a) |
              (Expr a) ://: (Expr a) |
              (Expr a) :%%: (Expr a) deriving (Show, Generic1, Eq)

infixl 3 :++:
infixr 3 :**:
infixl 9 :^^:
infixr 9 :--:
infix 3 ://:
infix 7 :%%:

instance ShowP NatMy where
    showsPAPrec ap rp = showsPAPrec ap rp . from

instance ReadP NatMy where
    readsPAPrec ap rp = fmap (\(t, s) -> (to t, s)) . readsPAPrec ap rp

instance ShowP ExprPrim where
    showsPAPrec ap rp = showsPAPrec ap rp . from

instance ReadP ExprPrim where
    readsPAPrec ap rp = fmap (\(t, s) -> (to t, s)) . readsPAPrec ap rp

instance ShowP a => ShowP (TestData a) where
    showsPAPrec ap rp = showsPAPrec ap rp . from1

instance ReadP a => ReadP (TestData a) where
    readsPAPrec ap rp = fmap (\(t, s) -> (to1 t, s)) . readsPAPrec ap rp

instance ShowP a => ShowP (Expr a) where
    showsPAPrec ap rp = showsPAPrec ap rp . from1

instance ReadP a => ReadP (Expr a) where
    readsPAPrec ap rp = fmap (\(t, s) -> (to1 t, s)) . readsPAPrec ap rp

testSet1 :: [NatMy]
testSet1 = [
    Zs,
    CEs 3,
    CEs 2 :*- Zs,
    Ws 4 3 7 1 9,
    Ps,
    Hs 12 Zs 13]

testSet2 :: [ExprPrim]
testSet2 = [
    Cc 1 :++- Cc 2 :++- Cc 3 :^^- Cc 4 :%%- Cc 5 :^^- Cc 6 :^^- Cc 7,
    Cc 1 :++- Cc 2 :++- Cc 3 :++- Cc 4 :++- Cc 5 :++- Cc 6 :++- Cc 7]

testSet3 :: [TestData NatMy]
testSet3 = [
    Z,
    CE Ps,
    CE (CEs 14) :* CE (Hs 10 (CEs 19) 30),
    W (CEs 1) Zs Ps,
    P,
    H 14 Zs (CE (CEs 17))]

testSet4 :: [Expr (TestData Int)]
testSet4 = [
    -- different associativity, same precision
    --- 3
    C Z :++: (C Z :**: C Z),
    (C Z :++: C Z) :**: C Z,
    (C Z ://: C Z) :++: C Z,
    C Z ://: (C Z :++: C Z),
    --- 9
    C Z :--: (C Z :^^: C Z),
    (C Z :--: C Z) :^^: C Z,
    -- different precision
    --- same associativity
    C Z :++: C Z :^^: C Z,
    C Z :**: C Z :--: C Z,
    C Z ://: C Z :%%: C Z,
    --- different associativity
    C Z :++: C Z :--: C Z,
    C Z :++: C Z :%%: C Z,
    C Z :**: C Z :^^: C Z,
    C Z :**: C Z :%%: C Z,
    C Z :^^: C Z ://: C Z,
    C Z :^^: C Z :%%: C Z]

testSet5 :: [Expr (TestData NatMy)]
testSet5 = [
    C Z :++: C Z :++: C Z :++: C Z :++: C Z :++: C Z,
    C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z :**: C Z,
    C Z :^^: C Z :^^: C Z :^^: C Z :^^: C Z :^^: C Z :^^: C Z :^^: C Z,
    C Z :--: C Z :--: C Z :--: C Z :--: C Z :--: C Z :--: C Z :--: C Z :--: C Z :--: C Z]

myAssert :: Bool -> String -> String -> String
myAssert True = const
myAssert False = flip const

doTest :: String -> Bool -> String
doTest ifPassed res = myAssert res ifPassed undefined

doShowTest :: (Show a, ShowP a) => Bool -> String -> [a] -> String
doShowTest False name ts = doTest name $ all (\t -> showP t == show t) ts
doShowTest True name ts = doTest name $ all (\t -> length(showP t) < length(show t)) ts

doReadTest :: (ReadP a, ShowP a, Eq a) => String -> [a] -> String
doReadTest name ts = doTest name $ all (\t -> (t, "") `elem` readP (showP t)) ts

main :: IO ()
main = do
    putStrLn ""
    putStrLn . doShowTest False "Test #1 (ShowP *) passed" $ testSet1
    putStrLn . doShowTest True "Test #2 (ShowP > Show *) passed" $ testSet2
    putStrLn . doShowTest False "Test #3 (ShowP * -> *) passed" $ testSet3
    putStrLn . doShowTest False "Test #4 (ShowP >= Show) passed" $ testSet4
    putStrLn . doShowTest True "Test #5 (ShowP > Show) passed" $ testSet5

    putStrLn . doReadTest "Test #1 (ReadP *) passed" $ testSet1
    putStrLn . doReadTest "Test #2 (ReadP > Read *) passed" $ testSet2
    putStrLn . doReadTest "Test #3 (ReadP * -> *) passed" $ testSet3
    putStrLn . doReadTest "Test #4 (ReadP >= Read) passed" $ testSet4
    putStrLn . doReadTest "Test #5 (ReadP > Read) passed" $ testSet5

