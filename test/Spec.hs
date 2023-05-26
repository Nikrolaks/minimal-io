{-# LANGUAGE DeriveGeneric #-}

import GHC.Generics
import Show

data NatMy = Zs |
             Ss NatMy |
             Ps {} |
             Qs {es :: NatMy} |
             CEs Int |
             NatMy :*- NatMy |
             Hs Int NatMy Int |
             Ws {ws1 :: Int, ws2 :: Int, ws3 :: Int, ws4 :: Int, ws5 :: Int} deriving (Show, Generic)

data ExprPrim = Cc Int |
                ExprPrim :++- ExprPrim |
                ExprPrim :**- ExprPrim |
                ExprPrim :^^- ExprPrim |
                ExprPrim :--- ExprPrim |
                ExprPrim ://- ExprPrim |
                ExprPrim :%%- ExprPrim deriving (Show, Generic)

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
                  W {w1 :: a, w2 :: a, w3 :: a} deriving (Show, Generic1)

data Expr a = C a |
              (Expr a) :++: (Expr a) |
              (Expr a) :**: (Expr a) |
              (Expr a) :^^: (Expr a) |
              (Expr a) :--: (Expr a) |
              (Expr a) ://: (Expr a) |
              (Expr a) :%%: (Expr a) deriving (Show, Generic1)

infixl 3 :++:
infixr 3 :**:
infixr 9 :^^:
infixr 9 :--:
infix 3 ://:
infix 7 :%%:

instance ShowP NatMy where
    showsPAPrec ap rp = showsPAPrec ap rp . from
    showP = showP . from

instance ShowP ExprPrim where
    showsPAPrec ap rp = showsPAPrec ap rp . from
    showP = showP . from

instance ShowP a => ShowP (TestData a) where
    showsPAPrec ap rp = showsPAPrec ap rp . from1
    showP = showP . from1

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
    Cc 1 :++- Cc 2 :++- Cc 3 :++- Cc 4 :++- Cc 5 :++- Cc 6 :++- Cc 7
    ]

testSet3 :: [TestData NatMy]
testSet3 = [
    Z,
    CE Ps,
    CE (CEs 14) :* CE (Hs 10 (CEs 19) 30),
    W (CEs 1) Zs Ps,
    P,
    H 14 Zs (CE (CEs 17))]

myAssert :: Bool -> String -> String -> String
myAssert True = const
myAssert False = flip const

doTest :: String -> String -> Bool -> String
doTest ifPassed ifCrushed res = myAssert res ifPassed ifCrushed

main :: IO ()
main = do
    putStrLn ""
    putStrLn . doTest "Test #1 passed" undefined $ all (\t -> showP t == show t) testSet1
    putStrLn . doTest "Test #2 passed" undefined $ all (\t -> length (showP t) < length (show t)) testSet2
    putStrLn . doTest "Test #3 passed" undefined $ all (\t -> showP t == show t) testSet3
    
