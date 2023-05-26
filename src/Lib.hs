{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module Lib (
    AssociativePrecision,
    ShowP,
    someFunc,
    TestData,
    NatMy,
    Expr
) where

import GHC.Generics
import Debug.Trace

data AssociativePrecision = InfixAP Int | InfixlAP Int | InfixrAP Int deriving Show

prefixAP :: AssociativePrecision
prefixAP = InfixAP 10

uselessAP :: AssociativePrecision
uselessAP = InfixAP 0

uselessRP :: Bool
uselessRP = True

gF2AP :: Fixity -> AssociativePrecision
gF2AP Prefix = prefixAP
gF2AP (Infix LeftAssociative n) = InfixlAP n
gF2AP (Infix RightAssociative n) = InfixrAP n
gF2AP (Infix NotAssociative n) = InfixAP n

getPrecision :: AssociativePrecision -> Int
getPrecision (InfixAP n) = n
getPrecision (InfixlAP n) = n
getPrecision (InfixrAP n) = n

checkConflict :: AssociativePrecision -> AssociativePrecision -> Bool
checkConflict (InfixAP _) _ = True
checkConflict _ (InfixAP _) = True
checkConflict (InfixlAP _) (InfixrAP _) = True
checkConflict (InfixrAP _) (InfixlAP _) = True
checkConflict _ _ = False

shouldShowParen :: AssociativePrecision -> Bool -> AssociativePrecision -> Bool
shouldShowParen lastAP isRightPosed curAP =
    getPrecision curAP <= getPrecision lastAP &&
    (getPrecision curAP < getPrecision lastAP ||
    checkConflict lastAP curAP ||
    not isRightPosed)

-- 2 - это левый или правый аргумент
checkIsRightPosed :: AssociativePrecision -> Bool -> Bool
checkIsRightPosed (InfixlAP _) False = True
checkIsRightPosed (InfixrAP _) True = True
-- для Infix нет разницы, он побуждает конфликт
checkIsRightPosed _ _ = False

class ShowP a where
    --- showsPAPrec ap rp x r ++ s === showsPAPrec ap rp x (r ++ s)
    showsPAPrec :: AssociativePrecision -> Bool -> a -> ShowS
    showsPAPrec _ _ x s = (showP x) ++ s
    
    showP :: a -> String
    showP x = showsPAPrec uselessAP uselessRP x ""

instance ShowP Int where
    showP = show

class ShowP a => ShowProd a where
    showProd :: AssociativePrecision -> Bool -> a -> [ShowS]
    showProd ap rp x = [showsPAPrec ap rp x]

instance ShowP p => ShowP (Par1 p) where
    showsPAPrec ap rp (Par1 p) = showsPAPrec ap rp p

instance ShowP (f p) => ShowP (Rec1 f p) where
    showsPAPrec ap rp (Rec1 a) = showsPAPrec ap rp a

instance ShowP (U1 p) where
    showP U1 = ""

instance ShowP c => ShowP (Rec0 c p) where
    showsPAPrec ap rp r0@(K1 e) = showsPAPrec ap rp e

-- dummy
instance (ShowP (a p), ShowP (b p)) => ShowP ((:*:) a b p) where
    showP (a :*: b) = undefined

instance (ShowProd (a p), ShowProd (b p)) => ShowProd ((:*:) a b p) where
    showProd ap _ (a :*: b) =
        let
            rp = checkIsRightPosed ap False
        in
            showProd ap rp a ++ showProd ap (not rp) b

instance (Constructor c, ShowP ((:*:) a b p), ShowProd (a p), ShowProd (b p)) => ShowP (C1 c ((:*:) a b) p) where
    showsPAPrec ap rp c1@(M1 a) =
        let
            cn :: String
            cn = conName c1
            
            cf :: Fixity
            cf = conFixity c1
            
            myAP :: AssociativePrecision
            myAP = gF2AP cf
            
            next :: [ShowS]
            next = showProd myAP uselessRP a
            
            conv :: String -> ShowS
            conv ast = foldr1 (\u v -> showString (u ast) . v) next
            
            variants :: Fixity -> ShowS
            variants Prefix = if conIsRecord c1
                              then showString $ cn ++ " {" ++ (conv ", ") "}"
                              else showString (cn ++ " ") . conv " "
            variants _ = conv $ " " ++ cn ++ " "
        in
            showParen (shouldShowParen ap rp myAP) $ variants cf

instance (Constructor c, ShowP (U1 p)) => ShowP (C1 c U1 p) where
    -- only Prefix
    showP c1@(M1 a) = conName c1

instance (Constructor c, ShowP (f p)) => ShowP (C1 c f p) where
    -- only Prefix
    showsPAPrec ap rp c1@(M1 a) =  
        let
            cn = conName c1
            next = showsPAPrec prefixAP uselessRP a
        in
            showParen (shouldShowParen ap rp . gF2AP . conFixity $ c1) $ showString (
                if conIsRecord c1
                then cn ++ " {" ++ next "}"
                else cn ++ " " ++ next "")

instance ShowP (f p) => ShowP (D1 c f p) where
    showsPAPrec ap rp d1@(M1 a) = showsPAPrec ap rp a

instance (Selector c, ShowP (f p)) => ShowP (S1 c f p) where 
    showsPAPrec ap rp s1@(M1 a) =
            if length sn > 0
            then showString (sn ++ " = ") . showsPAPrec uselessAP uselessRP a
            else showString "" . showsPAPrec ap rp a
        where sn = selName s1

instance (Selector c, ShowP (f p)) => ShowProd (S1 c f p) where

instance ShowP (f p) => ShowP (M1 i c f p) where
    showsPAPrec ap rp m1@(M1 a) = showsPAPrec ap rp a

instance (ShowP (l p), ShowP (r p)) => ShowP ((:+:) l r p) where
    showsPAPrec ap rp x = 
        case x of
            L1 a -> showsPAPrec ap rp a
            R1 a -> showsPAPrec ap rp a

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

someFunc = do
    print . all (\t -> showP t == show t) $ testSet1
    print . all (\t -> length (showP t) < length (show t)) $ testSet2
    print . all (\t -> showP t == show t) $ testSet3
    
