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
    StringTree,
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

data StringTree = V String | L [StringTree] | R StringTree StringTree deriving Show

strAppend :: StringTree -> StringTree -> StringTree
strAppend c (L lst) = L $ c : lst
strAppend c a = L [c, a]

showInfo :: AssociativePrecision -> Bool -> a -> String -> String
showInfo ap rp x s = "(" ++ show ap ++ ") (" ++ show rp ++ ") (?) (" ++ s ++ ")"

class ShowP a where
    devsTree :: AssociativePrecision -> Bool -> a -> String -> StringTree
    devsTree ap rp x s = strAppend (V $ "devsTree " ++ showInfo ap rp x s) $ devTree x

    devTree :: a -> StringTree
    devTree x = strAppend (V "devTree : (?)") $ devsTree uselessAP uselessRP x ""

    --- showsPAPrec ap rp x r ++ s === showsPAPrec ap rp x (r ++ s)
    showsPAPrec :: AssociativePrecision -> Bool -> a -> ShowS
    showsPAPrec _ _ x s = trace "default shows " $ (showP x) ++ s
    
    showP :: a -> String
    showP x = trace "default showP" $ showsPAPrec uselessAP uselessRP x ""

instance ShowP Int where
    showP = show

class ShowP a => ShowProd a where
    showDevTree :: AssociativePrecision -> Bool -> a -> [StringTree]
    showDevTree ap rp x = [devsTree ap rp x "-"]

    showProd :: AssociativePrecision -> Bool -> a -> [ShowS]
    showProd ap rp x = trace ("showProd default " ++ show ap ++ " " ++ show rp) $ [showsPAPrec ap rp x]

instance ShowP (Par1 p) where
    devTree x = V "Par1 : (?)"
    showP (Par1 p) = trace "Par1" $ "NID"

instance ShowP (f p) => ShowP (Rec1 f p) where
    devTree x = V "Rec1 : (?)"
    showP (Rec1 a) = trace "Rec1" $ "NID"

instance ShowP (U1 p) where
    devTree x = V "U1 : (?)"
    showP U1 = trace "U1" $ ""

-- TODO
-- нужно здесь разобраться, чтобы не всегда нужен был контекст Show
-- CEs 1 почему-то попадет сюда сразу, без прохода через C1...
instance ShowP c => ShowP (Rec0 c p) where
    devTree x = V "Rec0 : (?)"
    showsPAPrec ap rp k1@(K1 e) = trace "Rec0" . showsPAPrec ap rp e

instance Show c => ShowP (K1 i c p) where
    devTree x = V "K1 : (?)"
    showsPAPrec ap rp k1@(K1 e) = trace "K1" . showString $ show e

-- dummy
instance (ShowP (a p), ShowP (b p)) => ShowP ((:*:) a b p) where
    devTree (a :*: b) = V "not implemented"
    showP (a :*: b) = trace ":*: WARNING" $ showP a ++ showP b

instance (ShowProd (a p), ShowProd (b p)) => ShowProd ((:*:) a b p) where
    showDevTree ap _ (a :*: b) = 
        let
            rp = checkIsRightPosed ap False
        in
            showDevTree ap rp a ++ showDevTree ap (not rp) b

    showProd ap _ (a :*: b) =
        let
            rp = checkIsRightPosed ap False
        in
            showProd ap rp a ++ showProd ap (not rp) b

instance (Constructor c, ShowP (((:*:) a b p)), ShowProd (a p), ShowProd (b p)) => ShowP (C1 c ((:*:) a b) p) where
    devsTree ap rp c1@(M1 a) s = strAppend (V $ "C1 with prod " ++ showInfo ap rp a s) .
        foldr (\u v -> strAppend (L [u]) v) (L []) $
            showDevTree (gF2AP . conFixity $ c1) uselessRP a
    showsPAPrec ap rp c1@(M1 a) = trace ("C1 PAP " ++ show ap ++ " " ++ show rp) $
        let
            cn = conName c1
            cf = conFixity c1
            myAP = gF2AP cf
            next = showProd myAP uselessRP a
            conv ast = foldr1 (\u v -> showString (u ast) . v) next
        in
        case cf of
            Prefix -> if conIsRecord c1
                      then showString $ cn ++ " {" ++ conv ", " "}"
                      else showString (cn ++ " ") . conv " "
            Infix _ _ -> 
                showParen (shouldShowParen ap rp myAP) . conv $ " " ++ cn ++ " "

instance (Constructor c, ShowP (U1 p)) => ShowP (C1 c U1 p) where
    devTree x = V $ "C1 with U1 (?)"
    -- only Prefix
    showP c1@(M1 a) = trace "C1 U1" $ conName c1

instance (Constructor c, ShowP (f p)) => ShowP (C1 c f p) where
    devTree c1@(M1 a) = 
        strAppend (V "C1 with anothers (?)") $ devTree a
    -- only Prefix
    showP c1@(M1 a) = trace "C1 default" $ 
        let
            cn = conName c1
            next = showP a
        in if conIsRecord c1
           then cn ++ " {" ++ next ++ "}"
           else cn ++ " " ++ next

instance ShowP (f p) => ShowP (D1 c f p) where
    devTree d1@(M1 a) = 
        strAppend (V $ "D1 (?)") $ devTree a
    showP d1@(M1 a) = trace "D1" $ showP a

instance (Selector c, ShowP (f p)) => ShowP (S1 c f p) where
    devsTree ap rp s1@(M1 a) s = 
        strAppend (V $ "S1 " ++ showInfo ap rp s1 s) $ devTree a
    showsPAPrec ap rp s1@(M1 a) = trace "S1" $ showString (if length sn > 0 then sn ++ " = " else "") . next
        where sn = selName s1
              next = showsPAPrec ap rp a

instance (Selector c, ShowP (f p)) => ShowProd (S1 c f p) where

instance ShowP (f p) => ShowP (M1 i c f p) where
    devTree m1@(M1 a) = 
        strAppend (V "M1 (?)") $ devTree a
    showP m1@(M1 a) = trace "M1" $ showP a

instance (ShowP (l p), ShowP (r p)) => ShowP ((:+:) l r p) where
    devTree x = case x of
        L1 a -> strAppend (V "L1 (?)") $ devTree a
        R1 a -> strAppend (V "R1 (?)") $ devTree a
    showP x = case x of
        L1 a -> trace "L1" $ showP a
        R1 a -> trace "R1" $ showP a

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
    devTree = devTree . from
    showP = showP . from

instance ShowP ExprPrim where
    devTree = devTree . from
    showP = showP . from

instance Show a => ShowP (TestData a) where
    devTree = devTree . from1
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

someFunc = do
    print . showP $ testSet2 !! 0
    