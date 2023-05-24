{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}

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
import Text.Show
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
strAppend (L u) (L v) = L $ u ++ v
strAppend c (L lst) = L $ c : lst
strAppend c a = L [c, a]

showInfo :: AssociativePrecision -> Bool -> a -> String -> String
showInfo ap rp x s = "(" ++ show ap ++ ") (" ++ show rp ++ ") (?) (" ++ s ++ ")"

class ShowP a where
    devsTree :: AssociativePrecision -> Bool -> a -> String -> StringTree
    devsTree ap rp x s = strAppend (V $ "devsTree " ++ showInfo ap rp x s) $ devTree x

    devTree :: a -> StringTree
    devTree x = strAppend (V "devTree : (?)") $ devsTree uselessAP uselessRP x ""

    --- showsPAPrec ap rp x r ++ s === showsPAPrec ap x (r ++ s)
    showsPAPrec :: AssociativePrecision -> Bool -> a -> ShowS
    showsPAPrec _ _ x s = (showP x) ++ s
    
    showP :: a -> String
    showP x = showsPAPrec uselessAP uselessRP x ""

instance ShowP (Par1 p) where
    devTree x = V "Par1 : (?)"
    showP (Par1 p) = "NID"

instance ShowP (f p) => ShowP (Rec1 f p) where
    devTree x = V "Rec1 : (?)"
    showP (Rec1 a) = "NID"

instance ShowP (U1 p) where
    devTree x = V "U1 : (?)"
    showP U1 = ""

-- TODO
-- нужно здесь разобраться, чтобы не всегда нужен был контекст Show
-- CEs 1 почему-то попадет сюда сразу, без прохода через C1...
instance Show c => ShowP (K1 i c p) where
    devTree x = V "K1 : (?)"
    showP k1@(K1 e) = show e

-- in record, поэтому размышления о правильности расстановки опущены
instance (ShowP (a p), ShowP (b p), ShowP (c p), ShowP ((:*:) b c p)) => ShowP ((:*:) a ((:*:) b c) p) where
    devsTree ap rp x@(a :*: b) s = 
        strAppend (V $ "a * b * c " ++ showInfo ap rp x s) $
            R (devsTree uselessAP uselessRP a s) (devsTree uselessAP uselessRP b s)
    -- so dirty hack
    showsPAPrec _ _ (a :*: b) s =
        (showsPAPrec uselessAP uselessRP a s) ++ (showsPAPrec uselessAP uselessRP b s)

instance (ShowP (a p), ShowP (b p)) => ShowP ((:*:) a b p) where
    devsTree ap rp x@(a :*: b) s = 
        strAppend (V $ "a * b " ++ showInfo ap rp x s) $
            R (devsTree ap (checkIsRightPosed ap False) a s) (devTree b)
    -- so dirty hack
    -- а вот сюда мы можем прийти из Infix a p
    showsPAPrec ap _ (a :*: b) s = 
        (showsPAPrec ap (checkIsRightPosed ap False) a s) ++ showP b -- TODO: WHERE IS MY COMMA

instance (Constructor c, ShowP (a p), ShowP (b p), ShowP (((:*:) a b p))) => ShowP (C1 c ((:*:) a b) p) where
    devsTree ap rp c1@(M1 a) s =
        strAppend (V $ "C1 with a * b " ++ showInfo ap rp c1 s) (
            devsTree (gF2AP . conFixity $ c1) uselessRP a $
                case conFixity c1 of
                    Prefix -> if conIsRecord c1
                              then ", "
                              else " "
                    Infix _ _ -> " ")
    showsPAPrec ap rp c1@(M1 a) =
        let
            cn = conName c1
            cf = conFixity c1
            myAP = gF2AP cf
            next = showsPAPrec myAP uselessRP a
        in
        case cf of
            Prefix -> if conIsRecord c1
                      then showString $ cn ++ " {" ++ (next ", ") ++ "}"
                      else showString $ cn ++ " " ++ (next " ")
            Infix _ _ -> 
                showParen (shouldShowParen ap rp myAP) .
                    showString . next $ " " ++ cn ++ " "

instance (Constructor c, ShowP (U1 p)) => ShowP (C1 c U1 p) where
    devTree x = V $ "C1 with U1 (?)"
    -- only Prefix
    showP c1@(M1 a) = conName c1

instance (Constructor c, ShowP (f p)) => ShowP (C1 c f p) where
    devTree c1@(M1 a) = 
        strAppend (V "C1 with anothers (?)") $ devTree a
    -- only Prefix
    showP c1@(M1 a) =
        let
            cn = conName c1
            next = showP a
        in if conIsRecord c1
           then cn ++ " {" ++ next ++ "}"
           else cn ++ " " ++ next

instance ShowP (f p) => ShowP (D1 c f p) where
    devTree d1@(M1 a) = 
        strAppend (V $ "D1 (?)") $ devTree a
    showP d1@(M1 a) = showP a

instance (Selector c, ShowP (f p)) => ShowP (S1 c f p) where
    devsTree ap rp s1@(M1 a) s = 
        strAppend (V $ "S1 " ++ showInfo ap rp s1 s) $ devTree a
    showsPAPrec _ _ s1@(M1 a) s = (if length sn > 0 then sn ++ " = " else "") ++ next ++ s
        where sn = selName s1
              next = showP a

instance ShowP (f p) => ShowP (M1 i c f p) where
    devTree m1@(M1 a) = 
        strAppend (V "M1 (?)") $ devTree a
    showP m1@(M1 a) = showP a

instance (ShowP (l p), ShowP (r p)) => ShowP ((:+:) l r p) where
    devTree x = case x of
        L1 a -> strAppend (V "L1 (?)") $ devTree a
        R1 a -> strAppend (V "R1 (?)") $ devTree a
    showP x = case x of
        L1 a -> showP a
        R1 a -> showP a

data NatMy = Zs |
             Ss NatMy |
             Ps {} |
             Qs {es :: NatMy} |
             CEs Int |
             NatMy :*- NatMy |
             Ws {ws1 :: Int, ws2 :: Int, ws3 :: Int} deriving (Show, Generic)

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

instance Show a => ShowP (TestData a) where
    devTree = devTree . from1
    showP = showP . from1

someFunc = do
    --putStrLn "Hello world!"
    --let test1 = Zs :: NatMy
    --let test2 = CEs 3 :: NatMy
    --let test3 = CEs 2 :*- Zs :: NatMy
    let test4 = Ws 4 3 7 :: NatMy
    --let test5 = Ps :: NatMy
    --let test6 = Qs test2 :: NatMy
    --putStrLn . showP $ test1
    --putStrLn . showP $ test2
    --putStrLn . showP $ test3
    putStrLn . showP $ test4
    --putStrLn . showP $ test5
    --putStrLn . showP $ test6
    --putStrLn "-------------------------"
    print . devTree $ test4
    --print . fromM1 . from $ test4