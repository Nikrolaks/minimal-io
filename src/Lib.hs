{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Lib (
    TestData,
    StringTree,
    AssociativePrecision,
    ShowP,
    someFunc
) where

import GHC.Generics
import Text.Show

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

data StringTree = L String |
                  Ch String StringTree |
                  R String StringTree StringTree deriving Show

showInfo :: String -> AssociativePrecision -> Bool -> a -> String
showInfo s ap rp _ = "[" ++ show ap ++ " " ++ show rp ++ "] " ++ s

class ShowP a where
    devTree :: AssociativePrecision -> Bool -> a -> StringTree
    devTree ap rp = L . showInfo "dummy" ap rp

    --- showsPAPrec ap rp x r ++ s === showsPAPrec ap x (r ++ s)
    showsPAPrec :: AssociativePrecision -> Bool -> a -> ShowS
    showsPAPrec _ _ x s = showP x ++ s
    
    showP :: a -> String
    showP x = showsPAPrec uselessAP uselessRP x ""

instance ShowP (Par1 p) where
    devTree ap rp = L . showInfo "Par1" ap rp
    showsPAPrec _ _ (Par1 p) = showString "not implemented"

instance ShowP (f p) => ShowP (Rec1 f p) where
    devTree ap rp = L . showInfo "Rec1" ap rp
    showsPAPrec _ _ (Rec1 a) = showString "not implemented"

instance ShowP (U1 p) where
    devTree ap rp = L . showInfo "U1" ap rp
    showP U1 = ""

-- TODO
-- нужно здесь разобраться, чтобы не всегда нужен был контекст Show
-- CEs 1 почему-то попадет сюда сразу, без прохода через C1...
instance Show c => ShowP (K1 i c p) where
    devTree ap rp = L . showInfo "K1" ap rp
    showP k1@(K1 e) = show e

-- in record, поэтому размышления о правильности расстановки опущены
instance (ShowP (a p), ShowP (b p), ShowP (c p), ShowP ((:*:) b c p)) => ShowP ((:*:) a ((:*:) b c) p) where
    devTree ap rp x@(a :*: b) = R (showInfo ":*:" ap rp x)
        (devTree uselessAP uselessRP a) (devTree uselessAP uselessRP b)
    -- so dirty hack
    showsPAPrec _ _ (a :*: b) s =
        showP a ++ s ++ showsPAPrec uselessAP uselessRP b s

instance (ShowP (a p), ShowP (b p)) => ShowP ((:*:) a b p) where
    devTree ap rp x@(a :*: b) = R (showInfo ":*:" ap rp x)
        (devTree ap (checkIsRightPosed ap False) a)
        (devTree ap (checkIsRightPosed ap True) b)
    -- so dirty hack
    -- а вот сюда мы можем прийти из Infix a p
    showsPAPrec ap _ (a :*: b) s = 
        showsPAPrec ap (checkIsRightPosed ap False) a "" ++ 
            s ++ 
            showsPAPrec ap (checkIsRightPosed ap True) b ""

instance (Constructor c, ShowP (a p), ShowP (b p), ShowP (((:*:) a b p))) => ShowP (C1 c ((:*:) a b) p) where
    devTree ap rp c1@(M1 a) =
        Ch (showInfo ("C1" ++ (show $ shouldShowParen ap rp (gF2AP . conFixity $ c1))) ap rp c1) $
            devTree (gF2AP . conFixity $ c1) uselessRP a
    showsPAPrec ap rp c1@(M1 a) =
        let
            cn = conName c1
            cf = conFixity c1
            myAP = gF2AP cf
            next = showsPAPrec myAP uselessRP a
        in
        case cf of
            -- record 
            Prefix -> showString $ cn ++ " {" ++ next ", " ++ "}"
            infixity -> 
                showParen (shouldShowParen ap rp myAP) .
                    showString . next $ " " ++ cn ++ " "

instance (Constructor c, ShowP (U1 p)) => ShowP (C1 c U1 p) where
    devTree ap rp = L . showInfo "C1" ap rp
    -- only Prefix
    showP c1@(M1 a) = conName c1

instance (Constructor c, ShowP (f p)) => ShowP (C1 c f p) where
    devTree ap rp c1@(M1 a) = Ch (showInfo "C1" ap rp c1) $ devTree uselessAP uselessRP a
    -- only Prefix
    showP c1@(M1 a) =
        let
            cn = conName c1
            next = showP a
        in if conIsRecord c1
           then cn ++ " {" ++ next ++ "}"
           else cn ++ " " ++ next

instance ShowP (f p) => ShowP (D1 c f p) where
    devTree ap rp d1@(M1 a) = Ch (showInfo "D1" ap rp d1) $ devTree uselessAP uselessRP a
    showP d1@(M1 a) = showP a

instance (Selector c, ShowP (f p)) => ShowP (S1 c f p) where
    devTree ap rp s1@(M1 a) = Ch (showInfo "S1" ap rp s1) $ devTree uselessAP uselessRP a
    showP s1@(M1 a) | length sn > 0 = sn ++ " = " ++ next
                    | otherwise = next
        where sn = selName s1
              next = showP a

instance ShowP (f p) => ShowP (M1 i c f p) where
    devTree ap rp m1@(M1 a) = Ch (showInfo "M1" ap rp m1) $ devTree uselessAP uselessRP a
    showP m1@(M1 a) = showP a

instance (ShowP (l p), ShowP (r p)) => ShowP ((:+:) l r p) where
    devTree ap rp x = case x of
        L1 a -> Ch (showInfo "L1" ap rp x) $ devTree uselessAP uselessRP a
        R1 a -> Ch (showInfo "R1" ap rp x) $ devTree uselessAP uselessRP a
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
    devTree ap rp x = devTree ap rp $ from x
    showP = showP . from

instance Show a => ShowP (TestData a) where
    devTree ap rp x = devTree ap rp $ from1 x
    showP = showP . from1

someFunc = do
    --putStrLn "Hello world!"
    let test1 = Zs :: NatMy
    let test2 = CEs 3 :: NatMy
    let test3 = CEs 2 :*- Zs :: NatMy
    let test4 = Ws 4 3 7 :: NatMy
    let test5 = Ps :: NatMy
    let test6 = Qs test2 :: NatMy
    putStrLn . showP $ test1
    putStrLn . showP $ test2
    putStrLn . showP $ test3
    putStrLn . showP $ test4
    putStrLn . showP $ test5
    putStrLn . showP $ test6
    --print . fromM1 . from $ test4