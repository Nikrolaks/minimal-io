{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Read (
    AssociativePrecision,
    ReadP,
    someFunc2
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

shouldParen :: AssociativePrecision -> Bool -> AssociativePrecision -> Bool
shouldParen lastAP isRightPosed curAP =
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

class ReadP a where
    readsPAPrec :: AssociativePrecision -> Bool -> a -> ReadS a

class ReadP a => ReadProd a where
    readProd :: AssociativePrecision -> Bool -> String -> a -> ReadS a
    readProd ap rp d = readsPAPrec ap rp

instance ReadP Int where
    readsPAPrec ap rp _ = readsPrec (getPrecision ap)

instance ReadP p => ReadP (Par1 p) where
    readsPAPrec ap rp _ s = [(Par1 x, t) | (x, t) <- readsPAPrec ap rp (undefined :: p) s]

instance ReadP (f p) => ReadP (Rec1 f p) where
    readsPAPrec ap rp _ s = [(Rec1 a, t) | (a, t) <- readsPAPrec ap rp (undefined :: f p) s]

instance ReadP (U1 p) where
    readsPAPrec _ _ _ s = [(U1, s)]

instance ReadP c => ReadP (Rec0 c p) where
    readsPAPrec ap rp _ s = [(K1 e, t) | (e, t) <- readsPAPrec ap rp (undefined :: c) s]

-- dummy
instance (ReadP (a p), ReadP (b p)) => ReadP ((:*:) a b p) where
    readsPAPrec ap _ _ s = [(a :*: b, r) |
                            (a, t) <- readsPAPrec ap rp (undefined :: a p) s,
                            (b, r) <- readsPAPrec ap (not rp) (undefined :: b p) t]
        where rp = checkIsRightPosed ap False

instance (ReadProd (a p), ReadProd (b p)) => ReadProd ((:*:) a b p) where
    readProd ap _ d _ s = [(a :*: b, r) |
                           (a, t) <- readProd ap rp d (undefined :: a p) s,
                           (d, u) <- lex t,
                           (b, r) <- readProd ap (not rp) d (undefined :: b p) u]
        where rp = checkIsRightPosed ap False

instance (Constructor c, ReadP ((:*:) a b p), ReadProd (a p), ReadProd (b p), ReadProd ((:*:) a b p)) => ReadP (C1 c ((:*:) a b) p) where
    readsPAPrec ap rp dm =
        let
            cn :: String
            cn = conName dm

            cf :: Fixity
            cf = conFixity dm

            myAP :: AssociativePrecision
            myAP = gF2AP cf
            
            next d = readProd myAP uselessRP d (unM1 dm)
        in
            readParen (shouldParen ap rp myAP) $ 
                case cf of
                    Prefix -> if conIsRecord dm
                              then \s -> [(M1 a, r) |
                                          (cn, t) <- lex s,
                                          ("{", u) <- lex t,
                                          (a, v) <- next ", " u,
                                          ("}", r) <- lex v]
                              else \s -> [(M1 a, r) |
                                          (cn, t) <- lex s,
                                          (a, r) <- next " " t]
                    _ -> \s -> [(M1 a, r) | (a, r) <- next cn s]

instance (Constructor c, ReadP (U1 p)) => ReadP (C1 c U1 p) where
    -- only Prefix
    readsPAPrec _ _ dm s =
        let
            cn = conName dm
        in
            [(M1 U1, r) | (cn, r) <- lex s]

instance (Constructor c, ReadP (f p)) => ReadP (C1 c f p) where
    -- only Prefix
    readsPAPrec ap rp dm =  
        let
            cn :: String
            cn = conName dm

            next = readsPAPrec prefixAP uselessRP (unM1 dm)
        in
            readParen (shouldParen ap rp . gF2AP . conFixity $ dm) $
                \s -> (
                    if conIsRecord dm
                    then [(M1 a, r) |
                          (cn, t) <- lex s,
                          ("{", u) <- lex t,
                          (a, v) <- next u,
                          ("}", r) <- lex v]
                    else [(M1 a, r) |
                          (cn, t) <- lex s,
                          (a, r) <- next t])

instance ReadP (f p) => ReadP (D1 c f p) where
    readsPAPrec ap rp _ s = [(M1 a, r) | (a, r) <- readsPAPrec ap rp (undefined :: f p) s]

instance (Selector c, ReadP (f p)) => ReadP (S1 c f p) where 
    readsPAPrec ap rp dm s = (
            if length sn > 0
            then [(M1 a, r) |
                  (sn, t) <- lex s,
                  ("=", u) <- lex t,
                  (a, r) <- readsPAPrec uselessAP uselessRP (undefined :: f p) u]
            else [(M1 a, r) | (a, r) <- readsPAPrec ap rp (undefined :: f p) s])
        where
            sn = selName dm

instance (Selector c, ReadP (f p)) => ReadProd (S1 c f p) where

instance ReadP (f p) => ReadP (M1 i c f p) where
    readsPAPrec ap rp _ s = [(M1 a, r) | (a, r) <- readsPAPrec ap rp (undefined :: f p) s]

instance (ReadP (l p), ReadP (r p)) => ReadP ((:+:) l r p) where
    readsPAPrec ap rp _ s =
        [(L1 a, u) | (a, u) <- readsPAPrec ap rp (undefined :: l p) s] ++
        [(R1 b, v) | (b, v) <- readsPAPrec ap rp (undefined :: r p) s]

data Exa = Z | I Int Exa deriving (Eq, Show, Read, Generic)

instance ReadP Exa where
    readsPAPrec ap rp x s = [(to a, t) | (a, t) <- readsPAPrec ap rp (from x) s]

someFunc2 :: IO ()
someFunc2 = do
    let test1 = "Z"
    let test2 = "I 3 Z"
    let test3 = "I 3 (I 2 Z)"
    let res1 = readsPAPrec uselessAP uselessRP (undefined :: Exa) test1
    let res2 = readsPAPrec uselessAP uselessRP (undefined :: Exa) test2
    let res3 = readsPAPrec uselessAP uselessRP (undefined :: Exa) test3
    print $ (Z, "") `elem` res1
    print $ (I 3 Z, "") `elem` res2
    print $ (I 3 (I 2 Z), "") `elem` res3
