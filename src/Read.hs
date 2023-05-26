{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module Read (
    ReadP(..),
    someFunc2
) where

import Base (
    AssociativePrecision,
    prefixAP,
    uselessAP,
    uselessRP,
    gF2AP,
    getPrecision,
    checkConflict,
    shouldParen,
    checkIsRightPosed)

import GHC.Generics
import Debug.Trace

class ReadP a where
    readsPAPrec :: AssociativePrecision -> Bool -> ReadS a

class ReadP a => ReadProd a where
    readProd :: AssociativePrecision -> Bool -> String -> ReadS a
    readProd ap rp d = readsPAPrec ap rp

instance ReadP Int where
    readsPAPrec ap rp = readsPrec (getPrecision ap)

instance ReadP p => ReadP (Par1 p) where
    readsPAPrec ap rp s = [(Par1 x, t) | (x, t) <- readsPAPrec ap rp s]

instance ReadP (f p) => ReadP (Rec1 f p) where
    readsPAPrec ap rp s = [(Rec1 a, t) | (a, t) <- readsPAPrec ap rp s]

instance ReadP (U1 p) where
    readsPAPrec _ _ s = [(U1, s)]

instance ReadP c => ReadP (Rec0 c p) where
    readsPAPrec ap rp s = [(K1 e, t) | (e, t) <- readsPAPrec ap rp s]

-- dummy
instance (ReadP (a p), ReadP (b p)) => ReadP ((:*:) a b p) where
    readsPAPrec = undefined

instance (ReadProd (a p), ReadProd (b p)) => ReadProd ((:*:) a b p) where
    readProd ap _ "" s = [(a :*: b, r) |
                          (a, t) <- readProd ap rp "" s,
                          (b, r) <- readProd ap (not rp) "" t]
        where rp = checkIsRightPosed ap False
    readProd ap _ d s = [(a :*: b, r) |
                         (a, t) <- readProd ap rp d s,
                         (d, u) <- lex t,
                         (b, r) <- readProd ap (not rp) d u]
        where rp = checkIsRightPosed ap False

instance (Constructor c, ReadP ((:*:) a b p), ReadProd (a p), ReadProd (b p), ReadProd ((:*:) a b p)) => ReadP (C1 c ((:*:) a b) p) where
    readsPAPrec ap rp =
        let
            (shouldMy, res) =
                let
                    cn = conName . fst $ res "" !! 0
                    cf = conFixity . fst $ res "" !! 0
                    myAP = gF2AP cf
                in (
                    shouldParen ap rp (gF2AP . conFixity . fst $ res "" !! 0),
                    case cf of
                        Prefix -> if (conIsRecord . fst $ res "" !! 0)
                                  then \s -> [(M1 a, r) |
                                              (cn, t) <- lex s,
                                              ("{", u) <- lex t,
                                              (a, v) <- readProd myAP uselessRP ", " u,
                                              ("}", r) <- lex v]
                                  else \s -> [(M1 a, r) |
                                              (cn, t) <- lex s,
                                              (a, r) <- readProd myAP uselessRP "" t]
                        _ -> \s -> [(M1 a, r) | (a, r) <- readProd myAP uselessRP cn s])
        in
            readParen shouldMy res

instance (Constructor c, ReadP (U1 p)) => ReadP (C1 c U1 p) where
    -- only Prefix
    readsPAPrec _ _ s =
        let
            res = 
                let
                    cn = conName . fst $ res !! 0
                in
                    [(M1 U1, r) | (cn, r) <- lex s]
        in
            res

instance (Constructor c, ReadP (f p)) => ReadP (C1 c f p) where
    -- only Prefix
    readsPAPrec ap rp =  
        let
            (shouldMy, res) =
                let
                    cn = conName . fst $ res "" !! 0
                in (
                    shouldParen ap rp (gF2AP . conFixity . fst $ res "" !! 0),
                    if (conIsRecord . fst $ res "" !! 0)
                    then \s -> [(M1 a, r) |
                                (cn, t) <- lex s,
                                ("{", u) <- lex t,
                                (a, v) <- readsPAPrec prefixAP uselessRP u,
                                ("}", r) <- lex v]
                    else \s -> [(M1 a, r) |
                                (cn, t) <- lex s,
                                (a, r) <- readsPAPrec prefixAP uselessRP t])
        in
            readParen shouldMy res

instance ReadP (f p) => ReadP (D1 c f p) where
    readsPAPrec ap rp s = [(M1 a, r) | (a, r) <- readsPAPrec ap rp s]

instance (Selector c, ReadP (f p)) => ReadP (S1 c f p) where 
    readsPAPrec ap rp s = 
        let
            res = 
                let
                    sn = selName (fst $ res !! 0)
                in
                    if length sn > 0
                    then [(M1 a, r) |
                          (sn, t) <- lex s,
                          ("=", u) <- lex t,
                          (a, r) <- readsPAPrec uselessAP uselessRP u]
                    else [(M1 a, r) | (a, r) <- readsPAPrec ap rp s]
        in res

instance (Selector c, ReadP (f p)) => ReadProd (S1 c f p) where

instance ReadP (f p) => ReadP (M1 i c f p) where
    readsPAPrec ap rp s = [(M1 a, r) | (a, r) <- readsPAPrec ap rp s]

instance (ReadP (l p), ReadP (r p)) => ReadP ((:+:) l r p) where
    readsPAPrec ap rp s =
        [(L1 a, u) | (a, u) <- readsPAPrec ap rp s] ++
        [(R1 b, v) | (b, v) <- readsPAPrec ap rp s]

data Exa = Z
         | I Int Exa
--         | W {w1 :: Int, w2 :: Int}
--         | Int :*- Int
--         | Ps {we :: Int}
--         | Q {}
            deriving (Eq, Show, Read, Generic)

data A0 = Zs | Ss Int deriving (Eq, Show, Read, Generic)
data A1 a = Is a deriving (Eq, Show, Read, Generic1)

instance ReadP Exa where
    readsPAPrec ap rp s = [(to a, t) | (a, t) <- readsPAPrec ap rp s]

instance ReadP A0 where
    readsPAPrec ap rp s = [(to a, t) | (a, t) <- readsPAPrec ap rp s]

instance ReadP a => ReadP (A1 a) where
    readsPAPrec ap rp s = [(to1 a, t) | (a, t) <- readsPAPrec ap rp s]

someFunc2 :: IO ()
someFunc2 = do
    --let test1 = "Z"
    --let test2 = "I 3 Z"
    let test3 = "I 3 (I 2 Z)"
    --let test4 = "W {w1 = 1, w2 = 3}"
    --let test5 = "7 :*- 8"
    --let test6 = "Ps {we = 14}"
    --let test7 = "Q"
    --let res1 = readsPAPrec uselessAP uselessRP test1
    --let res2 = readsPAPrec uselessAP uselessRP test2
    let res3 = (readsPAPrec uselessAP uselessRP :: ReadS Exa) test3
    --let res4 = readsPAPrec uselessAP uselessRP test4
    --let res5 = readsPAPrec uselessAP uselessRP test5
    --let res6 = readsPAPrec uselessAP uselessRP test6
    --let res7 = readsPAPrec uselessAP uselessRP test7
    --print $ (Z, "") `elem` res1
    --print $ (I 3 Z, "") `elem` res2
    --print $ (I 3 (I 2 Z), "") `elem` res3
    --print $ (W 1 3, "") `elem` res4
    --print $ (7 :*- 8, "") `elem` res5
    --print $ (Ps 14, "") `elem` res6
    --print $ (Q, "") `elem` res7
    print $ res3
    
    --let t0 = "Ss 13"
    --let t1 = "Is (Ss 12)"
    --print $ (readsPAPrec uselessAP uselessRP :: ReadS A0) t0
    --print $ (readsPAPrec uselessAP uselessRP :: ReadS (A1 A0)) t1
