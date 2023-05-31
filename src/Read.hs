{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Read (
    ReadP(..)
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

    readP :: ReadS a
    readP = readsPAPrec uselessAP uselessRP

class ReadP a => ReadProd a where
    readProd :: AssociativePrecision -> Bool -> String -> ReadS a
    readProd ap rp d = readsPAPrec ap rp

instance ReadP Int where
    readsPAPrec ap rp = readsPrec (getPrecision ap)

instance ReadP p => ReadP (Par1 p) where
    readsPAPrec ap rp s = [(Par1 x, r) | (x, r) <- readsPAPrec ap rp s]

instance ReadP (f p) => ReadP (Rec1 f p) where
    readsPAPrec ap rp s = [(Rec1 a, r) | (a, r) <- readsPAPrec ap rp s]

instance ReadP (U1 p) where
    readsPAPrec _ _ s = []

instance ReadP c => ReadP (Rec0 c p) where
    readsPAPrec ap rp s = [(K1 e, r) | (e, r) <- readsPAPrec ap rp s]

-- dummy
instance (ReadP (a p), ReadP (b p)) => ReadP ((:*:) a b p) where
    readsPAPrec = undefined

insertions :: String -> String -> [Int]
insertions = helper 0 
    where
        helper :: Int -> String -> String -> [Int]
        helper _ _ [] = []
        helper n pat s@(x:xs) | take (length pat) s == pat = n : end
                              | otherwise = end
            where end = helper (n+1) pat xs

instance (ReadProd (a p), ReadProd (b p)) => ReadProd ((:*:) a b p) where
    readProd ap _ "" s = [(a :*: b, r) |
                          (a, t) <- readProd ap rp "" s,
                          (b, r) <- readProd ap (not rp) "" t]
        where rp = checkIsRightPosed ap False
    readProd ap _ d s = [(a :*: b, r) |
                         deli <- insertions d s,
                         (a, t) <- readProd ap rp d (take deli s),
                         (b, r) <- readProd ap (not rp) d (drop (deli + length d) s)]
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
    readsPAPrec _ _ s | fst (lex s !! 0) == conName (undefined :: C1 c U1 p) = [(M1 U1, r) | (_, r) <- lex s]
                      | otherwise = []

instance (Constructor c, ReadP (f p)) => ReadP (C1 c f p) where
    -- only Prefix
    readsPAPrec ap rp =  
        let
            pr = (undefined :: C1 c f p)
            cn = conName pr
        in
            readParen (shouldParen ap rp . gF2AP . conFixity $ pr) $
                if (conIsRecord pr)
                    then \s -> [(M1 a, r) |
                                (cn, t) <- lex s,
                                ("{", u) <- lex t,
                                (a, v) <- readsPAPrec prefixAP uselessRP u,
                                ("}", r) <- lex v]
                    else \s -> [(M1 a, r) |
                                (cn, t) <- lex s,
                                (a, r) <- readsPAPrec prefixAP uselessRP t]

instance ReadP (f p) => ReadP (D1 c f p) where
    readsPAPrec ap rp s = [(M1 a, r) | (a, r) <- readsPAPrec ap rp s]

instance (Selector c, ReadP (f p)) => ReadP (S1 c f p) where 
    readsPAPrec ap rp s =
        let
            sn = selName (undefined :: S1 c f p)
        in
            if length sn > 0
            then [(M1 a, r) |
                  (sn, t) <- lex s,
                  ("=", u) <- lex t,
                  (a, r) <- readsPAPrec uselessAP uselessRP u]
            else [(M1 a, r) | (a, r) <- readsPAPrec ap rp s]

instance (Selector c, ReadP (f p)) => ReadProd (S1 c f p) where

instance ReadP (f p) => ReadP (M1 i c f p) where
    readsPAPrec ap rp s = [(M1 a, r) | (a, r) <- readsPAPrec ap rp s]

instance (ReadP (l p), ReadP (r p)) => ReadP ((:+:) l r p) where
    readsPAPrec ap rp s =
        [(L1 a, u) | (a, u) <- readsPAPrec ap rp s] ++
        [(R1 b, v) | (b, v) <- readsPAPrec ap rp s]