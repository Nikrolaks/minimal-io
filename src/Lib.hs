{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE EmptyDataDeriving          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Lib (
    Expression,
    StringTree,
    AssociativePrecision,
    ShowP,
    someFunc
) where

import GHC.Generics
import Text.Show
import Data.Typeable
import Data.Foldable
--import Generics.Deriving

data Expression a = Z | S (Expression a) | P {} | Q {e :: (Expression a)} | CE a | (Expression a) :* (Expression a) | W {w1 :: a, w2 :: a, w3 :: a} deriving (Show, Generic)

data StringTree = L String | Ch String StringTree | R String StringTree StringTree deriving Show

data AssociativePrecision = InfixAP Int | InfixlAP Int | InfixrAP Int

class ShowP a where
    devTree :: a -> StringTree

    --- LAW showsPAPrec ap x r ++ s == showsPAPrec ap x (r ++ s)
    showsPAPrec :: AssociativePrecision -> a -> ShowS
    showsPAPrec _ x s = showP x s
    
    showP :: a -> ShowS
    showP x = showsPAPrec (InfixAP 11) x

instance ShowP (Par1 p) where
    devTree = const . L $ "Par1"
    showP (Par1 p) = showString "not implemented"

instance ShowP (f p) => ShowP (Rec1 f p) where
    devTree = const . L $ "Rec1"
    showP (Rec1 a) = showString "not implemented"

instance ShowP (U1 p) where
    devTree = const . L $ "U1"
    showP U1 = id

instance Show c => ShowP (K1 i c p) where
    devTree = const . L $ "K1"
    showP k1@(K1 e) = showString $ show e

instance (ShowP (a p), ShowP (b p), ShowP (c p), ShowP ((:*:) b c p)) => ShowP ((:*:) a ((:*:) b c) p) where
    devTree (a :*: b) = R ":*:" (devTree a) (devTree b)
    -- so dirty hack
    showP (a :*: b) s = showP a "" ++ s ++ showP b s

instance (ShowP (a p), ShowP (b p)) => ShowP ((:*:) a b p) where
    devTree (a :*: b) = R ":*:" (devTree a) (devTree b)
    -- so dirty hack
    showP (a :*: b) s = showP a "" ++ s ++ showP b ""

instance (Constructor c, ShowP (a p), ShowP (b p), ShowP (((:*:) a b p))) => ShowP (C1 c ((:*:) a b) p) where
    devTree c1@(M1 a) = Ch "C1" $ devTree a
    showP c1@(M1 a) =
        let
            cn = conName c1
            next = showP a
        in
        case conFixity c1 of
            -- record 
            Prefix -> showString $ cn ++ " {" ++ next ", " ++ "}"
            Infix _ _ -> showString . next $ " " ++ cn ++ " "

instance (Constructor c, ShowP (U1 p)) => ShowP (C1 c U1 p) where
    devTree c1@(M1 a) = Ch "C1" $ devTree a
    -- only Prefix
    showP c1@(M1 a) = showString . conName $ c1

instance (Constructor c, ShowP (f p)) => ShowP (C1 c f p) where
    devTree c1@(M1 a) = Ch "C1" $ devTree a
    -- only Prefix
    showP c1@(M1 a) =
        let
            cn = conName c1
            next = showP a
        in if conIsRecord c1
           then showString $ cn ++ " {" ++ next "" ++ "}"
           else showString (cn ++ " ") . next

instance ShowP (f p) => ShowP (D1 c f p) where
    devTree d1@(M1 a) = Ch "D1" $ devTree a
    showP d1@(M1 a) = showP a

instance (Selector c, ShowP (f p)) => ShowP (S1 c f p) where
    devTree s1@(M1 a) = Ch "S1" $ devTree a
    showP s1@(M1 a) | length sn > 0 = showString (sn ++ " = ") . next
                    | otherwise = next
        where sn = selName s1
              next = showP a

instance ShowP (f p) => ShowP (M1 i c f p) where
    devTree m1@(M1 a) = Ch "M1" $ devTree a
    showP m1@(M1 a) = showP a

instance (ShowP (l p), ShowP (r p)) => ShowP ((:+:) l r p) where
    devTree x = case x of
        L1 a -> Ch "L1" $ devTree a
        R1 a -> Ch "R1" $ devTree a
    showP x = case x of
        L1 a -> showP a
        R1 a -> showP a

infixl 3 :*

printRes test = showP (from test) $ " !!! " ++ (show $ devTree (from test))

someFunc = do
    --let test1 = Z :: Expression Int
    --let test2 = CE 3 :: Expression Int
    --let test3 = CE 2 :* Z :: Expression Int
    --let test4 = W 4 3 7 :: Expression Int
    --let test5 = P :: Expression Int
    --let test6 = Q test2
    --putStrLn $ printRes test1
    --putStrLn $ printRes test2
    --putStrLn $ printRes test3
    --putStrLn $ printRes test4
    --putStrLn $ printRes test5
    --putStrLn $ printRes test6
    --print . fromM1 . from $ test4


