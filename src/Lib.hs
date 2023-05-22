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

module Lib
    ( Expression,
        someFunc
    ) where

import GHC.Generics
--import Generics.Deriving

data Expression a = V | CE a | (Expression a) :* (Expression a) deriving (Show, Generic)

class ShowP f where
    showP :: String -> f a -> String

-- If we have a parameter ‘p’, we just map over it, as expected:

instance ShowP Par1 where
    showP _ (Par1 p) = "Par1 p"

-- The same with ‘Rec1’ (just use ‘fmap’ because the inner part is a ‘Functor’):

instance ShowP f => ShowP (Rec1 f) where
    showP _ (Rec1 a) = "Rec1 a"

--instance (ShowP f, Constructor f) => ShowP (Rec1 f) where
--    showP _ r = conName $ unRec1 r

-- A constructor without fields only can be returned untouched:

instance ShowP U1 where
  showP s U1 = s

-- A field that is not ‘p’ parameter should not change:

instance Show c => ShowP (K1 i c) where
    --showP _ :: K1 i c p -> String
    showP s k1 = s ++ "uyt" ++ (show . unK1 $ k1)

-- Metadata has no effect, just unwrap it and continue with the inner value,
-- if the inner value is an instance of ‘Functor’:

instance (Constructor c, ShowP f) => ShowP (C1 c f) where
    showP _ c1@(M1 a) = case conFixity c1 of
        Prefix -> showP cn a
        Infix _ n -> show n ++ showP cn a
        where
            cn = conName c1

instance (ShowP f) => ShowP (D1 c f) where
    showP _ d1@(M1 a) = showP "d1" a

instance (Selector c, ShowP f) => ShowP (S1 c f) where
    showP s s1@(M1 a) = showP (s ++ selName s1 ++ "x3") a

instance ShowP f => ShowP (M1 i c f) where
    showP _ (M1 a) = showP "etoty" a

-- When we have a sum, we should try to map what we get, provided that it
-- contains something that has ‘Functor’ instance:

instance (ShowP l, ShowP r) => ShowP (l :+: r) where
    showP s (L1 a) = showP (s ++ "L") a
    showP s (R1 a) = showP (s ++ "R") a

-- The same for products:

instance (ShowP a, ShowP b) => ShowP (a :*: b) where
    showP s (a :*: b) = showP "" a ++ " " ++ s ++ " " ++ showP "" b


infixl 3 :*

someFunc :: IO ()
someFunc = do
    let e = CE 1 :* V
    let t = from e
    putStrLn $ showP "" t
