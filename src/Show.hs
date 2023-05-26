{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module Show (
    ShowP(..)
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
    showsPAPrec ap rp k1@(K1 e) = showsPAPrec ap rp e

-- dummy
instance (ShowP (a p), ShowP (b p)) => ShowP ((:*:) a b p) where
    showP (a :*: b) = undefined

instance (ShowProd (a p), ShowProd (b p)) => ShowProd ((:*:) a b p) where
    showProd ap _ (a :*: b) =
        let
            rp = checkIsRightPosed ap False
        in
            showProd ap rp a ++ showProd ap (not rp) b

instance (Constructor c, ShowP (((:*:) a b p)), ShowProd (a p), ShowProd (b p)) => ShowP (C1 c ((:*:) a b) p) where
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
            showParen (shouldParen ap rp myAP) $ variants cf

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
            showParen (shouldParen ap rp . gF2AP . conFixity $ c1) $ showString (
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