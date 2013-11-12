{-# LANGUAGE RecordWildCards #-}

module BV.Util(mod2,
               zero,
               mkConst, 
               tConst,
               constSlice,
               constMul,
               constInvert,
               constNeg,
               constConcat,
               catom,
               ctermPlus,
               ctermMul,
               ctermUMinus,
               ctermSubst,
               catomSolve) where

import Data.Bits
import Data.List
import Math.NumberTheory.Moduli

import Util hiding (trace)
import BV.Types

mod2 :: Integer -> Int -> Integer
mod2 i w = i `mod` (1 `shiftL` w)


zero :: Int -> Const
zero w = Const 0 w

mkConst :: Integer -> Int -> Const
mkConst i w = Const (i `mod2` w) w

constSlice :: Integer -> (Int, Int) -> Const
constSlice c (l,h) = Const (foldl' (\a i -> if' (testBit c i) (setBit a (i-l)) a) 0 [l..h]) (h - l + 1)

constMul :: Integer -> Const -> Int -> Const
constMul c cn w = mkConst (c * (cVal cn)) w

constInvert :: Integer -> Int -> Maybe Integer
constInvert i w = invertMod i (1 `shiftL` w)

constNeg :: Const -> Const
constNeg (Const c w) = mkConst ((complement c) `mod2` w) w

constConcat :: Const -> Const -> Const
constConcat c1 c2 = mkConst (cVal c1 + (cVal c2 `shiftL` (width c1))) (width c1 + width c2)

tConst :: Integer -> Int -> Term
tConst i w = TConst $ mkConst i w

-- assumes that terms have been gathered already
ctermOrder :: CTerm -> CTerm
ctermOrder (CTerm ts c) = CTerm (sortBy (\t1 t2 -> compare (snd t1) (snd t2)) ts) c

ctermGather :: CTerm -> CTerm
ctermGather (CTerm ts c) = CTerm ts' c
    where w = width c
          ts' = filter ((/= 0) . fst)
                $ map (\ts0@((_,v):_) -> ((sum $ map fst ts0) `mod2` w, v))
                $ sortAndGroup snd ts

ctermPlus :: [CTerm] -> CTerm
ctermPlus = ctermOrder . ctermGather . ctermPlus'

ctermPlus' :: [CTerm] -> CTerm
ctermPlus' ts = CTerm (concatMap ctVars ts) (mkConst (sum $ map (cVal . ctConst) ts) w)
    where w = width $ head ts

ctermMul :: CTerm -> Integer -> Int -> CTerm
ctermMul t c w = ctermOrder $ ctermGather $ ctermMul' t c w

ctermMul' :: CTerm -> Integer -> Int -> CTerm
ctermMul' CTerm{..} c w = CTerm (map (\(i,v) -> ((i*c) `mod2` w, v)) ctVars) (mkConst ((cVal ctConst) * c) w)

ctermSubst :: (Var, (Int,Int)) -> CTerm -> CTerm -> CTerm
ctermSubst v ct ct'@(CTerm vs c) = ctermPlus
                                   $ (map (\(i,v') -> if' (v'==v) (ctermMul ct i w) (CTerm [(i,v')] (zero w))) vs) 
                                     ++ [CTerm [] c]
    where w = width ct'

ctermUMinus :: CTerm -> CTerm
ctermUMinus t = ctermMul t (-1) (width t)

catom :: Rel -> CTerm -> CTerm -> Either Bool CAtom
catom rel (CTerm [] c1) (CTerm [] c2) = Left $
    case rel of
         Eq  -> cVal c1 == cVal c2
         Neq -> cVal c1 /= cVal c2
         Lt  -> cVal c1 <  cVal c2
         Lte -> cVal c1 <= cVal c2
catom rel ct1 ct2 = Right $ CAtom rel ct1 ct2

-- Solve atom wrt given variable
catomSolve :: (Var, (Int,Int)) -> CAtom -> Maybe CTerm
catomSolve v a@(CAtom rel ct1 ct2) | rel /= Eq  = Nothing
                                   | null lhs   = Nothing
                                   | otherwise  = fmap (\inv -> ctermMul (ctermUMinus $ CTerm rhs ctConst) inv w) minv
    where CTerm{..} = ctermPlus [ct1, ctermUMinus ct2]
          (lhs, rhs) = partition ((== v) . snd) ctVars
          [(i,_)] = lhs
          w = width ct1
          minv = constInvert i w
