{-# LANGUAGE RecordWildCards #-}

module BV.Util(mod2,
               zero,
               mkConst, 
               tConst,
               termExt,
               constSlice,
               constMul,
               constInvert,
               constNeg,
               constConcat,
               mkCAtom,
               ctermPlus,
               ctermMul,
               ctermUMinus,
               ctermSlice,
               ctermSubst,
               catomSolve) where

import Data.Bits
import Data.List
import Data.Maybe
import Math.NumberTheory.Moduli

import Util hiding (trace)
import BV.Types
import Debug.Trace

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

termExt :: Term -> Int -> Term
termExt t w | width t >= w = t
            | otherwise    = TConcat [t, tConst 0 (w - width t)]

-- assumes that terms have been gathered already
ctermOrder :: CTerm -> CTerm
ctermOrder (CTerm ts c) = CTerm (sortBy (\t1 t2 -> compare (snd t1) (snd t2)) ts) c

ctermGather :: CTerm -> CTerm
ctermGather (CTerm ts c) = CTerm ts' c
    where w = width c
          ts' = filter ((/= 0) . fst)
                $ map (\ts0@((_,v):_) -> ((sum $ map fst ts0) `mod2` w, v))
                $ sortAndGroup snd ts

ctermPlus :: [CTerm] -> Int -> CTerm
ctermPlus ts w = ctermOrder $ ctermGather $ ctermPlus' ts w

ctermPlus' :: [CTerm] -> Int -> CTerm
ctermPlus' ts w | any ((< w) . width) ts = error "BV.ctermPlus': cannot expand term width"
                | otherwise = CTerm (concatMap ctVars ts) (mkConst (sum $ map (cVal . ctConst) ts) w)

ctermMul :: CTerm -> Integer -> Int -> CTerm
ctermMul t c w = ctermOrder $ ctermGather $ ctermMul' t c w

ctermMul' :: CTerm -> Integer -> Int -> CTerm
ctermMul' CTerm{..} c w = CTerm (map (\(i,v) -> ((i*c) `mod2` w, v)) ctVars) (mkConst ((cVal ctConst) * c) w)

ctermSubst :: (Var, (Int,Int)) -> CTerm -> CTerm -> CTerm
ctermSubst v ct ct'@(CTerm vs c) = 
    ctermPlus
    ((map (\(i,v') -> if' (v'/=v) 
                          (CTerm [(i,v')] (zero w)) $
                        if' (width ct < width ct')
                            (error $ "BV.ctermSubst " ++ show v ++ " " ++ show ct ++ " " ++ show ct' ++ ": cannot expand term width")
                            (ctermMul ct i w)) vs) 
     ++ [CTerm [] c]) w
    where w = width ct'

ctermUMinus :: CTerm -> CTerm
ctermUMinus t = ctermMul t (-1) (width t)

ctermSlice :: CTerm -> (Int,Int) -> Maybe CTerm
ctermSlice ct@(CTerm ts c) (l,h) | -- at most one term has bits below l and this term must have multiplier =1
                                   (all (\(i,_) -> i `mod2` l == 0 || i == 1) ts) &&
                                   (length $ filter (\i -> i `mod2` l /= 0) $ (cVal c) : (map fst ts)) <= 1
    = Just $ CTerm ((filter (\(_,(_,(ll,hh))) -> ll <= hh))
                    $ map (\(i,(v,(l',_h))) -> if' (i `mod2` l == 0)
                                                   (i `shiftR` l, (v,(l',min _h (l'+h))))
                                                   (i `mod2` w, (v,(l'+l, min _h (l'+h))))) ts)
             $ constSlice (cVal c) (l,h)
                                 | otherwise 
    = trace (error $ "ctermSlice: cannot handle slice [" ++ show l ++ ":" ++ show h ++ "] of term " ++ show ct) Nothing

                             {-| null ts 
                              = Just $ CTerm [] $ constSlice (cVal c) (l,h)
                              | l == 0  
                              = Just $ CTerm (map (\(i,(v,(l',_h))) -> (i `mod2` w, (v,(l',min _h (l'+h))))) ts) $ constSlice (cVal c) (l,h)
                              | length ts == 1 && cVal c == 0 && (fst $ head ts) == 1
                              = let [(_, (v,(_l,_h)))] = ts in
                                Just $ CTerm [(1,(v,(l+_l,min _h (l+_l+w-1))))] $ zero w -}
    where w = h - l + 1

catom :: Rel -> CTerm -> CTerm -> Either Bool CAtom
catom rel (CTerm [] c1) (CTerm [] c2) = Left $
    case rel of
         Eq  -> cVal c1 == cVal c2
         Neq -> cVal c1 /= cVal c2
         Lt  -> cVal c1 <  cVal c2
         Lte -> cVal c1 <= cVal c2
catom rel ct1 ct2 | ct1 == ct2        = Left $
     case rel of
         Eq  -> True
         Neq -> False
         Lt  -> False
         Lte -> True  
catom rel ct1 ct2 = Right $ CAtom rel ct1 ct2

-- Move the first variable (in var ordering) to the left and
-- try to solve the equation wrt this var.
mkCAtom :: Rel -> CTerm -> CTerm -> Either Bool CAtom
mkCAtom rel ct1 ct2 | width ct1 /= width ct2 = error "BV.mkCAtom: cannot make an atom out of unequal-width terms"
                    | elem rel [Eq, Neq] = 
    if null ctVars 
       then catom rel ct (CTerm [] $ zero $ width ct)
       else Right $ catomInSolvedForm rel (head ctVars) (ctermUMinus $ CTerm (tail ctVars) ctConst)
                    | otherwise          = catom rel ct1 ct2
    where ct@CTerm{..} = ctermPlus [ct1, ctermUMinus ct2] $ width ct1
          
catomInSolvedForm :: Rel -> (Integer, (Var,(Int,Int))) -> CTerm -> CAtom
catomInSolvedForm rel (i, v) ct = maybe (CAtom rel (CTerm [(i,v)] (zero $ width ct)) ct) 
                                        (\inv -> CAtom rel (CTerm [(1,v)] (zero $ width ct)) (ctermMul ct inv w))
                                        (constInvert i w)
    where w = width ct

-- Solve atom wrt given variable.  If successful, returns the solution,
-- and additional atoms that are implided by the input atom, but not
-- by the solution. 
-- (see Section 3.2 of "A decision procedure for bit-vector arithmetic")
catomSolve :: (Var, (Int,Int)) -> CAtom -> Maybe (Either Bool (CTerm, [CAtom]))
catomSolve v (CAtom rel ct1 ct2) | rel /= Eq      = Nothing
                                 | null lhs       = Nothing
                                 | pow2 == 0      = Just $ Right (ctermMul ctrhs inv w, [])
                                 | cas == Nothing = Just $ Left False
                                 | otherwise      = fmap (\ct' -> Right (ctermMul ct' inv w', fromJust cas))
                                                         $ ctermSlice ctrhs (pow2,w-1)
    where CTerm{..} = ctermPlus [ct1, ctermUMinus ct2] $ width ct1
          (lhs, rhs) = partition ((== v) . snd) ctVars
          ctrhs = ctermUMinus $ CTerm rhs ctConst
          [(i,_)] = lhs
          w = width ct1
          (pow2, oddi) = oddevenDecomp i
          w' = w - pow2
          inv = fromJust $ constInvert oddi w'
          cas = case mkCAtom Eq (CTerm [] $ zero w') (fromJust $ ctermSlice ctrhs (0, pow2-1)) of
                     Left True  -> Just []
                     Left False -> Nothing
                     Right ca   -> Just [ca]

 -- decompose i into a product of a power of 2 and an odd number
oddevenDecomp :: Integer -> (Int, Integer)
oddevenDecomp i | odd i     = (0, i)
                | otherwise = let (p, i') = oddevenDecomp (i `div` 2)
                                  in (p + 1, i')
