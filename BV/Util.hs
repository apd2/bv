module BV.Util() where

import BV.Types

mod2 :: Integer -> Int -> Integer
mod2 i w = i `mod` (1 `shiftL` w)


zero :: Int -> Const
zero w = Const 0 w

const :: Integer -> Int -> Const
const i w = Const (i `mod2` w) w

constSlice :: Integer -> (Int, Int) -> Const
constSlice c (l,h) = Const (foldl' (\a i -> if' (testBit c i) (setBit a (i-l)) a) 0 [l..h]) (h - l + 1)

constMul :: Integer -> Const -> Int -> Const
constMul c cn w = const (c * (cVal cn)) w

constInvert :: Integer -> Int -> Integer
constInvert i w = invertMod i (1 `shiftL` w)

constNeg :: Const -> Const
constNeg (Const c w) = const (complement c) `mod2` w) w

constConcat :: Const -> Const -> Const
constConcat c1 c2 = const (c1 + (c2 `shiftL` (width c1))) (width c1 + width c2)

-- assumes that terms have been gathered already
ctermOrder :: CTerm -> CTerm
ctermOrder (CTerm ts c) = CTerm (sortBy (compare . snd) ts) c

ctermGather :: CTerm -> CTerm
ctermGather (CTerm ts c) = CTerm ts' c
    where w = width c
          ts' = filter ((/= 0) . fst)
                $ map (\ts'@((_,v):_) -> ((sum $ map fst ts') `mod2` w, v))
                $ sortAndGroup snd ts

ctermPlus :: [CTerm] -> CTerm
ctermPlus = ctermOrder . ctermGather . ctermPlus'

ctermPlus' :: [CTerm] -> CTerm
ctermPlus' ts = CTerm (concatMap ctVars ts, const (sum $ map ctConst ts) w)

ctermMul :: CTerm -> Integer -> Int -> CTerm
ctermMul t c w = ctermOrder . ctermGather . ctermMul' t c w

ctermMul' :: CTerm -> Integer -> Int -> CTerm
ctermMul' CTerm{..} c w = CTerm (map (\(i,v) -> (i*c) `mod2` w) ctVars) (const ((cVal ctConst) * c) w)

ctermSubst :: (Var, (Int,Int)) -> CTerm -> CTerm -> CTerm
ctermSubst v ct ct'@(CTerm vs c) = ctermPlus
                                   $ (map (\(i,v') -> if' (v'==v) (ctermMul ct i w) (CTerm [(i,v')] (zero w)) vs)) 
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
catomSolve (CAtom rel ct1 ct2) | rel /= Eq = Nothing
                               | null lhs  = Nothing
                               | otherwise = Just $ ctermMul (ctermUMinus $ CTerm rhs ctConst) (constInvert i w) w
    where CTerm{..} = ctermPlus [ct1, ctermUMinus ct2]
          (lhs, rhs) = partition (\(i,v') -> v' == v && odd i) ctVars
          [(i,_)] = lhs
          w = width ct1
