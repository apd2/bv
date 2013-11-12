-- Convert bit-vector terms and atoms to canonical form.
-- Based on: Barrett, Dill, Levitt "A Decision Procedure for Bit-Vector Arithmetic", 1998

{-# LANGUAGE RecordWildCards, TupleSections #-}

module BV.Canonize(termToCTerm,
                   atomToCAtom,
                   ex,
                   exTerm) where

import Data.Bits
import Data.List
import Data.Maybe
import Debug.Trace

import Util hiding (trace)
import TSLUtil hiding (assert)
import BV.Types
import BV.Util

-----------------------------------------------------------------
-- Validation
-----------------------------------------------------------------
assert :: Bool -> String -> a -> a
assert True  _ a = a
assert False s _ = error s

termValidate :: Term -> Term
termValidate t@(TConst (Const{..})) = assert (cVal `mod2` cWidth == cVal) ("invalid constant: " ++ show t) t
termValidate t@(TVar _)             = t
termValidate t@(TSlice t' (l,h))    = assert ((l <= h) && (h < width t')) ("invalid slice: " ++ show t) $ TSlice (termValidate t') (l,h)
termValidate   (TConcat ts)         = TConcat $ map termValidate ts
termValidate   (TNeg t')            = TNeg $ termValidate t'
termValidate t@(TPlus ts)           = assert ((not $ null ts) && (all (((width $ head ts) ==) . width) $ tail ts)) ("invalid sum: " ++ show t) 
                                      $ TPlus $ map termValidate ts
termValidate t@(TMul c t' w)        = assert (c `mod2` w == c) ("invalid multiplication: " ++ show t) $ TMul c (termValidate t') w

-----------------------------------------------------------------
-- Simplification
-----------------------------------------------------------------

-- Slices blow up canonization -- bring them all the way in if possible
termSimplify :: Term -> Term
termSimplify t@(TConst _)      = t
termSimplify t@(TVar _)        = t
termSimplify   (TConcat ts)    = case ts' of
                                     [t] -> t
                                     _   -> TConcat ts' 
                                 where
                                 ts' = mergeConcat
                                       $ concatMap (\t' -> case t' of
                                                                TConcat ts'' -> ts''
                                                                _            -> [t'])
                                       $ map termSimplify ts
termSimplify   (TNeg t)        = case termSimplify t of
                                      TNeg t'    -> t'
                                      TConst c   -> TConst $ constNeg c
                                      TConcat ts -> TConcat $ map (termSimplify . TNeg) ts
                                      t'         -> TNeg t'
termSimplify   (TPlus ts)      = case ts' of
                                      [t'] -> t'
                                      _    -> TPlus ts'
                                 where ts' = groupSum
                                             $ concatMap (\t' -> case t' of
                                                                      TPlus ts'' -> ts''
                                                                      _          -> [t'])
                                             $ map termSimplify ts
termSimplify   (TMul c t w) | c == 0                 = TConst $ zero w
                            | c == 1 && width t == w = termSimplify t
                            | otherwise = case termSimplify t of
                                               TConst cn      -> TConst $ constMul c cn w
                                               TMul   c' t' _ -> termSimplify $ TMul ((c * c') `mod2` w) t' w
                                               t'             -> TMul c t' w

termSimplify   (TSlice t (l,h)) | l == 0 && h == width t - 1 = termSimplify t
                                | otherwise = case termSimplify t of
                                                   TConst c         -> TConst $ constSlice (cVal c) (l,h)
                                                   TConcat ts       -> termSimplify $ TConcat $ concatSlice ts (l,h)
                                                   TNeg t'          -> termSimplify $ TNeg $ TSlice t' (l,h)
                                                   TSlice t' (l',_) -> termSimplify $ TSlice t' (l+l',h+l')
                                                   t'               -> TSlice t' (l,h)

concatSlice :: [Term] -> (Int,Int) -> [Term]
concatSlice []     _                    = []
concatSlice (t:ts) (l,h) | l >= width t = concatSlice ts (l - width t, h - width t)
                         | h < 0        = []
                         | otherwise    = TSlice t (max l 0, min h (width t - 1)) : concatSlice ts (l - width t, h - width t)

mergeConcat :: [Term] -> [Term]
mergeConcat []         = error "empty concat"
mergeConcat [t]        = [t]
mergeConcat (t1:t2:ts) = 
    case (t1, t2) of
         (TSlice t1' (l1,h1), TSlice t2' (l2,h2)) -> if' ((t1' == t2') && (l2 == h1 + 1))
                                                         (mergeConcat $ (termSimplify $ TSlice t1' (l1,h2)):ts)
                                                         (t1:mergeConcat (t2:ts)) 
         (TConst c1, TConst c2)                   -> [TConst $ constConcat c1 c2]
         _                                        -> t1:mergeConcat (t2:ts)

groupSum :: [Term] -> [Term]
groupSum ts = case ts'' ++ tconst of
                   []    -> [TConst $ zero w]
                   ts''' -> ts'''
    where w = width $ head ts
          (consts, ts') = partition termIsConst ts
          tconst = case (sum $ map (cVal . (\(TConst c) -> c)) consts) `mod2` w of
                        0 -> []
                        c -> [tConst c w]
          ts'' = groupSum' ts'


groupSum' :: [Term] -> [Term]
groupSum' []                  = []
groupSum' ts@((TMul _ t _):_) = maybeToList t' ++ (groupSum' ts')
                                where (t', ts') = groupTerm t ts
groupSum' ts@(t:_)            = maybeToList t' ++ (groupSum' ts')
                                where (t',ts') = groupTerm t ts

groupTerm :: Term -> [Term] -> (Maybe Term, [Term])
groupTerm t ts = (grouped, rest)
    where
    w = width $ head ts
    (coef, rest) = foldl' (\(coef',ts') t' -> if t' == t
                                                 then ((coef' + 1) `mod2` w, ts')
                                                 else case t' of
                                                           TMul c' t'' _ -> if t'' == t
                                                                               then ((coef' + c') `mod2` w, ts')
                                                                               else (coef', t':ts')
                                                           _             -> (coef', t':ts'))
                          (0,[]) ts
    grouped = case coef of
                   0 -> Nothing
                   1 -> Just t
                   _ -> Just $ TMul coef t w

-----------------------------------------------------------------
-- Term canonization
-----------------------------------------------------------------

termToCTerm :: Term -> CTerm
termToCTerm t = {-trace ("termToCTerm: t=" ++ show t ++ " simplified=" ++ show tsimp) $-} termToCTerm' tsimp
    where tsimp = termSimplify $ termValidate t

termToCTerm' :: Term -> CTerm
termToCTerm' (TConst c)       = CTerm [] c
termToCTerm' (TVar v)         = CTerm [(1,(v,(0, width v - 1)))] (zero $ width v)
termToCTerm' (TSlice t (l,h)) = {-trace ("termToCTerm' " ++ show (TSlice t (l,h)) ++ "=" ++ show t' ++ "(" ++ show (width t') ++ ")")-} t'
    where w = h - l + 1
          ct@(CTerm ts c) = termToCTerm' t
          t' = if' (null ts) 
                   (CTerm [] $ constSlice (cVal c) (l,h))                                   $
               if' (l == 0)
                   (CTerm (map (\(i,(v,(l',_))) -> (i `mod2` w, (v,(l',l'+h)))) ts) $ constSlice (cVal c) (l,h)) $
               if' (length ts == 1 && cVal c == 0 && (fst $ head ts) == 1)
                   (CTerm [(1,(fst $ snd $ head ts,(l,h)))] $ zero w)
                   (error $ "BV.termToCTerm: cannot handle slice [" ++ show l ++ ":" ++ show h ++ "] of term " ++ show ct)
termToCTerm' (TConcat ts)      = ctermPlus ts''
    where ts' = map termToCTerm' ts
          w = sum $ map width ts'
          (_, ts'') = foldl' (\(off, cts) ct@CTerm{..} -> 
                               let w' = width ct
                                   ((i,(v,(l',h'))) :_) = ctVars
                                   ct' = if' (length ctVars == 0) 
                                             (ctermMul ct (1 `shiftL` off) w) $
                                         if' (length ctVars == 1 && cVal ctConst == 0 && h' - l' < width ctConst) 
                                             (ctermMul ct (1 `shiftL` off) w) $
                                         if' (length ctVars == 1 && 
                                              h' - l' < width ctConst && 
                                              i == (-1) `mod2` w' && 
                                              ctConst == mkConst (-1) w')
                                             (CTerm [(((-1)*(1 `shiftL` off)) `mod2` w, (v,(l',h')))] $ mkConst (-1* (1 + ((-1) `mod2` off) + (((-1) `mod2` (w-off-w')) `shiftL` (off+w')))) w)
                                             (error $ "termToCTerm: cannot handle " ++ show (TConcat ts))
                               in (off+w', ct':cts)) 
                             (0,[]) ts'

termToCTerm' (TNeg t)          = {-trace ("termToCTerm' " ++ show (TNeg t) ++ "=" ++ show ct')-} ct'
    where ct = termToCTerm' t
          w = width ct
          ct' = ctermPlus [ctermMul ct (-1) w, CTerm [] (mkConst (-1) w)]

termToCTerm' (TPlus ts)        = ctermPlus $ map termToCTerm' ts
termToCTerm' (TMul c t w)      = ctermMul (termToCTerm' t) c w

------------------------------------------------------------
-- Atom canonization
------------------------------------------------------------

atomToCAtom :: Atom -> Either Bool CAtom
atomToCAtom a@(Atom rel t1 t2) = assert (width t1 == width t2) ("atomToCAtom: width mismatch: " ++ show a) $ mkCAtom rel ct1 ct2
    where ct1 = termToCTerm t1
          ct2 = termToCTerm t2

-- Move the first variable (in var ordering) to the left and
-- try to solve the equation wrt this var.
mkCAtom :: Rel -> CTerm -> CTerm -> Either Bool CAtom
mkCAtom rel ct1 ct2 | elem rel [Eq, Neq] = 
    if null ctVars 
       then catom rel ct (CTerm [] $ zero $ width ct)
       else Right $ catomInSolvedForm rel (head ctVars) (ctermUMinus $ CTerm (tail ctVars) ctConst)
                    | otherwise          = catom rel ct1 ct2
    where ct@CTerm{..} = ctermPlus [ct1, ctermUMinus ct2]
          
catomInSolvedForm :: Rel -> (Integer, (Var,(Int,Int))) -> CTerm -> CAtom
catomInSolvedForm rel (i, v) ct = maybe (CAtom rel (CTerm [(i,v)] (zero $ width ct)) ct) 
                                        (\inv -> CAtom rel (CTerm [(1,v)] (zero $ width ct)) (ctermMul ct inv w))
                                        (constInvert i w)
    where w = width ct

catomSubst :: (Var,(Int,Int)) -> CTerm -> CAtom -> Either Bool CAtom
catomSubst v t (CAtom rel t1 t2) = mkCAtom rel (ctermSubst v t t1) (ctermSubst v t t2)

------------------------------------------------------------
-- Existential quantification
------------------------------------------------------------

exTerm :: [Var] -> [Atom] -> Maybe (Either Bool [CAtom])
exTerm vs as = 
   case catomsConj (map atomToCAtom as) of
        Left b    -> Just $ Left b
        Right cas -> {-trace ("exTerm: cas=" ++ show cas) $-} ex vs cas

ex :: [Var] -> [CAtom] -> Maybe (Either Bool [CAtom])
ex vs as = case catomsSliceVars as vs of
                (Left b, _)      -> Just (Left b)
                (Right as', vs') -> {-trace ("ex: sliced: " ++ show as' ++ " q:" ++ show vs') $-} ex' vs' as'

ex' :: [(Var, (Int,Int))] -> [CAtom] -> Maybe (Either Bool [CAtom])
ex' []     as = Just $ Right as
ex' (v:vs) as = case ex1 as v of
                     Nothing          -> Nothing
                     Just (Left b)    -> Just (Left b)
                     Just (Right as') -> ex' vs as'

ex1 :: [CAtom] -> (Var, (Int,Int)) -> Maybe (Either Bool [CAtom])
ex1 as v = fmap (\i -> catomsConj $ map (catomSubst v (fromJust $ sols !! i)) $ take i as ++ drop (i+1) as)
           $ findIndex isJust sols
    where sols = map (catomSolve v) as

-- Slice vars into non-overlapping ranges
catomsSliceVars :: [CAtom] -> [Var] -> (Either Bool [CAtom], [(Var,(Int,Int))])
catomsSliceVars as []     = (Right as,[])
catomsSliceVars as (v:vs) = case eas' of
                                 Left b  -> (Left b, (map (v,) ss))
                                 Right _ -> (as'', (map (v,) ss) ++ vs')
    where (eas', ss)  = catomsSliceVar as v
          (as'', vs') = catomsSliceVars (fromRight eas') vs

catomsSliceVar :: [CAtom] -> Var -> (Either Bool [CAtom], [(Int,Int)])
catomsSliceVar as v = ( applySubst as substs
                      , nub $ concatMap snd ss')
    where ss   = concatMap (catomFindVarSlices v) as
          ends = (\(ls, hs) -> (sort $ nub ls, sort $ nub hs)) $ unzip ss
          ss'  = zip ss $ map (partitionSlice ends) ss
          substs = map (\((l,h), subs) -> ((l,h), CTerm (addSlices subs) $ zero (h - l + 1)) ) ss'

          addSlices :: [(Int,Int)] -> [(Integer, (Var,(Int,Int)))]
          addSlices = fst . foldl' (\(vs, off) (l,h) -> ((1 `shiftL` off,(v,(l,h))):vs, off + (h - l + 1))) ([], 0)

          applySubst :: [CAtom] -> [((Int,Int), CTerm)] -> Either Bool [CAtom]
          applySubst as0 [] = Right as0
          applySubst as0 ((s, ct):subs) = case catomsConj $ map (catomSubst (v,s) ct) as0 of
                                               Left b    -> Left b
                                               Right _as -> applySubst _as subs


catomFindVarSlices :: Var -> CAtom -> [(Int,Int)]
catomFindVarSlices v (CAtom _ t1 t2) = concatMap (\(_,(v',s)) -> if' (v'==v) [s] []) $ ctVars t1 ++ ctVars t2

catomsConj :: [Either Bool CAtom] -> Either Bool [CAtom]
catomsConj = (\as -> if' (null as) (Left True)                 $
                     if' (any (== Left False) as) (Left False) (Right $ map fromRight as))
             . filter (/= Left True)

partitionSlice :: ([Int], [Int]) -> (Int,Int) -> [(Int,Int)]
partitionSlice (ls,hs) (l,h) = zip ls' hs'
    where ls' = sort $ nub $ filter (\l' -> l' >= l && l' <= h) $ ls ++ map (1+) hs
          hs' = sort $ nub $ filter (\h' -> h' >= l && h' <= h) $ hs ++ map (-1+) ls
