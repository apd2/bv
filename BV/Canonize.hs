-- Convert bit-vector terms and atoms to canonical form.
-- Based on: Barrett, Dill, Levitt "A Decision Procedure for Bit-Vector Arithmetic", 1998

module BV.Canonize(termCanonize,
                   atomCanonize,
                   ex) where

import Data.List

import Util
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
termValidate t@(TPlus ts)           = assert ((not $ null ts) && all (((width $ head ts) ==) . width) $ tail ts) ("invalid sum: " ++ show t) 
                                      $ TPlus $ map termValidate ts
termValidate t@(TMul c t' w)        = assert (c `mod2` w == c) ("invalid multiplication: " ++ show t) $ TMul c (termValidate t') w

-----------------------------------------------------------------
-- Simplification
-----------------------------------------------------------------

-- Slices blow up canonization -- bring them all the way in if possible
termSimplify :: Term -> Term
termSimplify t@(TConst _)      = t
termSimplify t@(TVar _)        = t
termSimplify   (TConcat [t])   = termSimplify t
termSimplify   (TConcat ts)    = TConcat 
                                 $ mergeConcat
                                 $ concatMap (\t' -> case t' of
                                                          TConcat ts' -> ts'
                                                          _           -> [t'])
                                 $ map termSimplify ts
termSimplify   (TNeg t)        = case termSimplify t of
                                      TNeg t'    -> t'
                                      TConst c   -> constNeg c
                                      TConcat ts -> TConcat $ map (termSimplify . TNeg) ts
                                      t'         -> TNeg t'
termSimplify t@(TPlus ts)      = case ts' of
                                      [t'] -> t'
                                      _    -> TPlus ts'
                                 where ts' = groupSum
                                             $ concatMap (\t' -> case t' of
                                                                      TPlus ts'' -> ts''
                                                                      _          -> [t'])
                                             $ map termSimplify t
termSimplify   (TMul c t w) | c == 0                 = zero w
                            | c == 1 && width t == w = termSimplify t
                            | otherwise = case termSimplify t of
                                               TConst cn       -> constMul c cn w
                                               TMul   c' t' w' -> termSimplify $ TMul ((c * c') `mod2` w) t' w
                                               t'              -> TMul c t' w

termSimplify   (TSlice t (l,h)) | l == 0 && h == width t - 1 = termSimplify t
termSimplify                    | otherwise = case termSimplify t of
                                                   TConst c         -> TConst $ constSlice (cVal c) (l,h)
                                                   TConcat ts       -> termSimplify $ TConcat $ concatSlice ts (l,h)
                                                   TNeg t'          -> termSimplify $ TNeg $ TSlice t' (l,h)
                                                   TSlice t' (l',_) -> termSimplify $ TSlice t' (l+l',h+l')
                                                   t'               -> TSlice t' s

concatSlice :: [Term] -> (Int,Int) -> [Term]
concatSlice []     _                    = []
concatSlice (t:ts) (l,h) | l >= width t = concatSlice ts (l - width t, h - width t)
                         | h < 0        = []
                         | otherwise    = TSlice t (max l 0, min h (twidth t - 1)) : concatSlice ts (l - width t, h - width t)

mergeConcat :: [Term] -> [Term]
mergeConcat [t]        = [t]
mergeConcat (t1:t2:ts) = 
    case (t1, t2) of
         (TSlice t1' (l1,h1), TSlice t2' (l2,h2)) -> if' (t1' == t2') && (l2 == h1 + 1)
                                                         (mergeConcat (termSimplify $ TSlice t1' (l1,h2)):ts)
                                                         (t1:mergeConcat (t2:ts)) 
         (TConst c1, TConst c2)                   -> constConcat c1 c2
         _                                        -> t1:mergeConcat (t2:ts)

groupSum :: [Term] -> [Term]
groupSum ts = case ts'' ++ tconst of
                   []    -> zero w
                   ts''' -> ts'''
    where w = width $ head ts
          (consts, ts') = partition isTermConst ts
          tconst = case (sum $ map cVal consts) `mod2` w of
                        0 -> []
                        c -> [TConst c w]
          ts'' = groupSum' ts'


groupSum' :: [Term] -> [Term]
groupSum' []                  = []
groupSum' ts@((TMul c t w):_) = maybeToList t' ++ (groupSum' ts')
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
                   1 -> t
                   _ -> TMul coef t w

-----------------------------------------------------------------
-- Term canonization
-----------------------------------------------------------------

termCanonize :: Term -> CTerm
termCanonize = termToCTerm . termSimplify . termValidate

termToCTerm :: Term -> CTerm
termToCTerm (TConst c)       = CTerm [] 
termToCTerm (TVar v)         = CTerm [(1,(v,(0, width v - 1)))] (zero $ width v)
termToCTerm (TSlice t (l,h)) = t'
    where w = h - l + 1
          ct@(CTerm ts c) = termToCTerm t
          t' = if' (null ts) 
                   (CTerm [] $ constSlice (cVal c) (l,h))                                   $
               if' (l == 0)
                   (CTerm (map (\(i,v) -> (i `mod2` w, v)) ts) $ constSlice (cVal c) (l,h)) $
               if' (length ts@((i,v):_) == 1 && cVal c == 0 && i == 1)
                   (CTerm [1,(v,(l,h))] c)
                   (error $ "BV.termCanonize: cannot handle slice [" ++ show l ++ ":" ++ show h ++ "] of term " ++ show ct)
termToCTerm (TConcat ts)      = ctermPlus ts''
    where ts' = map termToCTerm ts
          w = sum $ map width ts'
          (ts'', _) = foldl' (\(off, cts) ct -> (off+width ct, ctermMul ct (1 `shiftL` width ct)) w) 
                             (0,[]) ts'

termToCTerm (TNeg t)          = ct'
    where ct = termToCTerm t
          w = width ct
          ct' = ctermPlus [(ctermMul ct (-1) w), CTerm [] (const (-1) w)]

termToCTerm (TPlus ts)        = ctermPlus $ map termToCTerm ts
termToCTerm (TMul c t w)      = ctermMul (termToCTerm t) c w

------------------------------------------------------------
-- Atom canonization
------------------------------------------------------------

atomToCAtom :: Atom -> Either Bool CAtom
atomToCAtom (Atom rel t1 t2) = mkCAtom rel ct1 ct2
    where ct1 = termCanonize t1
          ct2 = termCanonize t2

-- Move the first variable (in var ordering) to the left and
-- try to solve the equation wrt this var.
mkCAtom :: Rel -> CTerm -> CTerm -> Either Bool CAtom
mkCAtom rel ct1 ct2 | elem rel [Eq, Neq] = 
    if (null ctVars) 
       then catom rel ct (CTerm [] $ zero $ width ct)
       else Right $ catomInSolvedForm rel (head ctVars) (ctermUMinus $ CTerm (tail ctVars) ctConst))
    where w = width ct1
          ct@CTerm{..} = ctermPlus [ct1, ctermUMinus ct2]
                    | otherwise          = catom rel ct1 ct2
          
catomInSolvedForm :: Rel -> (Integer, (Var,(Int,Int))) -> CTerm -> CAtom
catomInSolvedForm rel (i, v) ct | odd a     = CAtom rel (CTerm [(1,v)] (zero $ width ct)) (ctermMul ct (constInvert i w) w)
                                | otherwise = CAtom rel (CTerm [(i,v)] (zero $ width ct)) ct
    where w = width ct

catomSubst :: (Var,(Int,Int)) -> CTerm -> CAtom -> Either Bool CAtom
catomSubst v t (CAtom rel t1 t2) = mkCAtom rel (ctermSubst v t t1) (ctermSubst v t t2)

------------------------------------------------------------
-- Existential quantification
------------------------------------------------------------

ex :: [Var] -> [CAtom] -> Maybe [CAtom]
ex vs as = ex' vs' as'
    where (as', vs') = catomsSliceVars as vs

ex' :: [(Var, (Int,Int))] -> [CAtom] -> Maybe (Either Bool [CAtom])
ex' []     as = Just $ Right as
ex' (v:vs) as = case ex1 as v of
                     Nothing          -> Nothing
                     Just (Left b)    -> Just (Left b)
                     Just (Right as') -> ex' vs as'

ex1 :: [CAtom] -> (Var, (Int,Int)) -> Maybe (Either Bool [CAtom])
ex1 as v = fmap (\i -> (\as -> if' (null as) (Left True)                 $
                               if' (any (== Left False) as) (Left False) $
                               (Right $ map fromRight as))
                       $ filter (/= Left True)
                       $ map (catomSubst v (fromJust $ sols !! i)) $ take i as ++ drop (i+1) as)
           $ findIndex isJust sols
    where sols = map (catomSolve v) as

-- Slice vars into non-overlapping ranges and 
catomsSliceVars :: [CAtom] -> [Var] -> ([CAtom], [(Var,(Int,Int))])
catomsSliceVars as []     = (as,[])
catomsSliceVars as (v:vs) = (as'', (map (v,) ss) ++ vs')
    where (as', ss)   = catomsSliceVar as v
          (as'', vs') = catomsSliceVars as' vs

catomsSliceVar :: [CAtom] -> Var -> ([CAtom], [(Int,Int)])
catomsSliceVar as v = foldl' (\as' ((v,s),ct) -> map (catomSubst (v,s) ct) as') as substs
    where ss   = concatMap (catomFindVarSlices v) as
          ends = nub $ sort $ concatMap (\(l,h) -> [l,h]) ss
          ss'  = zip ss $ map (partitionSlice ends) ss
          substs = map (\((l,h), subs) -> ((v,(l,h)), CTerm (addSlices subs) $ zero (h - l + 1)) ) ss'
          addSlices :: [(Int,Int)] -> [(Integer, (Var,(Int,Int)))]
          addSlices = foldl' (\(vs, off) (l,h) -> ((1 `shiftL` off,(v,(l,h))):vs, off + (h - l + 1))) ([], 0)

-- ends is assumed to be sorted
partitionSlice :: [Int] -> (Int,Int) -> [(Int,Int)]
partitionSlice ends (l,h) = pairs $ filter (\i -> i>=l && i<=h) ends
    where pairs []         = []
          pairs [_]        = []
          pairs (i1:i2:is) = (i1,i2) : pairs (i2:is)
