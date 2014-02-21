-- Convert bit-vector terms and atoms to canonical form.
-- Based on: Barrett, Dill, Levitt "A Decision Procedure for Bit-Vector Arithmetic", 1998

{-# LANGUAGE RecordWildCards, TupleSections #-}

module BV.Canonize(termToCTerm,
                   atomToCAtoms,
                   ex,
                   exTerm) where

import Data.Bits
import Data.List
import Data.Maybe
import Debug.Trace
import Control.Applicative hiding (Const)

import Util hiding (trace)
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
termToCTerm t = {-trace ("termToCTerm: t=" ++ show t ++ " simplified=" ++ show tsimp) $-} termToCTerm' tsimp (width tsimp)
    where tsimp = termSimplify $ termValidate t

-- The second argument specifies width of the result.  It is less than or equal
-- to width of the first argument.  
termToCTerm' :: Term -> Int -> CTerm
termToCTerm' (TConst c)       u = CTerm [] $ constSlice (cVal c) (0, u - 1)
termToCTerm' (TVar v)         u = CTerm [(1,(v,(0,u-1)))] $ zero u
termToCTerm' (TSlice t (l,hh)) u = {-trace ("termToCTerm' " ++ show (TSlice t (l,hh)) ++ "=" ++ show t' ++ "(" ++ show (width t') ++ ")")-} t'
    where h = l + u - 1
          ct = termToCTerm' t (h+1)
          t' = fromMaybe (error $ "BV.termToCTerm: cannot handle slice [" ++ show l ++ ":" ++ show h ++ "] of term " ++ show ct)
                         (ctermSlice ct (l,h))
termToCTerm' (TConcat ts)     u = ctermPlus ts'' u
    where (_, ts'') = foldl' (\(off, cts) t -> 
                               let ct@CTerm{..} = termToCTerm' t (min (width t) (u-off))
                                   w' = width ct
                                   ((i,(v,(l',h'))) :_) = ctVars
                                   ct' = if' (length ctVars == 0) 
                                             (ctermMul ct (1 `shiftL` off) u) $
                                         if' (length ctVars == 1 && cVal ctConst == 0 && h' - l' < width ctConst) 
                                             (ctermMul ct (1 `shiftL` off) u) $
                                         if' (length ctVars == 1 && 
                                              h' - l' < width ctConst && 
                                              i == (-1) `mod2` w' && 
                                              ctConst == mkConst (-1) w')
                                             (CTerm [(((-1)*(1 `shiftL` off)) `mod2` u, (v,(l',h')))] $ mkConst (-1* (1 + ((-1) `mod2` off) + (((-1) `mod2` (u-off-w')) `shiftL` (off+w')))) u)
                                             (error $ "termToCTerm: cannot handle " ++ show (TConcat ts))
                               in if' (off >= u) (off+w', cts) (off+w', ct':cts))
                             (0,[]) ts

termToCTerm' (TNeg t)         u = {-trace ("termToCTerm' " ++ show (TNeg t) ++ "=" ++ show ct')-} ct'
    where ct = termToCTerm' t u
          ct' = ctermPlus [ctermMul ct (-1) u, CTerm [] (mkConst (-1) u)] u

termToCTerm' (TPlus ts)       u = ctermPlus (map (\t -> termToCTerm' t u) ts) u
termToCTerm' (TMul c t w)     u = ctermMul (termToCTerm' t (minimum [u,w,width t])) c u

------------------------------------------------------------
-- Atom canonization
------------------------------------------------------------
atomToCAtoms :: Atom -> [[CAtom]]
atomToCAtoms a = case atomToCAtom a of
                      Left False -> []
                      Left True  -> [[]]
                      Right a'   -> catomSimplify a'

atomToCAtom :: Atom -> Either Bool CAtom
atomToCAtom (Atom rel t1 t2) = mkCAtom rel' ct1 ct2'
    where w = max (width t1) (width t2)
          t1' = termExt t1 w
          t2' = termExt t2 w
          ct1 = termToCTerm t1'
          ct2 = termToCTerm t2'
          (ct2', rel') = if width ct1 == 1 && rel == Neq
                            then (termToCTerm $ TNeg t2', Eq)
                            else (ct2, rel)

catomSubst :: (Var,(Int,Int)) -> CTerm -> CAtom -> Either Bool CAtom
catomSubst v t (CAtom rel t1 t2) = mkCAtom rel (ctermSubst v t t1) (ctermSubst v t t2)

------------------------------------------------------------
-- Existential quantification
------------------------------------------------------------

exTerm :: [Var] -> [Atom] -> Maybe (Either Bool [[CAtom]])
exTerm vs as = trace ("exTerm " ++ show vs ++ " " ++ show as) $
   case catomsConj (map atomToCAtom as) of
        Left b    -> Just $ Left b
        Right cas -> ex vs cas

ex :: [Var] -> [CAtom] -> Maybe (Either Bool [[CAtom]])
ex vs as = case catomsSliceVars as vs of
                (Left b, _)      -> Just (Left b)
                (Right as', vs') -> case ex' vs' as' of
                                         Nothing          -> Nothing
                                         Just (Left b)    -> Just $ Left b
                                         Just (Right ass) -> Just $ Right $ concatMap simplifyCAtoms ass

ex' :: [(Var, (Int,Int))] -> [CAtom] -> Maybe (Either Bool [[CAtom]])
ex' [] as = Just $ Right [as]
ex' vs as = -- find a variable that can be quantified away
            case findIndex isJust quant_res of
                 Nothing -> -- if all remaining variables occur only in inequalities, 
                            -- then return remaining atoms (without quantified variables)
                            let (withoutvs, withvs) = partition (\(CAtom _ t1 t2) -> null $ intersect vs (map snd $ (ctVars t1 ++ ctVars t2))) as in
                            if all (\(CAtom r _ _) -> r == Neq) withvs
                               then if' (null withoutvs) (Just $ Left True) (Just $ Right [withoutvs])
                               else exInequalities vs as
                 Just i  -> case fromJust $ quant_res !! i of
                                 Left b    -> Just (Left b)
                                 Right as' -> trace ("quantifying " ++ (show $ vs !! i) ++ " -> " ++ show as') $
                                              ex' (take i vs ++ drop (i+1) vs) as'
    where quant_res = map (ex1 as) vs

ex1 :: [CAtom] -> (Var, (Int,Int)) -> Maybe (Either Bool [CAtom])
ex1 as v | null withv                      = Just $ Right as
         | any (== Just (Left False)) sols = Just $ Left False
         | otherwise = 
         fmap (\i -> let Just (Right (ct, catoms)) = sols !! i in
                     catomsConj $ (map (catomSubst v ct) $ take i sorted ++ drop (i+1) sorted) ++ map Right catoms ++ map Right withoutv)
              $ findIndex isJust sols
    where (withv, withoutv) = partition (\CAtom{..} -> any (== v) $ map snd $ ctVars catomLHS ++ ctVars catomRHS) as
          groups = reverse $ sortAndGroup width withv
          sorted = concat groups
          sols = map (catomSolve v) $ head groups

-- All remaining variables are in !=/</> atoms.
-- Try to solve using heuristics
exInequalities :: [(Var, (Int,Int))] -> [CAtom] -> Maybe (Either Bool [[CAtom]])
exInequalities [] as = Just $ Right [as]
exInequalities vs as = 
    -- Find a variable that only occurs naked on the RHS or LHS side of inequalities
    let isIn v CTerm{..} = (any ((==v) . snd) ctVars)
        mv = find (\v -> all (\CAtom{..} -> (isNakedIn v catomLHS && (not $ isIn v catomRHS)) || 
                                            (isNakedIn v catomRHS && (not $ isIn v catomLHS)) || 
                                            (not $ isIn v catomLHS || isIn v catomRHS)) as) vs
    in case mv of
            Nothing -> Nothing
            Just v  -> let vs' = filter (/= v) vs 
                           ass = filter (/= Left False) $ map (eliminateNaked v) $ map nub $ concatMap (stripConstants v) $ expandNeq v as in
                       if' (null ass) (Just $ Left False) $
                       if' (any (== Left True) ass) (Just $ Left True)
                           (let sols = map (\(Right as') -> ex' vs' as') ass in
                            if' (any isNothing sols) Nothing $
                            if' (any (== Just (Left True)) sols) (Just $ Left True) $
                            Just $ Right (concatMap (fromRight . fromJust) sols))

isNakedIn :: (Var, (Int,Int)) -> CTerm -> Bool
isNakedIn v CTerm{..} = (length ctVars == 1) && (head ctVars == (1, v))

expandNeq :: (Var,(Int,Int)) -> [CAtom] -> [[CAtom]]
expandNeq _ []               = [[]]
expandNeq v (a@CAtom{..}:as) = concatMap (\a_ -> map (a_:) as') a'
    where asplit = map fromRight $ filter (/= Left False) [mkCAtom Lt catomRHS catomLHS, mkCAtom Lt catomLHS catomRHS]
          a' = if' (catomRel == Neq && ((isNakedIn v catomLHS) || (isNakedIn v catomRHS))) 
                   asplit [a]
          as' = expandNeq v as

-- Transform inequalities in the form t < x + const into up to three systems of inequalities, 
-- where the constant is moved to the LHS.
stripConstants :: (Var,(Int,Int)) -> [CAtom] -> [[CAtom]]
stripConstants _ []               = [[]]
stripConstants v (a@CAtom{..}:as) | (not $ isNakedIn v catomLHS || isNakedIn v catomRHS) = map (a:) as'
                                  | isNakedIn v catomRHS                                 = concatMap (\as_ -> map (as_++) as') $ stripConstantsR a
                                  | isNakedIn v catomLHS                                 = concatMap (\as_ -> map (as_++) as') $ stripConstantsL a
    where as'  = stripConstants v as
          w    = width catomRHS

-- The input atom has the variable to be stripped on the RHS
stripConstantsR :: CAtom -> [[CAtom]]
stripConstantsR a | cVal c == 0  = [[a]]
                  | otherwise    = {-trace ("stripConstantsR " ++ show a ++ " = " ++ show res)-} res
    where -- -c <= x /\ t < c /\ t-c `r` x
          mas1 = mkCAtomConj [(Lte, ctermUMinus cterm, xterm), (Lt, t, cterm), (r, ctermMinus t cterm, xterm)]
          -- x < -c /\ t > c /\ t-c `r` x
          mas2 = mkCAtomConj [(Lt, xterm, ctermUMinus cterm),  (Lt, cterm, t), (r, ctermMinus t cterm, xterm)]
          -- x < -c /\ t <= c 
          mas3 = mkCAtomConj [(Lt, xterm, ctermUMinus cterm),  (Lte, t, cterm)]
          CAtom r t (CTerm x c) = a
          xterm = CTerm x $ zero $ width a
          cterm = CTerm [] c
          res = catMaybes [mas1,mas2,mas3] 

-- The input atom has the variable to be stripped on the LHS
stripConstantsL :: CAtom -> [[CAtom]]
stripConstantsL a | cVal c == 0  = [[a]]
                  | otherwise    = {-trace ("stripConstantsL " ++ show a ++ " = " ++ show res)-} res
    where -- x < -c /\ c <= t /\ x `r` t - c
          mas1 = mkCAtomConj [(Lt, xterm, ctermUMinus cterm), (Lte, cterm, t), (r, xterm, ctermMinus t cterm)]
          -- -c <= x /\ t < c  /\ x `r` t - c
          mas2 = mkCAtomConj [(Lte, ctermUMinus cterm, xterm), (Lt, t, cterm), (r, xterm, ctermMinus t cterm)]
          -- -c <= x /\ c <= t
          mas3 = mkCAtomConj [(Lte, ctermUMinus cterm, xterm), (Lte, cterm, t)]
          CAtom r (CTerm x c) t = a
          xterm = CTerm x $ zero $ width a
          cterm = CTerm [] c
          res = catMaybes [mas1,mas2,mas3]

simplifyCAtoms :: [CAtom] -> [[CAtom]]
simplifyCAtoms []     = [[]]
simplifyCAtoms (a:as) = map nub $ concatMap (\as_ -> map (as_++) as') a'
    where as' = simplifyCAtoms as
          a' = catomSimplify a

catomSimplify :: CAtom -> [[CAtom]]
catomSimplify a@CAtom{..} = 
    if' ((elem catomRel [Lt, Lte]) && (null $ ctVars catomLHS)) (stripConstantsR a) $
    if' ((elem catomRel [Lt, Lte]) && (null $ ctVars catomRHS)) (stripConstantsL a)
        [[a]]

-- Eliminate naked variable by constructing all pairwise combinations
-- of terms t1 < t2 such that t1 < v < r2
eliminateNaked :: (Var, (Int,Int)) -> [CAtom] -> Either Bool [CAtom]
eliminateNaked v as = if' (any (== Left False) as') (Left False) 
                          (Right $ other ++ map fromRight (filter (/= Left True) as'))
    where
    (lts, rts, other) = foldl' (\(lts', rts', other') a@CAtom{..} -> if' (isNakedIn v catomLHS) (lts', (catomRHS, catomRel):rts', other') $
                                                                     if' (isNakedIn v catomRHS) ((catomLHS, catomRel): lts', rts', other')
                                                                     (lts', rts', a:other'))
                        ([],[],[]) as
    -- in case v occurs on one side of inequalities only, just make sure that,
    -- if the inequality is strict, then the term on the other side is not 
    -- 0 (for v<t) or -1 (for t<v)
    as' = if' (null lts) (mapMaybe (\(t,r) -> if' (r == Lte) Nothing (Just $ mkCAtom Lt (CTerm [] (zero $ width t)) t)) rts) $
          if' (null rts) (mapMaybe (\(t,r) -> if' (r == Lte) Nothing (Just $ mkCAtom Lt t (CTerm [] $ mkConst (-1) $ width t))) lts) $
          concat $ combine <$> lts <*> rts
    combine (t1, Lt)  (t2, Lte) = [mkCAtom Lt  t1 t2]
    combine (t1, Lte) (t2, Lt)  = [mkCAtom Lt  t1 t2]
    combine (t1, Lte) (t2, Lte) = [mkCAtom Lte t1 t2]
    combine (t1, Lt)  (t2, Lt)  = let w = width t1 in
                                  [mkCAtom Lt (ctermPlus [t1, CTerm [] (mkConst 1 w)] w) t2, 
                                   mkCAtom Lt t1 (CTerm [] $ mkConst (-1) w)]


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
          substs = map (\((l,h), subs) -> ((l,h), addSlices subs)) ss'

          addSlices :: [(Int,Int)] -> [(Integer, (Var,(Int,Int)))]
          addSlices = fst . foldl' (\(vs, off) (l,h) -> ((1 `shiftL` off,(v,(l,h))):vs, off + (h - l + 1))) ([], 0)

          applySubst :: [CAtom] -> [((Int,Int), [(Integer, (Var,(Int,Int)))])] -> Either Bool [CAtom]
          applySubst as0 [] = Right as0
          applySubst as0 ((s, ct):subs) = case catomsConj $ map (\a -> catomSubst (v,s) (CTerm ct $ zero $ width a) a) as0 of
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
