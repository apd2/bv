module BV.Types(Var(..),
                Const(..),
                Rel(..),
                Term(..),
                Atom(..),
                CTerm(..),
                CAtom(..),
                ppSlice) where

import Text.PrettyPrint

import PP

class WithWidth a where
    width :: a -> Int

data Var = Var { vName  :: String
               , vWidth :: Int
               }

instance PP Var where
    pp Var{..} = pp vName <> (braces $ pp vWidth)

instance Show Var where
    show = render . pp

instance WithWidth Var where
    width = vWidth

data Const = Const { cVal   :: Integer
                   , cWidth :: Int 
                   }

instance PP Const where
    pp Const{..} = pp cVal <> (braces $ pp cWidth)

instance Show Const where
    show = render . pp

instance WithWidth Const where
    width = cWidth

data Rel = Eq | Neq | Lt | Lte deriving (Eq)

instance PP Rel where
    pp Eq  = text "=="
    pp Neq = text "!="
    pp Lt  = text "<"
    pp Lte = text "<="

instance Show Rel where
    show =  render . pp

-- Input term

ppSlice :: (Int,Int) -> Doc
ppSlice (l,h) = brackets $ if' (l==h) (pp l) (pp l <> char ':' <> pp h)

data Term = TConst  Const
            TVar    Var
            TSlice  Term (Int, Int)
            TConcat [Term]
            TNeg    Term
            TPlus   [Term]       -- all terms must be of equal width
            TMul    Integer Term Int

instance PP Term where
    pp (TConst  c)   = pp c
    pp (TVar    v)   = pp v
    pp (TSlice  t s) = pp t <> ppSlice s
    pp (TConcat [t]) = pp t
    pp (TConcat ts)  = parens $ hcat $ punctuate (text "++") $ map pp ts
    pp (TNeg    t)       = parens $ char '~' <> pp t
    pp (TPlus   ts)      = parens $ hcat $ punctuate (char '+') $ map pp ts
    pp (TMul    c t w)   = pp c <> char '*' <> pp t <> (braces $ pp w)

instance Show Term where
    show = render . pp

instance WithWidth Term where
    width (TConst c)       = width c
    width (TVar   v)       = width v
    width (TSlice _ (l,h)) = h - l + 1
    width (TConcat ts)     = sum $ map width ts
    width (TNeg t)         = width t
    width (TPlus (t:_))    = width t
    width (TMul _ _ w)     = w

-- Input atom
data Atom = Atom Rel Term Term

instance PP Atom where
    pp (Atom rel t1 t2) = pp t1 <+> pp rel <+> pp t2

instance Show Atom where
    show = render . pp

-- Term in canonical form (linear combination of vars)
data CTerm = CTerm { ctVars  :: [(Integer,(Var,(Int,Int)))]
                   , ctConst :: Const
                   }

instance PP CTerm where
    pp (CTerm [] c)             = pp c
    pp (CTerm ts c) | cVal c == 0 = tstxt
                    | otherwise   = tstxt <> char '+' <> pp c
                    where tstxt = hcat 
                                  $ punctuate (char '+') 
                                  $ map (\(m,(v,(l,h))) -> (if' (m==1) empty (pp m <> char '*')) 
                                                           <> pp v
                                                           <> if' (l==0 && h==width v - 1) empty (ppSlice (l,h))) ts

instance Show CTerm where
    show = render . pp

instance WithWidth CTerm where
    width (CTerm _ c) = width c

-- Atom in canonical form
-- Truly canonical form requires that the LHS CTerm is a naked variable
data CAtom = CAtom Rel CTerm CTerm

instance PP CAtom where
    pp (CAtom r t1 t2) = pp t1 <+> pp rel <+> pp t2 

instance Show CAtom where
    show = render . pp
