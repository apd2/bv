module Main where

import Data.List

import BV.Util
import BV.Types
import BV.Canonize

vx16, vy16, vz16 :: Var
vx16 = Var "x" 16
vy16 = Var "y" 16
vz16 = Var "z" 16

x16, y16, z16 :: Term
x16  = TVar vx16
y16  = TVar vy16
z16  = TVar vz16


terms :: [Term]
terms = [ x16 .++ y16
        , TMul 256 (x16 .: (0,7)) 16
        , (x16 .++ y16) .: (8,23)
        , (x16 .: (0,7)) .++ (x16 .: (8,15))
        , TNeg $ x16 .: (0,7)
        , TNeg $ (x16 .++ (tConst 0 16)) .: (8,23)
        , TNeg $ ((tConst 0 16) .++ (tConst 0 16)) .: (8,23)
        , TNeg $ (tConst 65535 16 .++ x16) .: (8,23)
        , TNeg $ (x16 .++ y16) .: (8,23)
        , TNeg $ (x16 .++ y16 .++ z16) .: (8,39)
        , (x16 .++ y16 .++ z16) .: (8,39)
        ]

atoms :: [Atom]
atoms = [ x16 .== y16 
        , y16 .== x16 
        , (TConst $ zero 16) .== x16 
        , (TConst $ zero 16) .== (TNeg $ (x16 .++ y16) .: (8,23))
        ]

formulas :: [([Var],[Atom])]
formulas = [ ([vx16], [x16 .== y16])
           , ([vx16], [x16 ./= y16])
           , ([vx16], [x16 ./= y16, x16 .== z16])
           , ([vx16], [(x16 .: (0,7)) .== ((y16 .+ tConst 4 16) .: (0,7)), x16 .== (z16 .+ tConst 8 16)])
           , ([vx16], [x16 .== (y16 .+ tConst 4 16), x16 .== (z16 .+ tConst 8 16)])
           , ([Var "$tmp1" 12], [(TVar (Var "$tmp1" 12)) .< (TVar (Var "used" 12)), (TPlus [TVar (Var "used" 12), tConst 4095 12]) .<= (TVar (Var "$tmp1" 12))])
           ]


main :: IO ()
main = do
    let cts = map termToCTerm terms
    putStrLn $ "termToCTerm test\n" ++
             ( intercalate "\n" 
             $ map (\(t,ct) -> show t ++ " --> " ++ show ct) 
             $ zip terms cts)

    let cas = map atomToCAtom atoms
    putStrLn $ "\natomToCAtom test\n" ++
             ( intercalate "\n" 
             $ map (\(a,ca) -> show a ++ " --> " ++ show ca) 
             $ zip atoms cas)

    let res = map (uncurry exTerm) formulas
    putStrLn $ "\nexistential quantification test\n" ++
             ( intercalate "\n"
             $ map (\((vs,as), r) -> "Ex " ++ (intercalate "," $ map show vs) ++ "." ++ (intercalate " /\\ " $ map show as) ++ " = " ++ show r)
             $ zip formulas res)
