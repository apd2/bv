module Main where

import Data.List

import BV.Util
import BV.Types
import BV.Canonize

x16, y16 :: Term
x16 = TVar $ Var "x" 16
y16 = TVar $ Var "y" 16
z16 = TVar $ Var "z" 16

terms :: [Term]
terms = [ x16 .++ y16
        , TMul 256 (x16 .: (0,7)) 16
        , (x16 .++ y16) .: (8,23)
        , (x16 .: (0,7)) .++ (x16 .: (8,15))
        , TNeg $ x16 .: (0,7)
        , TNeg $ (x16 .++ (TConst $ mkConst 0 16)) .: (8,23)
        , TNeg $ ((TConst $ mkConst 0 16) .++ (TConst $ mkConst 0 16)) .: (8,23)
        , TNeg $ ((TConst $ mkConst 65535 16) .++ x16) .: (8,23)
        , TNeg $ (x16 .++ y16) .: (8,23)
        , TNeg $ (x16 .++ y16 .++ z16) .: (8,39)
        , (x16 .++ y16 .++ z16) .: (8,39)
        ]

atoms = [ x16 .== y16 
        , y16 .== x16 
        , (TConst $ zero 16) .== x16 
        , (TConst $ zero 16) .== (TNeg $ (x16 .++ y16) .: (8,23))
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
