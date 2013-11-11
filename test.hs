module Main where

import Data.List

import BV.Types
import BV.Canonize

x16, y16 :: Term
x16 = TVar $ Var "x" 16
y16 = TVar $ Var "y" 16

terms :: [Term]
terms = [ x16 .++ y16
        , (x16 .++ y16) .: (8,23)
        , (x16 .: (0,7)) .++ (x16 .: (8,15))
        , TNeg $ (x16 .++ y16) .: (8,23)
        ]

main :: IO ()
main = do
    let cts = map termToCTerm terms
    putStrLn $ "termToCTerm test\n" ++
             ( intercalate "\n" 
             $ map (\(t,ct) -> show t ++ " --> " ++ show ct) 
             $ zip terms cts)
