module Precedence where

import Data.List

type Precedence = [String]

showPrecedence :: Precedence -> String
showPrecedence p = intercalate " > " p

gtPrec :: Precedence -> String -> String -> Bool
gtPrec [] _ _ = False
gtPrec (f : fs) g h
  | f == g    = elem h fs
  | otherwise = gtPrec fs g h 

geqPrec :: Precedence -> String -> String -> Bool
geqPrec p f g = f == g || gtPrec p f g

largest :: Precedence -> String -> Bool
largest (g : _) f = f == g
largest _       _ = False
