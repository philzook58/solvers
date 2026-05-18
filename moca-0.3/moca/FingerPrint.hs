module FingerPrint where

import Terms
import Rules
import Substitutions
import Data.List

import Debug.Trace


data Feature = FSymbol String | A | B | N deriving Eq
instance Show Feature where
    show (FSymbol f)  = f
    show A            = "A"
    show B            = "B"
    show N            = "N"
showFeatures :: [Feature] -> String
showFeatures fs = intercalate " | " [ show f | f <- fs]

features :: Term -> [Feature]
features (V x)                       = [A,           B,          B]
features (F f [])                    = [FSymbol f,   N,          N]
features (F f ((V x):_))             = [FSymbol f,   A,          B]
features (F f ((F g []):_))          = [FSymbol f,   FSymbol g,  N]
features (F f ((F g ((V x):_)):_))   = [FSymbol f,   FSymbol g,  A]
features (F f ((F g ((F h _):_)):_)) = [FSymbol f,   FSymbol g,  FSymbol h]
