module KBO where

import Data.List
import Term
import Rule
import Precedence
import Lex

type Weight = ([(String, Int)], Int)

type Parameter = (Weight, Precedence)

showWeight :: Weight -> String
showWeight (wf, w0) =
  unlines (( "  w0 = " ++ show w0 ) :
           [ "  w(" ++ f ++ ") = " ++ show k | (f, k) <- wf ])

showParameter :: Parameter -> String
showParameter (w, p) =
  "KBO with weight\n\n" ++
  showWeight w ++
  "\nand precedence:\n\n" ++
  "  " ++ intercalate " > " p ++ "\n"

-- exponentialForm t f x checks if t is of form f^n(x).
exponentialForm :: Term -> String -> String -> Bool
exponentialForm (V y)     _ x = x == y
exponentialForm (F g [t]) f x = f == g && exponentialForm t f x
exponentialForm _ _ _         = False

-- w(t)
weight :: Weight -> Term -> Int
weight (_, w0) (V _)    = w0
weight w@(wf, _) (F f ts)
  | Just n <- lookup f wf = n + sum [ weight w t | t <- ts ]
  | otherwise             = error "weight"

gtKBO :: Parameter -> Term -> Term -> Bool
gtKBO param@(w, _) s t = 
  nonduplicating (s, t) && 
  ws > wt || (ws >= wt && gtKBO' param s t) 
  where
    ws = weight w s
    wt = weight w t

gtKBO' :: Parameter -> Term -> Term -> Bool
gtKBO' _ t@(F f _) (V x) = exponentialForm t f x
gtKBO' param@(_, p) (F f ss) (F g ts) =
  gtPrec p f g ||
  (f == g && gtLex (gtKBO param) ss ts)
gtKBO' _ _ _ = False
