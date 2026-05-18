module EKBO where

import Term
import Rule
import qualified Linear
import Precedence
import Lex

type Weight = ([(String, Int)], Int)

type Parameter = (Linear.Algebra, Weight, Precedence)

-- Pretty printers

showWeight :: Weight -> String
showWeight (wf, w0) =
  unlines (( "  w0 = " ++ show w0 ) :
           [ "  w(" ++ f ++ ") = " ++ show k | (f, k) <- wf ])

showParameter :: Parameter -> String
showParameter (m, w, p) =
  "EKBO with interpretations on natural numbers\n\n" ++
  Linear.showAlgebra m ++
  "\nweights\n\n" ++
  showWeight w ++
  "\nand precedence:\n\n" ++
  showPrecedence p ++ "\n"

-- EWPO

labeled :: Linear.Algebra -> String -> Bool
labeled a f
  | Just _ <- lookup (mark f) a = True
  | otherwise                   = False

-- s = f(s1,...,sm) >_B f(t1,...,tn) = t if 
--  - f > g, or 
--  - f is labeled and s# >_A t#
gtB :: Linear.Algebra -> Precedence -> Term -> Term -> Bool
gtB a p s@(F f _) t@(F g _) = 
  gtPrec p f g ||
  (f == g && labeled a f && Linear.gtA a (markTerm s) (markTerm t))
gtB _ _ _ _ = error "gtB"

-- s = f(s1,...,sm) >=_B f(t1,...,tn) = t if s# >_A t#
geqB :: Linear.Algebra -> Term -> Term -> Bool
geqB a s@(F f _) t@(F g _) =
  f == g &&
  (not (labeled a f) || (labeled a f && Linear.geqA a (markTerm s) (markTerm t)))
geqB _ _ _ = error "geqB"

-- EKBO

-- w(t)
weight :: Weight -> Term -> Int
weight (_, w0) (V _)    = w0
weight w@(wf, _) (F f ts)
  | Just n <- lookup f wf = n + sum [ weight w t | t <- ts ]
  | otherwise             = error "weight"

validWeight1 :: Weight -> (String, Int) -> Bool
validWeight1 (wf, w0) (f, n)
  | Just k <- lookup f wf = k >= 0 && (n /= 0 || k >= w0) 
  | otherwise             = False

validWeight :: Weight -> Signature -> Bool
validWeight w@(_, w0) sig = w0 > 0 && all (validWeight1 w) sig

admissible1 :: Parameter -> (String, Int) -> Bool
admissible1 (_, (wf, _), p) (f, n)
  | Just k <- lookup f wf = n /= 1 || k > 0 || largest p f
  | otherwise = error "admissible1"

admissible :: Parameter -> Signature -> Bool
admissible param sig = all (admissible1 param) sig

gtWeight :: Weight -> Term -> Term -> Bool
gtWeight w s t = weight w s > weight w t

-- exponentialForm t f x checks if t is of form f^n(x).
exponentialForm :: Term -> String -> String -> Bool
exponentialForm (V y)     _ x = x == y
exponentialForm (F g [t]) f x = f == g && exponentialForm t f x
exponentialForm _ _ _         = False

gtKBO :: Parameter -> Term -> Term -> Bool
gtKBO param@(_, w, _) s t = 
  nonduplicating (s, t) && 
  ws > wt || (ws >= wt && gtKBO' param s t) 
  where
    ws = weight w s
    wt = weight w t

gtKBO' :: Parameter -> Term -> Term -> Bool
gtKBO' _ t@(F f _) (V x) = exponentialForm t f x
gtKBO' param@(a, _, p) s@(F _ ss) t@(F _ ts) =
  gtB a p s t ||
  (geqB a s t && gtLex (gtKBO param) ss ts)
gtKBO' _ _ _ = False

gtEKBO :: Parameter -> Term -> Term -> Bool
gtEKBO param@(a, _, _) s t = Linear.geqA a s t && gtKBO param s t
