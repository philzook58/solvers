{-# LANGUAGE OverloadedStrings #-}
module KBOEncoding where

import qualified Data.Vector as V
import qualified Data.Text as T

import qualified KBO
import Signature
import SMT
import Term

varGt :: Term -> Term -> Formula
varGt s t = FVar ("k_" <> tshow s <> "_" <> tshow t)

varP :: Int -> Exp
varP f = Var ("p_" <> T.pack (show f))

varW0 :: Exp
varW0 = Var "w0"

varW :: Int -> Exp
varW f = Var ("w_" <> T.pack (show f))

varEqW :: Term -> Term -> Formula
varEqW s t = FVar ("w1_" <> tshow s <> "_" <> tshow t)

varGtW :: Term -> Term -> Formula
varGtW s t = FVar ("w2_" <> tshow s <> "_" <> tshow t)

weight :: Term -> Exp
weight (V _) = varW0
weight (F f ts) = SMT.plus (varW f : [ weight t | t <- ts ])

eqW :: Term -> Term -> Formula
eqW s t = SMT.eq (weight s) (weight t)

gtW :: Term -> Term -> Formula
gtW s t = SMT.gt (weight s) (weight t)

gt :: Term -> Term -> Formula
gt s t
  | duplicating (s, t) = bottom
gt (V _) _ = bottom
gt s@(F f _) t@(V x)
  | isIteration f x s = varEqW s t
  | otherwise = varGtW s t
gt s@(F f ss) t@(F g ts) =
  disj [
    varGtW s t,
    conj [
      varEqW s t,
      disj [ 
        SMT.gt (varP f) (varP g),
        if f == g then gtLex ss ts else bottom
      ]
    ]
  ]
  where
    gtLex [] _ = bottom
    gtLex (_ : _) [] = top
    gtLex (s' : ss') (t' : ts')
      | s' == t' = gtLex ss' ts'
      | otherwise = varGt s' t'

-- possible: terms subject to comparison by >kbo
side_condition :: [(Term, Term)] -> Signature -> Formula
side_condition possible sig = conj $ 
  [
    Distinct [ varP f | f <- [0..(V.length sig -1)] ],  -- total precedence
    SMT.gt varW0 (Val 0),
    conj [ SMT.geq (varW f) (Val 0) | f <- [0..(V.length sig-1)] ],
    conj [ SMT.geq (varW f) varW0 | f <- constants sig ],
    conj [ implies (SMT.eq (varW f) (Val 0)) (maximumP f) | f <- unaries sig ] -- admissibility
  ] ++
  [ conj [
      implies (varGt t' u') (KBOEncoding.gt t' u'),
      implies (varEqW t' u') (eqW t' u'),
      implies (varGtW t' u') (gtW t' u')
    ] | (t, u) <- possible, t' <- subterms t, u' <- subterms u
  ]
  where
    maximumP f = conj [ SMT.gt (varP f) (varP g) | g <- [0..(V.length sig -1)], f /= g ]

decode :: Model -> Signature -> KBO.Param
decode m sig = ((w0, w), pr)
  where
    pr = V.fromList [ evalExp m (varP f) | f <- [0..(V.length sig -1)] ]
    w = V.fromList [ evalExp m (varW f) | f <- [0..(V.length sig -1)] ]
    w0 = evalExp m varW0
