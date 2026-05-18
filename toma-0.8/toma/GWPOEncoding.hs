{-# LANGUAGE OverloadedStrings #-}
module GWPOEncoding where

import qualified Data.IntSet as IS
import qualified Data.Vector as V
import qualified Data.Text as T

import qualified GWPO
import Signature
import SMT
import Term
import qualified Algebra as A

varGt :: Term -> Term -> Formula
varGt s t = FVar ("gwpo_" <> tshow s <> "_" <> tshow t)

varGeqSq1 :: Term -> Term -> Formula
varGeqSq1 s t = FVar (">=1_" <> tshow s <> "_" <> tshow t)

varGtSq1 :: Term -> Term -> Formula
varGtSq1 s t = FVar (">1_" <> tshow s <> "_" <> tshow t)

varGeqSq2 :: Term -> Term -> Formula
varGeqSq2 s t = FVar (">=2_" <> tshow s <> "_" <> tshow t)

varGtSq2 :: Term -> Term -> Formula
varGtSq2 s t = FVar (">2_" <> tshow s <> "_" <> tshow t)

varPrec :: Int -> Exp
varPrec f = Var ("pr_" <> T.pack (show f))

geqSq1 :: A.Encoder -> Term -> Term -> Formula
geqSq1 e s t = A._geq e s t

gtSq1 :: A.Encoder -> Term -> Term -> Formula
gtSq1 e s t = A._gt e s t

geqSq2 :: A.Encoder -> Term -> Term -> Formula
geqSq2 _ (V _) _ = error "geqSq2 is not defined for variables"
geqSq2 _ _ (V _) = error "geqSq2 is not defined for variables"
geqSq2 e s@(F f _) t@(F g _) =
  disj [ A._gt' e s t, conj [ A._geq' e s t,  SMT.geq (varPrec f) (varPrec g) ] ]

gtSq2 :: A.Encoder -> Term -> Term -> Formula
gtSq2 _ (V _) _ = error "gtSq2 is not defined for variables"
gtSq2 _ _ (V _) = error "gtSq2 is not defined for variables"
gtSq2 e s@(F f _) t@(F g _) =
  disj [ A._gt' e s t, conj [ A._geq' e s t, SMT.gt (varPrec f) (varPrec g) ] ]

gt :: Term -> Term -> Formula
gt (V _) _ = bottom
gt s@(F _ _) t@(V x)
  | IS.member x (Term.variables s) = varGeqSq1 s t
  | otherwise = bottom
gt s@(F _ ss) t@(F _ ts) =
  disj [
    varGtSq1 s t,
    conj [
      varGeqSq1 s t,
      disj [
        disj [ if si == t then top else varGt si t  | si <- ss ],
        conj [
          conj [ varGt s tj | tj <- ts ],
          disj [ 
            varGtSq2 s t,
            conj [ varGeqSq2 s t, gtLex ss ts]
          ]
        ]
      ]
    ]
  ]
  where
    gtLex [] _ = bottom
    gtLex (_ : _) [] = top
    gtLex (s' : ss') (t' : ts')
      | s' == t' = gtLex ss' ts'
      | otherwise = varGt s' t'

-- possible: terms subject to comparison by >gwpo
side_condition :: A.Encoder -> [(Term, Term)] -> Signature -> Formula
side_condition e possible sig = conj $ 
  [ Distinct [ varPrec f | f <- [0..(V.length sig -1)] ] ] ++  -- total precedence
  [ conj [ A._side_condition e sig, A._simple e sig ] ] ++
  [ conj [
      implies (varGt t' u') (GWPOEncoding.gt t' u'),
      implies (varGeqSq1 t' u') (geqSq1 e t' u'),
      implies (varGtSq1 t' u') (gtSq1 e t' u'),
      if isVariable t' || isVariable u' then top else implies (varGeqSq2 t' u') (geqSq2 e t' u'),
      if isVariable t' || isVariable u' then top else implies (varGtSq2 t' u') (gtSq2 e t' u')
    ] | (t, u) <- possible, t' <- subterms t, u' <- subterms u
  ]

side_condition_wpo :: A.Encoder -> [(Term, Term)] -> Signature -> Formula
side_condition_wpo e possible sig =
  conj [
    A._no_marking e sig,
    side_condition e possible sig
  ]

decode :: A.Encoder -> Model -> Signature -> GWPO.Param
decode e m sig = (A._decode e m sig, pr)
  where
    pr = V.fromList [ evalExp m (varPrec f) | f <- [0..(V.length sig -1)] ]
