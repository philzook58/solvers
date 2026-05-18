{-# LANGUAGE OverloadedStrings #-}
module MGWPOEncoding where

import qualified Data.IntSet as IS

import qualified MGWPO
import Signature
import SMT
import Term
import qualified Algebra as A

varGt' :: Term -> Term -> Formula
varGt' s t = FVar ("gwpo_" <> tshow s <> "_" <> tshow t)

-- gwpo
gt' :: (A.Encoder, A.Encoder) -> Term -> Term -> Formula
gt' _ (V _) _ = bottom
gt' (e1, _) s@(F _ _) t@(V x)
  | IS.member x (Term.variables s) = A._geq e1 s t
  | otherwise = bottom
gt' (e1, e2) s@(F _ ss) t@(F _ ts) =
  disj [
    A._gt e1 s t,
    conj [
      A._geq e1 s t,
      disj [
        disj [ if si == t then top else varGt' si t  | si <- ss ],
        conj [
          conj [ varGt' s tj | tj <- ts ],
          disj [ 
            A._gt' e2 s t,
            conj [ A._geq' e2 s t, gtLex ss ts]
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
      | otherwise = varGt' s' t'

gt :: (A.Encoder, A.Encoder) -> Term -> Term -> Formula
gt es@(_, e2) s t = conj [ A._geq e2 s t, gt' es s t ]

-- possible: terms subject to comparison by >gwpo
side_condition :: (A.Encoder, A.Encoder) -> [(Term, Term)] -> Signature -> Formula
side_condition (e1, e2) possible sig = conj $ 
  [ conj [ A._side_condition e1 sig, A._no_marking e1 sig, A._simple e1 sig ] ] ++
  [ A._side_condition e2 sig ] ++
  [ conj [
      implies (varGt' t' u') (MGWPOEncoding.gt' (e1, e2) t' u')
    ] | (t, u) <- possible, t' <- subterms t, u' <- subterms u
  ]

decode :: (A.Encoder, A.Encoder) -> Model -> Signature -> MGWPO.Param
decode (e1, e2) m sig = (A._decode e1 m sig, A._decode e2 m sig)
