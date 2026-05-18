{-# LANGUAGE OverloadedStrings #-}
module SPOEncoding where

import qualified Data.IntSet as IS

import qualified SPO
import Signature
import SMT
import Term
import qualified Algebra as A

varGt' :: Term -> Term -> Formula
varGt' s t = FVar ("spo_" <> tshow s <> "_" <> tshow t)

varGeqSq :: Term -> Term -> Formula
varGeqSq s t = FVar ("sq1_" <> tshow s <> "_" <> tshow t)

varGtSq :: Term -> Term -> Formula
varGtSq s t = FVar ("sq2_" <> tshow s <> "_" <> tshow t)

geqSq :: [A.Encoder] -> Term -> Term -> Formula
geqSq _ (V _) _ = error "geqSq is not defined for variables"
geqSq _ _ (V _) = error "geqSq is not defined for variables"
geqSq [] (F _ _) (F _ _) = top
geqSq (e : es) s t = disj [ A._gt' e s t, conj [ A._geq' e s t, geqSq es s t ] ]

gtSq :: [A.Encoder] -> Term -> Term -> Formula
gtSq _ (V _) _ = error "gtSq is not defined for variables"
gtSq _ _ (V _) = error "gtSq is not defined for variables"
gtSq [] (F _ _) (F _ _) = bottom
gtSq (e : es) s t = disj [ A._gt' e s t, conj [ A._geq' e s t, gtSq es s t ] ]

gt' :: Term -> Term -> Formula
gt' (V _) _ = bottom
gt' s@(F _ _) (V x)
  | IS.member x (Term.variables s) = top
  | otherwise = bottom
gt' s@(F _ ss) t@(F _ ts) =
  disj [
    disj [ if si == t then top else varGt' si t  | si <- ss ],
    conj [
      conj [ varGt' s tj | tj <- ts ],
      disj [ 
        varGtSq s t,
        conj [ varGeqSq s t, gtLex ss ts]
      ]
    ]
  ]
  where
    gtLex [] _ = bottom
    gtLex (_ : _) [] = top
    gtLex (s' : ss') (t' : ts')
      | s' == t' = gtLex ss' ts'
      | otherwise = varGt' s' t'

gtrsim :: [A.Encoder] -> Term -> Term -> Formula
gtrsim es s t = conj [ A._geq e s t | e <- es ]

gt :: [A.Encoder] -> Term -> Term -> Formula
gt es s t = conj [ gtrsim es s t, gt' s t ]

-- possible: terms subject to comparison by >_mspo
side_condition :: [A.Encoder] -> [(Term, Term)] -> Signature -> Formula
side_condition es possible sig = conj $ 
  [ A._side_condition e sig | e <- es ] ++
  [ conj [
      implies (varGt' t' u') (gt' t' u'),
      if isVariable t' || isVariable u' then top else implies (varGeqSq t' u') (geqSq es t' u'),
      if isVariable t' || isVariable u' then top else implies (varGtSq t' u') (gtSq es t' u')
    ] | (t, u) <- possible, t' <- subterms t, u' <- subterms u
  ]

decode :: [A.Encoder] -> Model -> Signature -> SPO.Param
decode es m sig = [ A._decode e m sig | e <- es ]
