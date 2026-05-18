{-# LANGUAGE OverloadedStrings #-}
module GWPO where

import qualified Data.IntSet as IS
import qualified Data.Text as T

import Term
import qualified Precedence as Pr
import qualified Algebra as A
import Signature

type Param = (A.Algebra2, Pr.Precedence)

pp :: Signature -> Param -> T.Text
pp sig (a, pr)
  | A.marked a =
      "generalized weighted path order\n" <>
      "algebra:\n" <>
      A.pp sig a <>
      "precedence: " <> Pr.pp sig pr
  | otherwise = 
      "weighted path order\n" <>
      "algebra:\n" <>
      A.pp_no_marking sig a <>
      "precedence: " <> Pr.pp sig pr

geqSq1 :: Param -> Term -> Term -> Bool
geqSq1 (a, _) s t = A.geq a s t

gtSq1 :: Param -> Term -> Term -> Bool
gtSq1 (a, _) s t = A.gt a s t

-- lexicographic comparison by parameter
geqSq2 :: Param -> Term -> Term -> Bool
geqSq2 _ (V _) _ = error "geqSq2 is not defined for variables"
geqSq2 _ _ (V _) = error "geqSq2 is not defined for variables"
geqSq2 (a, pr) s@(F f _) t@(F g _) = A.gt' a s t || (A.geq' a s t && Pr.geq pr f g)

gtSq2 :: Param -> Term -> Term -> Bool
gtSq2 _ (V _) _ = error "gtSq2 is not defined for variables"
gtSq2 _ _ (V _) = error "gtSq2 is not defined for variables"
gtSq2 (a, pr) s@(F f _) t@(F g _) = A.gt' a s t || (A.geq' a s t && Pr.gt pr f g)

-- gwpo
gt :: Param -> Term -> Term -> Bool
gt _ (V _) _ = False
gt param s@(F _ _) t@(V x) =
  gtSq1 param s t || (geqSq1 param s t && IS.member x (Term.variables s))
gt param s@(F _ ss) t@(F _ ts) =
  gtSq1 param s t ||
  (geqSq1 param s t &&
    (any (\si -> si == t || gt param si t) ss ||
    (all (\tj -> gt param s tj) ts &&
        (gtSq2 param s t || (geqSq2 param s t && gtLex ss ts)))))
  where
    gtLex [] _ = False
    gtLex (_ : _) [] = True
    gtLex (s' : ss') (t' : ts') = gt param s' t' || (s' == t' && gtLex ss' ts')
