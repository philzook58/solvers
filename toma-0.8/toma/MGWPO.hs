{-# LANGUAGE OverloadedStrings #-}
module MGWPO where

import qualified Data.IntSet as IS
import qualified Data.Text as T

import Term
import qualified Algebra as A
import Signature

type Param = (A.Algebra2, A.Algebra2)

pp :: Signature -> Param -> T.Text
pp sig (a, b) = 
  "monotone generalized weighted path order\n" <>
  "algebra 1:\n" <>
  A.pp_no_marking sig a <>
  "algebra 2:\n" <>
  A.pp sig b

-- gwpo
gt' :: Param -> Term -> Term -> Bool
gt' _ (V _) _ = False
gt' (a, _) s@(F _ _) t@(V x) =
  A.gt a s t || (A.geq a s t && IS.member x (Term.variables s))
gt' param@(a, b) s@(F _ ss) t@(F _ ts) =
  A.gt a s t ||
  (A.geq a s t &&
    (any (\si -> si == t || gt' param si t) ss ||
    (all (\tj -> gt' param s tj) ts &&
        (A.gt' b s t || (A.geq' b s t && gtLex ss ts)))))
  where
    gtLex [] _ = False
    gtLex (_ : _) [] = True
    gtLex (s' : ss') (t' : ts') = gt' param s' t' || (s' == t' && gtLex ss' ts')

-- assumption for optimization: first algebra a is normal
gt :: Param -> Term -> Term -> Bool
gt param@(_, b) s t = A.geq b s t && gt' param s t
