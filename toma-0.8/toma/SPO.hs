{-# LANGUAGE OverloadedStrings #-}
module SPO where

import qualified Data.IntSet as IS
import qualified Data.Text as T

import Term
import qualified Algebra as A
import Signature

type Param = [A.Algebra2]

isLPO :: Param -> Bool
isLPO [A.Precedence _] = True
isLPO _ = False

pp :: Signature -> Param -> T.Text
pp sig as = 
  "monotonic semantic path order\n" <>
  T.concat [ "algebra " <> T.pack (show i) <> ":\n" <> A.pp sig a | (i, a) <- zip [(1 :: Int)..] as ]

-- lexicographic comparison by parameter
geqSq :: Param -> Term -> Term -> Bool
geqSq _ (V _) _ = error "geqSq is not defined for variables"
geqSq _ _ (V _) = error "geqSq is not defined for variables"
geqSq [] (F _ _) (F _ _) = True
geqSq (a : as) s t = A.gt' a s t || (A.geq' a s t && geqSq as s t)

gtSq :: Param -> Term -> Term -> Bool
gtSq _ (V _) _ = error "gtSq is not defined for variables"
gtSq _ _ (V _) = error "gtSq is not defined for variables"
gtSq [] (F _ _) (F _ _) = False
gtSq (a : as) s t = A.gt' a s t || (A.geq' a s t && gtSq as s t)

-- spo
gt' :: Param -> Term -> Term -> Bool
gt' _ (V _) _ = False
gt' _ s@(F _ _) (V x) = IS.member x (Term.variables s)
gt' param s@(F _ ss) t@(F _ ts) =
  any (\si -> si == t || gt' param si t) ss ||
  (all (\tj -> gt' param s tj) ts &&
    (gtSq param s t || (geqSq param s t && gtLex' ss ts)))
  where
    gtLex' [] _ = False
    gtLex' (_ : _) [] = True
    gtLex' (s' : ss') (t' : ts') = gt' param s' t' || (s' == t' && gtLex' ss' ts')

-- to guarantee monotonicity
gtrsim :: Param -> Term -> Term -> Bool
gtrsim as s t = all (\a -> A.geq a s t) as

gt :: Param -> Term -> Term -> Bool
gt param s t = gtrsim param s t && gt' param s t
