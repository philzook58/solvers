{-# LANGUAGE OverloadedStrings #-}
module MaxPlusEncoding where

import qualified Data.Vector as V
import qualified Data.Text as T

import Signature
import SMT
import Term
import qualified MaxPlus

-- f_A(x1,...,xn) = max{a0, b1 (a1 + x1), ..., bn (an + xn)}

-- Encoding functions.

-- (Nothing, b, a) denotes b a
-- (Just x, b, a)  denotes b (a + x)
type Affine = (Maybe Int, Formula, Exp)

var_a0 :: Int -> Int -> Exp
var_a0 aid f = 
  Var ("a0_" <> T.pack (show aid) <> "_" <> T.pack (show  f)) 

var_a0' :: Int -> Int -> Exp
var_a0' aid f = 
  Var ("a0#_" <> T.pack (show aid) <> "_" <> T.pack (show  f)) 

var_ai :: Int -> Int -> Int -> Exp
var_ai aid f i =
  Var ("a_" <>  T.pack (show aid) <> "_" <> T.pack (show  f) <> "_" <> T.pack (show i)) 

var_ai' :: Int -> Int -> Int -> Exp
var_ai' aid f i =
  Var ("a#_" <>  T.pack (show aid) <> "_" <> T.pack (show  f) <> "_" <> T.pack (show i)) 

var_bi :: Int -> Int -> Int -> Formula
var_bi aid f i =
  FVar ("b_" <> T.pack (show aid) <> "_" <> T.pack (show  f) <> "_" <> T.pack (show i)) 

var_bi' :: Int -> Int -> Int -> Formula
var_bi' aid f i =
  FVar ("b#_" <> T.pack (show aid) <> "_" <> T.pack (show  f) <> "_" <> T.pack (show i)) 

interpret :: Int -> Term -> [Affine]
interpret _ (V x)    = [(Just x, top, Val 0)]
interpret k (F f ts) =
  (Nothing, top, var_a0 k f) :
  [ (m, conj [var_bi k f i, b], plus [var_ai k f i, a]) 
  | (i, ti) <- zip [1..] ts,
    (m, b, a) <- interpret k ti]

interpret' :: Int -> Term -> [Affine]
interpret' _ (V _)    = error "interpret': not for variables"
interpret' k (F f ts) =
  (Nothing, top, var_a0' k f) :
  [ (m, conj [var_bi' k f i, b], plus [var_ai' k f i, a]) 
  | (i, ti) <- zip [1..] ts,
    (m, b, a) <- interpret k ti]

geq_affine :: Affine -> Affine -> Formula
geq_affine (_, b1, a1) (Nothing, b2, a2) =
  SMT.geq (times01 b1 a1) (times01 b2 a2)
geq_affine (Just x, b1, a1) (Just y, b2, a2)
  | x == y = 
      conj [ implies b2 b1, SMT.geq (times01 b1 a1) (times01 b2 a2) ]
geq_affine (_, b1, a1) (Just _, b2, _) =
  conj [ neg b2, SMT.geq (times01 b1 a1) (Val 0) ]

gt_affine :: Affine -> Affine -> Formula
gt_affine (_, b1, a1) (Nothing, b2, a2) =
  SMT.gt (times01 b1 a1) (times01 b2 a2)
gt_affine (Just x, b1, a1) (Just y, b2, a2)
  | x == y = -- implies b2 b1 is redundant? (follows from b1 * a1 > b2 * a2?)
      conj [ implies b2 b1, SMT.gt (times01 b1 a1) (times01 b2 a2) ]
gt_affine (_, b1, a1) (Just _, b2, _) =
  conj [ neg b2, SMT.gt (times01 b1 a1) (Val 0) ]

-- Hoare extensions of geq_affine and gt_affine

geq_affine_hoare :: [Affine] -> [Affine] -> Formula
geq_affine_hoare as bs =
  conj [ disj [ geq_affine a b | a <- as ] | b <- bs ]

gt_affine_hoare :: [Affine] -> [Affine] -> Formula
gt_affine_hoare as bs =
  conj ([ disj [ gt_affine a b | a <- as ] | b <- bs ])
 
-- s >=_A t
geq :: Int -> Term -> Term -> Formula
geq k s t = 
  geq_affine_hoare (interpret k s) (interpret k t)

-- s# >=_A t#
geq' :: Int -> Term -> Term -> Formula
geq' k s t = 
  geq_affine_hoare (interpret' k s) (interpret' k t)

-- s >_A t
gt :: Int -> Term -> Term -> Formula
gt k s t = 
  gt_affine_hoare (interpret k s) (interpret k t)

-- s# >_A t#
gt' :: Int -> Term -> Term -> Formula
gt' k s t = 
  gt_affine_hoare (interpret' k s) (interpret' k t)

side_condition :: Int -> Signature -> Formula
side_condition k sig =
  conj [ conj [ SMT.geq (var_a0 k f) (Val 0), SMT.geq (var_a0' k f) (Val 0) ] | f <- [0..(V.length sig - 1)] ]

simple :: Int -> Signature -> Formula
simple aid sig = conj [
    conj [ var_bi aid f i, SMT.geq (var_ai aid f i) (Val 0) ]
    | f <- [0 .. (V.length sig - 1)],  i <- [1 .. arity sig f]
  ]

no_marking :: Int -> Signature -> Formula
no_marking aid sig = conj [
    conj [ SMT.eq (var_a0 aid f) (var_a0' aid f) | f <- [0 .. (V.length sig -1)] ],
    conj [
      conj [
        iff (var_bi aid f i) (var_bi' aid f i),
        SMT.eq (var_ai aid f i) (var_ai' aid f i)
      ]
      | f <- [0..(V.length sig - 1)],
        i <- [1 .. (arity sig f - 1)]
    ]
  ]

-- decoding

decode :: Int -> Model -> Signature -> MaxPlus.Algebra2
decode aid m sig = (a, a')
  where
    ex = evalExp m
    ef f = if evalFormula m f then 1 else 0 
    interp f =
      (ex (var_a0 aid f), [ (ef (var_bi aid f i), ex (var_ai aid f i)) | i <- [1 .. arity sig f]])
    interp' f =
      (ex (var_a0' aid f), [ (ef (var_bi' aid f i), ex (var_ai' aid f i)) | i <- [1 .. arity sig f]])
    a = V.fromList [ interp f | f <- [0..(V.length sig - 1)] ]
    a' = V.fromList [ interp' f | f <- [0..(V.length sig - 1)] ]
