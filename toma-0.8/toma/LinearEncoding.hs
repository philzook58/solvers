{-# LANGUAGE OverloadedStrings #-}
module LinearEncoding where

import qualified Data.IntSet as IS
import qualified Data.Vector as V
import qualified Data.Text as T

import Signature
import SMT
import Term
import qualified Linear

-- Note: aid (i.e. algebra id) is used for avoiding collision

varCoef :: Int -> Int -> Int -> Formula
varCoef aid f i = FVar ("coef_" <> T.pack (show aid) <> "_" <> T.pack (show f) <> "_" <> T.pack (show i))

varConst :: Int -> Int -> Exp
varConst aid f = Var ("const_" <> T.pack (show aid) <> "_" <> T.pack (show f))

varCoef' :: Int -> Int -> Int -> Formula
varCoef' aid f i = FVar ("coef#_" <> T.pack (show aid) <> "_" <> T.pack (show f) <> "_" <> T.pack (show i))

varConst' :: Int -> Int -> Exp
varConst' aid f = Var ("const#_" <> T.pack (show aid) <> "_" <> T.pack (show f))

coef :: Int -> Int -> Term -> Exp
coef _aid x (V y)
  | x == y = Val 1
  | otherwise = Val 0
coef aid x (F f ts) =
  plus [ times01 (varCoef aid f i) (coef aid x ti) | (ti, i) <- zip ts [0..] ]

coef' :: Int -> Int -> Term -> Exp
coef' _aid _ (V _) = error "coef' is not defined for variables"
coef' aid x (F f ts) = 
  Plus [ times01 (varCoef' aid f i) (coef aid x ti) | (ti, i) <- zip ts [0..] ]

constant :: Int -> Term -> Exp
constant _aid (V _) = Val 0
constant aid (F f ts) =
  plus ( varConst aid f : [ times01 (varCoef aid f i) (constant aid ti) | (ti, i) <- zip ts [0..] ])

constant' :: Int -> Term -> Exp
constant' _aid (V _) = error "constant' is not defined for variables"
constant' aid (F f ts) =
  plus ( varConst' aid f : [ times01 (varCoef' aid f i) (constant aid ti) | (ti, i) <- zip ts [0..] ])

geq :: Int -> Term -> Term -> Formula
geq aid s t = conj (SMT.geq (constant aid s) (constant aid t) : [ SMT.geq (coef aid x s) (coef aid x t) | x <- xs ])
  where
    xs = IS.toList (IS.union (Term.variables s) (Term.variables t))

geq' :: Int -> Term -> Term -> Formula
geq' aid s t = conj (SMT.geq (constant' aid s) (constant' aid t) : [ SMT.geq (coef' aid x s) (coef' aid x t) | x <- xs ])
  where
    xs = IS.toList (IS.union (Term.variables s) (Term.variables t))

gt :: Int -> Term -> Term -> Formula
gt aid s t = conj (SMT.gt (constant aid s) (constant aid t) : [ SMT.geq (coef aid x s) (coef aid x t) | x <- xs ])
  where
    xs = IS.toList (IS.union (Term.variables s) (Term.variables t))

gt' :: Int -> Term -> Term -> Formula
gt' aid s t = conj (SMT.gt (constant' aid s) (constant' aid t) : [ SMT.geq (coef' aid x s) (coef' aid x t) | x <- xs ])
  where
    xs = IS.toList (IS.union (Term.variables s) (Term.variables t))

wellDefined :: Int -> Signature -> Formula
wellDefined aid sig =
  conj [ conj [ SMT.geq (varConst aid f) (Val 0), SMT.geq (varConst' aid f) (Val 0) ] | f <- [0..(V.length sig - 1)]]

small :: Int -> Signature -> Formula
small aid sig =
  conj [ conj [ SMT.geq (Val ub) (varConst aid f), SMT.geq (Val ub) (varConst' aid f) ] | f <- [0..(V.length sig - 1)]]
  where
    ub = 10 -- magic number to avoid overflow (to be adjusted)

-- (?) do not worry about overflow (64-bit integer is large enough?) 
side_condition :: Int -> Signature -> Formula
side_condition aid sig = conj [ wellDefined aid sig ] -- small aid sig 

simple :: Int -> Signature -> Formula
simple aid sig = conj [ varCoef aid f i | f <- [0..(V.length sig - 1)],  i <- [0..(arity sig f -1)]  ]

no_marking :: Int -> Signature -> Formula
no_marking aid sig = conj [
    conj (SMT.eq (varConst aid f) (varConst' aid f) : [ iff (varCoef aid f i) (varCoef' aid f i) | i <- [0..(arity sig f -1)] ])
  | f <- [0..(V.length sig - 1)] ]

decode :: Int -> Model -> Signature -> Linear.Algebra2
decode aid m sig = (a, a')
  where
    evalCoef f i = if evalFormula m (varCoef aid f i) then 1 else 0
    evalCoef' f i = if evalFormula m (varCoef' aid f i) then 1 else 0
    affine f = (evalExp m (varConst aid f), [ evalCoef f i | i <- [0..(arity sig f - 1)]])
    affine' f = (evalExp m (varConst' aid f), [ evalCoef' f i | i <- [0..(arity sig f - 1)]])
    a = V.fromList [ affine f | f <- [0..(V.length sig - 1)] ]
    a' = V.fromList [ affine' f | f <- [0..(V.length sig - 1)] ]
