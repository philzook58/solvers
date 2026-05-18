{-# LANGUAGE OverloadedStrings #-}
module PrecedenceEncoding where

import qualified Data.Vector as V
import qualified Data.Text as T

import Signature
import SMT
import Term
import qualified Precedence

-- Note: aid (i.e. algebra id) is used for avoiding collision

varPrec :: Int -> Int -> Exp
varPrec aid f = Var ("pr_" <> T.pack (show f) <> "_" <> T.pack (show aid))

geq :: Int -> Term -> Term -> Formula
geq _ _ _ = top

gt :: Int -> Term -> Term -> Formula
gt _ _ _ = bottom

geq' :: Int -> Term -> Term -> Formula
geq' aid (F f _) (F g _) = SMT.geq (varPrec aid f) (varPrec aid g)
geq' _ _ _ = error "geq': both of arguments must be non-variables"

gt' :: Int -> Term -> Term -> Formula
gt' aid (F f _) (F g _) = SMT.gt (varPrec aid f) (varPrec aid g)
gt' _ _ _ = error "gt': both of arguments must be non-variables"

side_condition :: Int -> Signature -> Formula
side_condition aid sig =  Distinct [ varPrec aid f | f <- [0..(V.length sig -1)] ] 

simple :: Int -> Signature -> Formula
simple _ _ = bottom

no_marking :: Int -> Signature -> Formula
no_marking _ _ = top

decode :: Int -> Model -> Signature -> Precedence.Precedence
decode aid m sig = V.fromList [ evalExp m (varPrec aid f) | f <- [0..(V.length sig -1)] ]
