{-# LANGUAGE OverloadedStrings #-}
module Proof where

import qualified Data.IntSet as IS
import qualified Data.Text as T

import qualified TPTP

-- a very simple equational proof
data Proof =
    Axiom (Maybe TPTP.Annotation) -- equation introduced by prover does not have annotation
  | Conversion IS.IntSet -- Conversion R represents a conversion <-R->* 

tshow :: Proof -> T.Text
tshow (Axiom _) = "(axiom)"
tshow (Conversion is) = 
  "(from {" <> T.intercalate ", " (map (T.pack . show) (IS.toList is)) <> "})"
