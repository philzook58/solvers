{-# LANGUAGE OverloadedStrings #-}
module Rule where

import qualified Data.Text as T

import Term
import Proof
import Signature

data Rule = Rule {
  _id :: Int,
  _orientation :: Orientation,
  _proof :: Proof,
  _lhs :: Term,
  _rhs :: Term,
  _depth :: Int
}

data Orientation =
    Oriented -- left to right
  | Unoriented
  deriving Eq

oriented :: Rule -> Bool
oriented rl = _orientation rl == Oriented

pp :: Signature -> Rule -> T.Text
pp sig rl =
  (T.pack (show (_id rl))) <> ": " <> Term.pp' sig vmap (_lhs rl) <> sep <> Term.pp' sig vmap (_rhs rl)
  where
    sep =
      case _orientation rl of
        Oriented -> " -> "
        Unoriented -> " = "
    vmap = nice_varnames [ _lhs rl, _rhs rl ]
