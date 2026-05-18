module Algebra where
-- TODO: nicely generalize to ReductionTriple

import Data.Text as T

import Term
import Signature
import SMT
import qualified Linear
import qualified LinearEncoding
import qualified Precedence
import qualified PrecedenceEncoding
import qualified MaxPlus
import qualified MaxPlusEncoding

data Algebra2 = Linear Linear.Algebra2
              | Precedence Precedence.Precedence
              | MaxPlus MaxPlus.Algebra2

toPrecedence :: Algebra2 -> Precedence.Precedence
toPrecedence (Precedence p) = p
toPrecedence (Linear _) = error "toPrecedence: Linear cannot be converted to precedence"
toPrecedence (MaxPlus _) = error "toPrecedence: MaxPlus cannot be converted to precedence"

data Class = L | P | M
  deriving Eq

toClass :: Char -> Class
toClass 'L' = L
toClass 'P' = P
toClass 'M' = M
toClass c = error ("order class " ++ [c] ++ " is not supported")

geq :: Algebra2 -> Term -> Term -> Bool
geq (Linear a) s t = Linear.geq a s t
geq (MaxPlus a) s t = MaxPlus.geq a s t
geq (Precedence _) _ _ = True

gt :: Algebra2 -> Term -> Term -> Bool
gt (Linear a) s t = Linear.gt a s t
gt (MaxPlus a) s t = MaxPlus.gt a s t
gt (Precedence _) _ _ = False

-- for top-marking
geq' :: Algebra2 -> Term -> Term -> Bool
geq' (Linear a) = Linear.geq' a
geq' (MaxPlus a) = MaxPlus.geq' a
geq' (Precedence p) = Precedence.geq_term p

-- for top-marking
gt' :: Algebra2 -> Term -> Term -> Bool
gt' (Linear a) = Linear.gt' a
gt' (MaxPlus a) = MaxPlus.gt' a
gt' (Precedence p) = Precedence.gt_term p

pp :: Signature -> Algebra2 -> T.Text 
pp sig (Linear a) = Linear.pp sig a
pp sig (MaxPlus a) = MaxPlus.pp sig a
pp sig (Precedence p) = Precedence.pp sig p

pp_no_marking :: Signature -> Algebra2 -> T.Text 
pp_no_marking sig (Linear a) = Linear.pp_no_marking sig a
pp_no_marking sig (MaxPlus a) = MaxPlus.pp_no_marking sig a
pp_no_marking sig (Precedence p) = Precedence.pp sig p

marked :: Algebra2 -> Bool
marked (Linear (a, b)) = not (a == b)
marked (MaxPlus (a, b)) = not (a == b)
marked (Precedence _) = False

data Encoder = Encoder {
  _side_condition :: Signature -> Formula,
  _geq :: Term -> Term -> Formula,
  _gt :: Term -> Term -> Formula,
  _geq' :: Term -> Term -> Formula, -- for top-marking
  _gt' :: Term -> Term -> Formula,  -- for top-marking,
  _simple :: Signature -> Formula,  -- for weak simplicity
  _no_marking :: Signature -> Formula,
  _decode :: Model -> Signature -> Algebra2
}

encoder :: Class -> Int -> Encoder
encoder L aid = Encoder {
  _side_condition = LinearEncoding.side_condition aid,
  _geq = LinearEncoding.geq aid,
  _gt = LinearEncoding.gt aid,
  _geq' = LinearEncoding.geq' aid,
  _gt' = LinearEncoding.gt' aid,
  _simple = LinearEncoding.simple aid,
  _no_marking = LinearEncoding.no_marking aid,
  _decode = decode
}
  where
    decode m sig = Linear (LinearEncoding.decode aid m sig)
encoder M aid = Encoder {
  _side_condition = MaxPlusEncoding.side_condition aid,
  _geq = MaxPlusEncoding.geq aid,
  _gt = MaxPlusEncoding.gt aid,
  _geq' = MaxPlusEncoding.geq' aid,
  _gt' = MaxPlusEncoding.gt' aid,
  _simple = MaxPlusEncoding.simple aid,
  _no_marking = MaxPlusEncoding.no_marking aid,
  _decode = decode
}
  where
    decode m sig = MaxPlus (MaxPlusEncoding.decode aid m sig)
encoder P aid = Encoder {
  _side_condition = PrecedenceEncoding.side_condition aid,
  _geq = PrecedenceEncoding.geq aid,
  _gt = PrecedenceEncoding.gt aid,
  _geq' = PrecedenceEncoding.geq' aid,
  _gt' = PrecedenceEncoding.gt' aid,
  _simple = PrecedenceEncoding.simple aid,
  _no_marking = PrecedenceEncoding.no_marking aid,
  _decode = decode
}
  where
    decode m sig = Precedence (PrecedenceEncoding.decode aid m sig)
