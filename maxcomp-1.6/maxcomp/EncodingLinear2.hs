module EncodingLinear2 where

-- only for SPO.

import SMT
import Term
import qualified Linear

-- Linear interpretations on natural numbers with {0, 1}-coefficients.
-- f_A(x_1, ..., x_n) = b_f_0 + a_f_1 x_1 + ... + a_f_n x_n
--   where b_f_0 in N, and a_f_1, ..., a_f_n in {0, 1}.

data Base = 
    Constant Exp
  | Indeterminate String

type Value = [(Formula, Base)]

indeterminates :: Value -> [String]
indeterminates l = [ x | (_, Indeterminate x) <- l ]

zero :: Value
zero = []

constant :: Exp -> Value
constant f = [(top, Constant f)]

sum :: [Value] -> Value
sum ls = concat ls

mul :: Formula -> Value -> Value
mul f l = [ (conj [f, f'], cx) | (f', cx) <- l ]

coefficient :: Value -> String -> Exp
coefficient l x =
  plus [ ite f (Val 1) (Val 0) | (f, Indeterminate x') <- l, x == x' ]

constantPart :: Value -> Exp
constantPart l = Plus [ ite f c (Val 0) | (f, Constant c) <- l ]

-- k: id of algebra
varB :: Int -> String -> Int -> Exp
varB k f i = Var ("b_" ++ show k ++ "_" ++ f ++ "_" ++ show i)

fvarA :: Int -> String -> Int -> Formula
fvarA k f i = FVar ("a_" ++ show k ++ "_" ++ f ++ "_" ++ show i)

interpret :: Int -> Term -> Value
interpret _ (V x)    = [(top, Indeterminate x)]
interpret k (F f ts) = 
  EncodingLinear2.sum
    (constant (varB k f 0) :
     [ mul (fvarA k f i) (interpret k t) | (i, t) <- zip [1..] ts ])

gtValue :: Value -> Value -> Formula
gtValue l1 l2 =
  conj (Gt (constantPart l1) (constantPart l2) :
        [ Geq (coefficient l1 x) (coefficient l2 x) 
        | x <- indeterminates l2 ])

geqValue :: Value -> Value -> Formula
geqValue l1 l2 =
  conj (Geq (constantPart l1) (constantPart l2) :
        [ Geq (coefficient l1 x) (coefficient l2 x) 
        | x <- indeterminates l2 ])

-- s >_A t
encodeGtA :: Int -> Term -> Term -> Formula
encodeGtA k s t = gtValue (interpret k s) (interpret k t)

--  s >=_A t
encodeGeqA :: Int -> Term -> Term -> Formula
encodeGeqA k s t = geqValue (interpret k s) (interpret k t)

encodeWellDef :: Int -> Signature -> Formula
encodeWellDef k sig =
  conj [ Geq (varB k f 0) (Val 0) | (f, _) <- sig ]

-- Decoding functions.

decodeInterpretation :: Int -> Model -> String -> Int -> Linear.Interpretation
decodeInterpretation k m f n =
  (f, (evalExp m (varB k f 0),
       [ evalFormula m (fvarA k f i) | i <- [1..n] ]))

decodeAlgebra :: Int -> Model -> Signature -> Linear.Algebra
decodeAlgebra k m sig =
   [ decodeInterpretation k m f n | (f, n) <- sig ]
