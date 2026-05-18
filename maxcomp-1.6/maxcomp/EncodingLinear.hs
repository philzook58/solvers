-- A module for encoding quasi-models for semantic labeling.

module EncodingLinear where

import Term
import SMT
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

varB :: String -> Int -> Exp
varB f i = Var ("b_" ++ f ++ "_" ++ show i)

fvarA :: String -> Int -> Formula
fvarA f i = FVar ("a_" ++ f ++ "_" ++ show i)

-- well-definedness of algebra
variableConstraint :: Signature -> Formula
variableConstraint sig =
  conj [ Geq (varB f 0) (Val 0) | (f, _) <- markSignature sig ]

interpret :: Term -> Value
interpret (V x)    = [(top, Indeterminate x)]
interpret (F f ts) = 
  EncodingLinear.sum
    (constant (varB f 0) :
     [ mul (fvarA f i) (interpret t) | (i, t) <- zip [1..] ts ])

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

-- s >_L t
gtA :: Term -> Term -> Formula
gtA s t = gtValue (interpret s) (interpret t)

--  s >=_A t
geqA :: Term -> Term -> Formula
geqA s t = geqValue (interpret s) (interpret t)

-- Decoding functions.

decodeInterpretation :: Model -> String -> Int -> Linear.Interpretation
decodeInterpretation m f n =
  (f, (evalExp m (varB f 0),
       [ evalFormula m (fvarA f i) | i <- [1..n] ]))

labeled :: String -> Formula
labeled f = FVar ("l_" ++ f)

decode :: Model -> Signature -> Linear.Algebra
decode m sig =
   [ decodeInterpretation m f n | (f, n) <- sig ] ++
   [ decodeInterpretation m (mark f) n | (f, n) <- sig, evalFormula m (labeled f) ]
