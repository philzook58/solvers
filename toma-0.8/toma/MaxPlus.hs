{-# LANGUAGE OverloadedStrings #-}
module MaxPlus where

import qualified Data.Vector as V
import qualified Data.Text as T

import Signature
import Term

-- f_A(x1,...,xn) = max{a0, b1 (a1 + x1), ..., bn (an + xn)}
type Interpretation = (Int, [(Int, Int)]) 
type Algebra = V.Vector Interpretation
type Algebra2 = (Algebra, Algebra) -- second is for top-marking

interp_lhs :: T.Text -> Int -> T.Text 
interp_lhs nam ar
  | ar == 0 = nam <> "_A"
  | otherwise = nam <> "_A(" <> T.intercalate ", " [ "x" <> T.pack (show i) | i <- [1 .. ar]] <> ")"

interp_rhs :: Interpretation -> T.Text
interp_rhs (c, bas)
  | all (\(b, _) -> b == 0) bas = T.pack (show c)
  | otherwise = "max{" <> T.pack (show c) <> ", " <>
                  T.intercalate ", " [ ex bi ai i  | ((bi, ai), i) <- zip bas [(1::Int)..], bi > 0 ] <> "}"
  where
    ex b 0 i = mono b ("x" <> T.pack (show i)) <> T.pack (show i)
    ex b a i
      | a < 0 = mono b ("x" <> T.pack (show i)) <> " - " <> T.pack (show (-a))
      | otherwise = mono b ("x" <> T.pack (show i)) <> " + " <> T.pack (show a)
    mono 1 x = x
    mono b x = T.pack (show b) <> " " <> x

pp_no_marking :: Signature -> Algebra2 -> T.Text 
pp_no_marking sig (a, _) = 
  T.unlines [ interp_lhs (name sig f) (arity sig f) <> " = " <> interp_rhs (a V.! f)
            | f <- [0 .. V.length sig - 1 ] ]

pp :: Signature -> Algebra2 -> T.Text 
pp sig ab = 
  T.unlines [ interp_lhs (name sig f <> m) (arity sig f) <> " = " <> interp_rhs (a V.! f)
            | f <- [0 .. V.length sig - 1 ],
              (m, a) <- [ ("", fst ab), ("#", snd ab) ] ]

-- (Nothing, b, a) denotes b a
-- (Just x, b, a)  denotes b (a + x)
type Affine = (Maybe Int, Int, Int)

interpret :: Algebra -> Term -> [Affine]
interpret _ (V x) = [(Just x, 1, 0)]
interpret alg (F f ts) =
  (Nothing, 1, fst (alg V.! f)) : 
  [ (m, bi * b, a + ai)
  | (ti, (bi, ai)) <- zip ts (snd (alg V.! f)),
    (m, b, a) <- interpret alg ti ]

interpret' :: Algebra2 -> Term -> [Affine]
interpret' _ (V _) = error "interpret': not for variables"
interpret' (alg1, alg2) (F f ts) =
  (Nothing, 1, fst (alg2 V.! f)) : 
  [ (m, bi * b, a + ai)
  | (ti, (bi, ai)) <- zip ts (snd (alg2 V.! f)),
    (m, b, a) <- interpret alg1 ti ]

geq_affine :: Affine -> Affine -> Bool
geq_affine (_, b1, a1) (Nothing, b2, a2) = 
  b1 * a1 >= b2 * a2
geq_affine (Just x, b1, a1) (Just y, b2, a2)
  | x == y = (b1 >= b2) && (b1 * a1 >= b2 * a2)
geq_affine (_, b1, a1) (Just _, b2, _) =
  b2 == 0 && b1 * a1 >= 0

gt_affine :: Affine -> Affine -> Bool
gt_affine (_, b1, a1) (Nothing, b2, a2) = 
  b1 * a1 > b2 * a2
gt_affine (Just x, b1, a1) (Just y, b2, a2)
  | x == y = (b1 >= b2) && (b1 * a1 > b2 * a2)
gt_affine (_, b1, a1) (Just _, b2, _) =
  b2 == 0 && b1 * a1 > 0

-- Hoare extensions of geq_affine and gt_affine

geq_affine_hoare :: [Affine] -> [Affine] -> Bool
geq_affine_hoare as bs =
  and [ or [ geq_affine a b | a <- as ] | b <- bs ]

gt_affine_hoare :: [Affine] -> [Affine] -> Bool
gt_affine_hoare as bs =
  and [ or [ gt_affine a b | a <- as ] | b <- bs ]

-- s >=_A t
geq :: Algebra2 -> Term -> Term -> Bool
geq (a, _) s t = 
  geq_affine_hoare (interpret a s) (interpret a t)

-- s# >=_A t#
geq' :: Algebra2 -> Term -> Term -> Bool
geq' a2 s t = 
  geq_affine_hoare (interpret' a2 s) (interpret' a2 t)

-- s >_A t
gt :: Algebra2 -> Term -> Term -> Bool
gt (a, _) s t = 
  gt_affine_hoare (interpret a s) (interpret a t)

-- s# >_A t#
gt' :: Algebra2 -> Term -> Term -> Bool
gt' a2 s t = 
  gt_affine_hoare (interpret' a2 s) (interpret' a2 t)
