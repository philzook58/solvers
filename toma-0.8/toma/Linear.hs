{-# LANGUAGE OverloadedStrings #-}
module Linear where
-- linear polynomial interpretation

import qualified Data.Vector as V
import qualified Data.IntSet as IS
import qualified Data.Text as T

import Signature
import Term

type Affine = (Int, [Int]) -- linear polynomial
type Algebra = V.Vector Affine -- associate each function symbol with a linear polynomial
type Algebra2 = (Algebra, Algebra) -- second is for top-marking

interp_lhs :: T.Text -> Int -> T.Text 
interp_lhs nam ar
  | ar == 0 = nam <> "_A"
  | otherwise = nam <> "_A(" <> T.intercalate ", " [ "x" <> T.pack (show i) | i <- [1 .. ar]] <> ")"

interp_rhs :: Affine -> T.Text
interp_rhs (c, coefs)
  | all (\co -> co == 0) coefs = T.pack (show c)
  | otherwise = T.intercalate " + " [ mono ci i   | (ci, i) <- zip coefs [(1::Int)..] , ci /= 0] <>
                if c /= 0 then " + " <> T.pack (show c) else ""
  where
    mono 1 i = "x" <> T.pack (show i)
    mono cf i = T.pack (show cf) <> " x" <> T.pack (show i)

pp_no_marking :: Signature -> Algebra2 -> T.Text 
pp_no_marking sig (a, _) = 
  T.unlines [ interp_lhs (name sig f) (arity sig f) <> " = " <> interp_rhs (a V.! f)
            | f <- [0 .. V.length sig - 1 ] ]

pp :: Signature -> Algebra2 -> T.Text 
pp sig ab = 
  T.unlines [ interp_lhs (name sig f <> m) (arity sig f) <> " = " <> interp_rhs (a V.! f)
            | f <- [0 .. V.length sig - 1 ],
              (m, a) <- [ ("", fst ab), ("#", snd ab) ] ]

-- coefficient of variable x
coef :: Algebra -> Int -> Term -> Int
coef _ x (V y)
  | x == y = 1
  | otherwise = 0
coef a x (F f ts) = sum [ ci * coef a x ti  | (ti, ci) <- zip ts (snd (a V.! f)) ]

coef' :: Algebra2 -> Int -> Term -> Int
coef' _ _ (V _) = error "coef' is not defined for variables"
coef' (a, b) x (F f ts) = sum [ ci * coef a x ti  | (ti, ci) <- zip ts (snd (b V.! f)) ]

constant :: Algebra -> Term -> Int
constant _ (V _) = 0
constant a (F f ts) = fst (a V.! f)  + sum [ ci * constant a ti | (ti, ci) <- zip ts (snd (a V.! f)) ]

constant' :: Algebra2 -> Term -> Int
constant' _ (V _) = error "constant' is not defined for variables"
constant' (a, b) (F f ts) = fst (b V.! f)  + sum [ ci * constant a ti | (ti, ci) <- zip ts (snd (b V.! f)) ]

-- TODO: optimize comparison
geq :: Algebra2 -> Term -> Term -> Bool
geq (a, _) s t = constant a s >= constant a t &&
  all (\x -> coef a x s >= coef a x t) (IS.toList (IS.union (variables s) (variables t)))

gt :: Algebra2 -> Term -> Term -> Bool
gt (a, _) s t = constant a s > constant a t &&
  all (\x -> coef a x s >= coef a x t) (IS.toList (IS.union (variables s) (variables t)))

geq' :: Algebra2 -> Term -> Term -> Bool
geq' a s t = constant' a s >= constant' a t &&
  all (\x -> coef' a x s >= coef' a x t) (IS.toList (IS.union (variables s) (variables t)))

gt' :: Algebra2 -> Term -> Term -> Bool
gt' a s t = constant' a s > constant' a t &&
  all (\x -> coef' a x s >= coef' a x t) (IS.toList (IS.union (variables s) (variables t)))
