{-# LANGUAGE OverloadedStrings #-}
module Term where

import Data.List
import qualified Data.IntMap.Strict as IM
import qualified Data.Text as T
import qualified Data.IntSet as IS
import Data.Maybe
import Data.Char (isAlphaNum)

import IntMultiSet as IMS
import Signature

data Term = V Int | F Int [Term] deriving Eq

-- only for debugging
instance Show Term where
  show (V x) = show x
  show (F f ts) = show f ++ "("  ++ intercalate "," [ show t | t <- ts ] ++ ")"

-- used for SMT encoding (to stringify terms)
tshow :: Term -> T.Text
tshow (V x) = T.pack (show x)
tshow (F f ts) = T.pack (show f) <> "("  <> T.intercalate "," [ tshow t | t <- ts ] <> ")"

type Subst = IM.IntMap Term

type Position = [Int] -- 0-indexed

nice_varnames :: [Term] -> IM.IntMap T.Text
nice_varnames ts =
  IM.fromList (zip (variables_ordered ts) ("X" : "Y" : "Z" : "W" : "V" : "U" : [ "U" <> T.pack (show n)  | n <- [(2::Int)..]]))

pp :: Signature -> IM.IntMap T.Text -> Term -> T.Text
pp sig vmap t = recur t
  where
    recur (V x) = vmap IM.! x
    recur (F f []) = name sig f
    recur (F f us) = name sig f <> "(" <> (T.intercalate ", " [ recur u | u <- us ]) <> ")"

isBinaryOperator :: T.Text -> Bool
isBinaryOperator f
  | c : _ <- T.unpack f = not (isAlphaNum c)
  | otherwise = False

isUnaryOperator :: T.Text -> Bool
isUnaryOperator f
  | c : [] <- T.unpack f = not (isAlphaNum c)
  | otherwise = False

-- print '+'('-'(X1), X3) as -X + Y
pp' :: Signature -> IM.IntMap T.Text -> Term -> T.Text
pp' sig vmap t = aux1 t
  where
    aux1 (F f [t1, t2])
      | isBinaryOperator (name sig f) =
          aux2 t1 <> " " <> name sig f <> " " <> aux2 t2 
    aux1 u = aux2 u
    aux2 (F f [ F g [] ])
      | isUnaryOperator (name sig f) =
          name sig f <> name sig g
    aux2 (F f [ V x ])
      | isUnaryOperator (name sig f) =
          name sig f <> vmap IM.! x
    aux2 (V x) = vmap IM.! x
    aux2 (F f []) = name sig f
    aux2 (F f [t1, t2])
      | isBinaryOperator (name sig f) =
          "(" <> aux2 t1 <> " " <> name sig f <> " " <> aux2 t2 <> ")" 
    aux2 (F f us) = name sig f <> "(" <> (T.intercalate ", " [ aux1 u | u <- us ]) <> ")"

-- Var(t)

variables :: Term -> IS.IntSet
variables (V x) = IS.singleton x
variables (F _ ts) = IS.unions [ variables t | t <- ts ]

-- variables in occurence order but without duplication
variables_ordered :: [Term] -> [Int]
variables_ordered ts = nub' (concatMap vars ts) [] IS.empty
  where
    nub' [] acc _ = reverse acc
    nub' (x : xs) acc s
      | IS.member x s = nub' xs acc s
      | otherwise = nub' xs (x : acc) (IS.insert x s)
    vars (V x) = [x]
    vars (F _ us) = concat [ vars u | u <- us ]

ground :: Term -> Bool
ground t = IS.null (variables t)

isVariable :: Term -> Bool
isVariable (V _) = True
isVariable _ = False

-- check if a term is of the form f(x_1, ..., x_n)
shallow :: Term -> Bool
shallow (V _) = False
shallow (F _ ts) = all isVariable ts

-- Fun(t)

functions :: Term -> IS.IntSet
functions (V _)    = IS.empty
functions (F f ts) = IS.insert f (IS.unions [ functions t | t <- ts ])

countFunctions :: Term -> IMS.IntMultiSet
countFunctions (V _) = IMS.empty
countFunctions (F f ts) = IMS.insert f (IMS.unions [ countFunctions t | t <- ts ])

-- |t|
size :: Term -> Int
size (V _)    = 1
size (F _ ts) = 1 + sum [ size t | t <- ts ]

height :: Term -> Int
height (V _) = 0
height (F _ []) = 0
height (F _ ts) = 1 + maximum [ height t | t <- ts ] 

countVariables :: Term -> IMS.IntMultiSet
countVariables (V x) = IMS.singleton x
countVariables (F _ ts) = IMS.unions [ countVariables t | t <- ts ]

-- |t|_x
countVariable :: Term -> Int -> Int
countVariable (V y) x
  | x == y    = 1
  | otherwise = 0
countVariable (F _ ts) x = sum [ countVariable t x | t <- ts ]

-- The list of all subterms of a term.
subterms :: Term -> [Term]
subterms t@(V _) = [t]
subterms t@(F _ us) = t : nub [ v | u <- us, v <- subterms u ]

proper_subterms :: Term -> [Term]
proper_subterms (V _)    = []
proper_subterms (F _ ts) = [ u | t <- ts, u <- subterms t ]

-- Pos(t)
positions :: Term -> [Position]
positions (V _)    = [ [] ]
positions (F _ ts) = [] : [ i : p | (i, t) <- zip [0..] ts, p <- positions t ]

-- Pos_F(t)
functionPositions :: Term -> [Position]
functionPositions (V _)    = []
functionPositions (F _ ts) = 
  [] : [ i : p | (i, t) <- zip [0..] ts, p <- functionPositions t ] 

-- function positions with subterms
functionPositions' :: Term -> [(Position, Term)]
functionPositions' (V _) = []
functionPositions' t@(F _ ts) =
  ([], t) : [ (i : p, u) | (i, ti) <- zip [0..] ts, (p, u) <- functionPositions' ti ]

nonRootFunctionPositions' :: Term -> [(Position, Term)]
nonRootFunctionPositions' (V _) = []
nonRootFunctionPositions' (F _ ts) =
  [ (i : p, u) | (i, ti) <- zip [0..] ts, (p, u) <- functionPositions' ti ]

-- t|_p
subtermAt :: Term -> Position -> Term
subtermAt t        []      = t
subtermAt (F _ ts) (i : p) = subtermAt (ts !! i) p
subtermAt _        _       = error "subtermAt"

-- replace t u p = t[u]_p
replace :: Term -> Term -> Position -> Term
replace _        u []      = u
replace (F f ts) u (i : p) =
  F f [ if i == j then replace tj u p else tj | (j, tj) <- zip [0..] ts ]
replace _ _ _ = error "replace: invalid position"

nonDuplicating :: (Term, Term) -> Bool
nonDuplicating (l, r) = (countVariables r) `IMS.isSubsetOf` (countVariables l)

duplicating :: (Term, Term) -> Bool
duplicating = not . nonDuplicating

variableCondition :: (Term, Term) -> Bool
variableCondition (V _, _) = False
variableCondition (l, r)   = (Term.variables r) `IS.isSubsetOf` (Term.variables l)

-- isIteration f x t checks if t = f^n(x) for some n 
isIteration :: Int -> Int -> Term -> Bool
isIteration _ x (V y) = x == y
isIteration f x (F g [t]) = f == g && isIteration f x t
isIteration _ _ _ = False

-- t sigma
substitute :: Term -> Subst -> Term
substitute (V x) sigma
    | Just t <- IM.lookup x sigma = t
    | otherwise                = V x
substitute (F f ts) sigma      = F f [ substitute t sigma | t <- ts ]

-- Dom(sigma)
domain :: Subst -> [Int]
domain = IM.keys

-- x sigma tau = (x sigma) tau for all variables x
compose :: Subst -> Subst -> Subst
compose sigma tau = IM.union sigma' tau -- NOTE: Map.union perfers left
  where
    sigma' = IM.mapMaybe (\t -> Just (substitute t tau)) sigma

-- matching
-- match t u returns σ if tσ = u.
match :: Term -> Term -> Maybe Subst
match t u
  | Just sol <- match' t u = build IM.empty sol
  | otherwise = Nothing
  where
    match' (V x) t' = Just [ (x, t') ]
    match' (F f ts) (F g us)
      | f == g = fmap concat (sequence [ match' t' u' | (t', u') <- zip ts us ])
    match' _ _ = Nothing
    build m [] = Just m
    build m ((x, t') : rest) =
      case IM.lookup x m of
        Just t'' -> if t' == t'' then build m rest else Nothing
        Nothing -> build (IM.insert x t' m) rest

subsumes :: Term -> Term -> Bool
subsumes t u = isJust (match t u)

-- Most general unifier

mgu' :: Subst -> [(Term, Term)] -> Maybe Subst
mgu' sigma [] = Just sigma
mgu' sigma ((V x, V y) : es)
  | x == y = mgu' sigma es
mgu' sigma ((V x, t) : es)
  | IS.notMember x (variables t) =
      mgu' (compose sigma tau) [ (substitute l tau, substitute r tau) | (l, r) <- es ]
  where tau = IM.singleton x t
mgu' sigma ((s, t@(V _)) : es) = mgu' sigma ((t, s) : es)
mgu' sigma ((F f ss, F g ts) : es)
  | f == g = mgu' sigma (zip ss ts ++ es)
mgu' _ _ = Nothing

mgu :: Term -> Term -> Maybe Subst
mgu s t = mgu' IM.empty [(s, t)]

unifiable :: Term -> Term -> Bool
unifiable s t = mgu s t /= Nothing
