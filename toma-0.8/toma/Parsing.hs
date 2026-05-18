{-# LANGUAGE OverloadedStrings #-}
module Parsing where

import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Maybe

import qualified Signature as Sig
import qualified Term as T

-- intermediate data structure for preprocessing.

data Term = V T.Text | F T.Text [Term]
  deriving Eq
type Signature = M.Map T.Text Int -- maps a symbol to its arity

tshow, tshow_aux :: Term -> T.Text
tshow (F f [t1, t2])
  | T.isBinaryOperator f =
      tshow_aux t1 <> " " <> f <> " " <> tshow_aux t2 
tshow t = tshow_aux t
tshow_aux (V x) = x
tshow_aux (F f []) = f
tshow_aux (F f [ V x ])
  | T.isUnaryOperator f = f <> x
tshow_aux (F f [ F g [] ])
  | T.isUnaryOperator f = f <> g
tshow_aux (F f [t1, t2])
  | T.isBinaryOperator f =
      "(" <> tshow_aux t1 <> " " <> f <> " " <> tshow_aux t2 <> ")"
tshow_aux (F f ts) = f <> "(" <> T.intercalate ", " [ tshow t | t <- ts ] <> ")"

instance Show Term where
  show = T.unpack . tshow

variables :: Term -> S.Set T.Text
variables (V x) = S.singleton x
variables (F _ ts) = S.unions [ variables t | t <- ts ]

ground :: Term -> Bool
ground t = S.null (variables t)

functions :: Term -> S.Set (T.Text, Int)
functions (V _) = S.empty
functions (F f ts) = S.insert (f, Prelude.length ts) (S.unions [ functions t | t <- ts ])

signatureOf :: [Term] -> Signature
signatureOf ts = 
  M.fromList (S.toList (S.unions [ functions t | t <- ts ]))

signatureOf' :: [Term] -> Sig.Signature
signatureOf' ts = V.fromList (S.toList (S.unions [ functions t  | t <- ts]))

-- return a fresh function symbol
fresh :: Signature -> T.Text -> T.Text
fresh sig prefix = head (freshes sig prefix)

-- infinitely many fresh symbols
freshes :: Signature -> T.Text -> [T.Text]
freshes sig prefix = [ f | f <- fs , not (M.member f sig) ]
  where
    fs = prefix : [ prefix <> (T.pack (show i)) | i <- [(0 :: Int)..]]

convertTerm :: M.Map T.Text Int -> M.Map T.Text Int -> Term -> T.Term 
convertTerm _ mv (V x)
  | Just x' <- M.lookup x mv = T.V x'
  | otherwise = error ("convertTerm: variable " ++ show x ++ " is not found")
convertTerm mf mv (F f ts)
  | Just f' <- M.lookup f mf = T.F f' ([ convertTerm mf mv t | t <- ts ])
  | otherwise = error ("convertTerm: function " ++ show f ++ " is not found")

match :: Term -> Term -> Bool
match t u
  | Just sol <- match' t u = isJust (build M.empty sol)
  | otherwise = False
  where
    match' (V x) t' = Just [ (x, t') ]
    match' (F f ts) (F g us)
      | f == g = fmap concat (sequence [ match' t' u' | (t', u') <- zip ts us ])
    match' _ _ = Nothing
    build m [] = Just m
    build m ((x, t') : rest) =
      case M.lookup x m of
        Just t'' -> if t' == t'' then build m rest else Nothing
        Nothing -> build (M.insert x t' m) rest

variant :: Term -> Term -> Bool
variant t u = match t u && match u t
