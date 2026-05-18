{-# LANGUAGE OverloadedStrings #-}

module Precedence where

import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Map as M

import IntMultiSet as IMS
import Signature
import Term hiding (pp')

type Precedence = V.Vector Int

pp :: Signature -> Precedence -> T.Text
pp sig prec = pp' (reverse (L.sortOn snd (V.toList (V.indexed prec)))) 
  where
    pp' [] = ""
    pp' [(f, _)] = name sig f
    pp' ((f, m) : (g, n) : l')
      | m > n = name sig f <> " > " <> pp' ((g, n) : l')
      | m == n = name sig f <> " ~ " <> pp' ((g, n) : l')
      | otherwise = error ("pp: a bug is found while pretty-printing " ++ show prec)

geq :: Precedence -> Int -> Int -> Bool
geq m f1 f2 = (m V.! f1) >= (m V.! f2)

geq_term :: Precedence -> Term -> Term -> Bool
geq_term m (F f _) (F g _) = geq m f g
geq_term _ _ _ = error "geq_term: arguments must be non-variables"

gt :: Precedence -> Int -> Int -> Bool
gt m f1 f2 = (m V.! f1) > (m V.! f2)

gt_term :: Precedence -> Term -> Term -> Bool
gt_term m (F f _) (F g _) = gt m f g
gt_term _ _ _ = error "gt_term: arguments must be non-variables"

-- frequency-based total precedence
-- the more frequent, the higher 
frequencyAsc :: Signature -> [Term] -> Precedence
frequencyAsc sig ts =
  V.fromList [ getPrecedence i | i <- [0..(V.length sig -1 )] ]
  where
    c = IMS.unions [ countFunctions t | t <- ts ]
    ranking = M.fromList (zip (L.sortBy (\i j -> compare (IMS.occur i c) (IMS.occur j c)) [0 .. V.length sig - 1]) [0..])
    getPrecedence i
      | Just p <- M.lookup i ranking = p
      | otherwise = error "frequencyAsc: something wrong happened"

frequencyDesc :: Signature -> [Term] -> Precedence
frequencyDesc sig ts = 
  V.map (\n -> (V.length sig - 1) - n ) (frequencyAsc sig ts)
