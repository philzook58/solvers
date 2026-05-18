{-# LANGUAGE OverloadedStrings #-}
module Weight where

import qualified Data.Vector as V
import qualified Data.Text as T

import Term
import Signature

-- (w0, w)
type Weight = (Int, V.Vector Int)

-- w0 >= 1 & w(c) >= w0 for all constants c
valid :: Signature -> Weight -> Bool
valid sig (w0, w) = w0 >= 1 && all id [ w V.! c >= w0 | c <- constants sig ]

pp :: Signature -> Weight -> T.Text
pp sig (w0, w) = "w0 = " <> (T.pack (show w0)) <> "; " <>
  T.intercalate "; " (map ppEntry (V.toList (V.indexed w))) 
  where
    ppEntry (f, wf) = 
      let (name', _) = sig V.! f
        in "w(" <> name'  <> ") = " <> (T.pack (show wf))

weight :: Weight -> Term -> Int
weight (w0, _) (V _) = w0
weight w@(_, w') (F f ts) =
  w' V.! f + sum (map (weight w) ts)

defaultWeight :: Signature -> Weight
defaultWeight sig = (1, V.replicate (V.length sig) 1)
