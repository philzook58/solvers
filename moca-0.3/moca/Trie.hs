module Trie where

import Terms
import Substitutions
import Data.List
import FingerPrint
import Rules

import Debug.Trace

type OTRST = (OTRS, Trie)
type XOTRST = (XOTRS, Trie)

data Trie = Node [EquationOrRule] [(Feature, Trie)]
instance Show Trie where
  show trie = intercalate "\n" [ "<" ++ showFeatures features ++ "> \n" ++ showERs ers 
                               | (features, ers) <- listOfFeaturesAndERS trie ]

listOfFeaturesAndERS :: Trie -> [([Feature], [EquationOrRule])]
listOfFeaturesAndERS trie = listOfFeaturesAndERS1 [] trie
listOfFeaturesAndERS1 :: [Feature] -> Trie -> [([Feature], [EquationOrRule])]
listOfFeaturesAndERS1 fs (Node ers [])  = [(fs, ers)]
listOfFeaturesAndERS1 fs (Node [] fts)  = [ (fs, ers) 
                                          | (f, t) <- fts, (fs, ers) <- listOfFeaturesAndERS1 (fs ++ [f]) t ]

createTrie :: OTRS -> OTRST
createTrie o@(es, trs, _) = (o, appendERs (Node [] []) (mixOfESAndTRS es trs))

append :: Trie -> [Feature] -> EquationOrRule -> Trie
append (Node ers fts) []        er  = Node (er : ers) fts
append (Node ers fts) (f : fs)  er  
  | Just trie' <- lookup f fts      = Node ers ((f, append trie'        fs er) : fts')
  | otherwise                       = Node ers ((f, append (Node [] []) fs er) : fts)
  where fts' = [ (f2, t) | (f2, t) <- fts, f /= f2 ]

appendER :: Trie -> EquationOrRule -> Trie
appendER trie (R (l, r)) = append trie (features l) (R (l, r))
appendER trie (E (l, r)) = append (append trie (features l) (E (l, r))) (features r) (E (r, l))

appendERs :: Trie -> [EquationOrRule] -> Trie
appendERs trie []         = trie
appendERs trie (er : ers) = appendERs (appendER trie er) ers




getMatchRules :: Trie -> Term -> [EquationOrRule]
getMatchRules trie t = getMatchRules2 trie (features t)
getMatchRules2 :: Trie -> [Feature] -> [EquationOrRule]
getMatchRules2 (Node ers [])  []         = ers
getMatchRules2 (Node ers fts) (f1 : fs1) = [ er | (f2, trie) <- fts, 
                                                  isMatch f1 f2, 
                                                  er <- getMatchRules2 trie fs1] 

-- 1st : feature of t, 2nd : feature of l in es
isMatch :: Feature -> Feature -> Bool
isMatch _           B           = True
isMatch B           _           = False
isMatch N           N           = True
isMatch N           _           = False
isMatch _           N           = False
isMatch _           A           = True
isMatch A           _           = False
isMatch (FSymbol f) (FSymbol g) = f == g

getUnifiableRules :: Trie -> Term -> [EquationOrRule]
getUnifiableRules trie t = getUnifiableRules2 trie (features t)
getUnifiableRules2 :: Trie -> [Feature] -> [EquationOrRule]
getUnifiableRules2 (Node ers [])  []         = ers
getUnifiableRules2 (Node ers fts) (f1 : fs1) = [ er | (f2, trie) <- fts, 
                                                      isUnifiable f1 f2, 
                                                      er <- getUnifiableRules2 trie fs1] 

isUnifiable :: Feature -> Feature -> Bool
isUnifiable _           B           = True
isUnifiable B           _           = True
isUnifiable N           N           = True
isUnifiable N           _           = False
isUnifiable _           N           = False
isUnifiable _           A           = True
isUnifiable A           _           = True
isUnifiable (FSymbol f) (FSymbol g) = f == g

isUnifiableFeatures :: [Feature] -> [Feature] -> Bool
isUnifiableFeatures fs1 fs2 = and [ isUnifiable f1 f2 | (f1, f2) <- zip fs1 fs2 ]
