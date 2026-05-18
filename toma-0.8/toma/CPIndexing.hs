module CPIndexing where
-- indexing for critical pairs

import Term
import Rule
import qualified Indexing as I
import Signature

-- first is type of fingerprinting
-- second is for root
-- third is for non-root position: (rule_id, p) with p potentially unifiable
type Index = ([Position], I.Index (RL Int), I.Index (RL (Int, Position)))
type RL a = Either a a

empty :: [Position] -> Index
empty ps = (ps, I.empty, I.empty)

insert :: Rule -> Index -> Index
insert rule (ps, ind1, ind2)
  | oriented rule = (ps, ind1', insertLeftAll ind2)
  | otherwise = (ps, ind1'', insertRightAll (insertLeftAll ind2))
  where
    ind1' = I.insert (Left (_id rule)) (I.fp (_lhs rule) ps) ind1
    ind1'' = I.insert (Right (_id rule)) (I.fp (_rhs rule) ps) ind1'
    insertLeft (q, t) = I.insert (Left (_id rule, q)) (I.fp t ps)
    insertRight (q, t) = I.insert (Right (_id rule, q)) (I.fp t ps)
    insertLeftAll idx = foldr insertLeft idx (nonRootFunctionPositions' (_lhs rule))
    insertRightAll idx = foldr insertRight idx (nonRootFunctionPositions' (_rhs rule))

retrieveRoot :: Signature -> Term -> Index -> [RL (Int, Position)]
retrieveRoot sig t (ps, ind1, _) = map addPos (I.retrieveUnifiables sig (I.fp t ps) ind1)
  where
    addPos (Left i) = Left (i, [])
    addPos (Right i) = Right (i, [])

retrieve :: Signature -> Term -> Index -> [RL (Int, Position)]
retrieve sig t (ps, ind1, ind2) =
  map addPos (I.retrieveUnifiables sig (I.fp t ps) ind1) ++ I.retrieveUnifiables sig (I.fp t ps) ind2
  where
    addPos (Left i) = Left (i, [])
    addPos (Right i) = Right (i, [])
