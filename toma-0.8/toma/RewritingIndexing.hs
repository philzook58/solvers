module RewritingIndexing where
-- indexing for forward rewriting and for subsumption

import Term
import Rule
import qualified Indexing as I
import Signature

-- Left i means lhs of rule i can match
-- Right i means rhs of rule i can match 
type Index = ([Position], I.Index (Either Int Int))

empty :: [Position] -> Index
empty ps = (ps, I.empty)

insert :: Rule -> Index -> Index
insert rule (ps, ind)
  | oriented rule = (ps, I.insert (Left (_id rule)) (I.fp (_lhs rule) ps) ind)
  | otherwise = (ps, ind')
  where
    ind' = I.insert (Right (_id rule)) (I.fp (_rhs rule) ps)
            (I.insert (Left (_id rule)) (I.fp (_lhs rule) ps) ind)

retrieve :: Signature -> Term -> Index -> [Either Int Int]
retrieve sig t (ps, ind) = I.retrieveMatchers sig (I.fp t ps) ind

toList :: Index -> [Either Int Int]
toList (_, i) = I.toList i
