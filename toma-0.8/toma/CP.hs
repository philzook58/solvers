module CP where

import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import Data.Maybe
import Control.Monad
import Term
import qualified Rule as R
import qualified CPIndexing as CPI
import Signature
import Equation

type LR a = Either a a

-- critical peak
-- represents _left <-id1- top -id2-> right
data CP = CP {
  _left :: Term,
  _id1 :: LR Int, -- non-root step 
  _id2 :: LR Int, -- root step
  _position :: Position, -- position of id2
  _right :: Term,
  _top :: Term,
  _depth :: Int
}

rename :: (Term, Term) -> (Term, Term) -> ((Term, Term), (Term, Term))
rename (l1, r1) (l2, r2) = ((rho1 l1, rho1 r1), (rho2 l2, rho2 r2))
  where
    vs1 = IS.union (variables l1) (variables r1)
    vs2 = IS.union (variables l2) (variables r2) 
    rho1 t = substitute t (IM.fromList (zip (IS.toList vs1) (map V [0..])))
    rho2 t = substitute t (IM.fromList (zip (IS.toList vs2) (map V [IS.size vs1..])))

tupleLR, tupleRL :: R.Rule -> (Term, Term, R.Orientation, LR Int, Int)
tupleLR rule = (R._lhs rule, R._rhs rule, R._orientation rule, Left (R._id rule), R._depth rule)
tupleRL rule = (R._rhs rule, R._lhs rule, R.Unoriented, Right (R._id rule), R._depth rule)

-- for reconstruction
ecpAt :: LR R.Rule -> Position -> LR R.Rule -> CP
ecpAt rl1 p rl2 =
  case ecpAt' (\_ -> \_ -> False) p (orient rl1) (orient rl2) of
    Just cp -> cp
    Nothing -> error "failed to reconstruct critical pair (bug)"
  where
    orient (Left rl) = tupleLR rl
    orient (Right rl) = tupleRL rl

-- p: position of l2
-- l2 = r2 is applied at root
-- this function does not assume renaming (TODO: renaming every single time is not optimal)
ecpAt' :: (Term -> Term -> Bool) -> Position ->
          (Term, Term, R.Orientation, LR Int, Int) -> (Term, Term, R.Orientation, LR Int, Int) -> Maybe CP
ecpAt' gt p (l1, r1, o1, i1, d1) (l2, r2, o2, i2, d2) = do
  guard (p /= [] || not (variant (l1', r1') (l2', r2')))
  sigma <- mgu l1' (subtermAt l2' p)
  let subst t = substitute t sigma
  guard (o1 == R.Oriented || not (gt (subst r1') (subst l1')))
  guard (o2 == R.Oriented || not (gt (subst r2') (subst l2')))
  let left = subst (replace l2' r1' p)
  let right = subst r2'
  guard (left /= right)
  return (CP {
    _left = left,
    _id1 = i1,
    _id2 = i2,
    _right = right,
    _position = p,
    _top = subst l1',
    _depth = max d1 d2 + 1
  })
  where
    ((l1', r1'), (l2', r2')) = rename (l1, r1) (l2, r2) 

ecpWithIndex :: Signature -> (Term -> Term -> Bool) -> IM.IntMap R.Rule -> CPI.Index -> CPI.Index -> R.Rule -> [CP]
ecpWithIndex sig gt rules idx1 idx2 rl =
  (if R.oriented rl
    then []
    else [ cp | m <- retrieve (R._rhs rl), -- case rl is applied below or at root, right to left (including overlay)
                let rl' = rules IM.! (getId m),
                cp <- maybeToList (ecpAt' gt (getPos m) (tupleRL rl) (orient m rl')) ] ++
         [ cp | (p, u) <- nonRootFunctionPositions' (R._rhs rl), -- case rl is applied at root, right to left (no overlay)
                m <- retrieveRoot u,
                let rl' = rules IM.! (getId m),
                cp <- maybeToList (ecpAt' gt p (orient m rl') (tupleRL rl)) ]) ++
  -- case rl is applied below or at root, left to right (including overlay)
  [ cp | m <- retrieve (R._lhs rl),
         let rl' = rules IM.! (getId m),
         cp <- maybeToList (ecpAt' gt (getPos m) (tupleLR rl) (orient m rl')) ] ++
  -- case rl is applied at root, left to right (no overlay)
  [ cp | (p, u) <- nonRootFunctionPositions' (R._lhs rl),
         m <- retrieveRoot u,
         let rl' = rules IM.! (getId m),
         cp <- maybeToList (ecpAt' gt p (orient m rl') (tupleLR rl)) ]
  where
    getId = either fst fst
    getPos = either snd snd
    orient (Left _) rule = tupleLR rule
    orient (Right _) rule = tupleRL rule
    retrieve u = CPI.retrieve sig u idx1 ++ CPI.retrieve sig u idx2
    retrieveRoot u = CPI.retrieveRoot sig u idx1 ++ CPI.retrieveRoot sig u idx2
