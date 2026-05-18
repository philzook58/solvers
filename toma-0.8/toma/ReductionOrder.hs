module ReductionOrder where

import qualified Data.Text as T
import Control.Monad
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.List.Split as Split
import Data.Maybe

import qualified Algebra
import Term
import qualified KBO
import qualified SPO
import qualified GWPO
import qualified MGWPO
import qualified LPO
import qualified SPOEncoding
import qualified GWPOEncoding
import qualified MGWPOEncoding
import qualified KBOEncoding
import Signature
import SMT
import Equation

data ReductionOrder =
    KBO KBO.Param
  | LPO LPO.Param
  | SPO SPO.Param
  | GWPO GWPO.Param
  | MGWPO MGWPO.Param

data Class =
    KB
  | LP
  | WP Algebra.Class
  | GWP Algebra.Class
  | MGWP Algebra.Class Algebra.Class
  | SP [Algebra.Class] -- LPO is represented by SP []
  deriving Eq

instance Show Class where
  show KB = "KBO"
  show LP = "LPO"
  show (WP _) = "WPO"
  show (GWP _) = "GWPO"
  show (MGWP _ _) = "MGWPO"
  show (SP [_]) = "SPO"
  show (SP as) = "SPO with " ++ show (length as) ++ " algebras"

-- the smaller, the less complex
-- (to be abolished?)
instance Ord Class where
  KB <= KB = True
  KB <= WP _ = True
  KB <= GWP _ = True
  KB <= SP _ = True
  GWP _ <= GWP _ = True -- not sure if this is right
  GWP _ <= SP _ = True
  SP as <= SP bs = length as <= length bs 
  _ <= _ = False

toClass :: String -> Class
toClass "kbo" = KB
toClass "lpo" = LP
toClass ('s' : 'p' : 'o' : rest) = SP [ Algebra.toClass c | c <- rest ]
toClass ('g' : 'w' : 'p' : 'o' : c : []) = GWP (Algebra.toClass c)
toClass ('m' : 'g' : 'w' : 'p' : 'o' : c1 : c2 : []) = MGWP (Algebra.toClass c1) (Algebra.toClass c2)
toClass ('w' : 'p' : 'o' : c : []) = WP (Algebra.toClass c)
toClass o = error (o ++ " is not supported")

toClasses :: String -> [Class]
toClasses s = map toClass (Split.splitOn "," s)

pp :: Signature -> ReductionOrder -> T.Text
pp sig (KBO param) = KBO.pp sig param
pp sig (SPO param) = SPO.pp sig param
pp sig (GWPO param) = GWPO.pp sig param
pp sig (MGWPO param) = MGWPO.pp sig param
pp sig (LPO param) = LPO.pp sig param

gt :: ReductionOrder -> Term -> Term -> Bool
gt (KBO p) = KBO.gt p
gt (LPO p) = LPO.gt p
gt (SPO p) = SPO.gt p 
gt (GWPO p) = GWPO.gt p 
gt (MGWPO p) = MGWPO.gt p

-- encoder for finding reduction order via SMT solving.
data Encoder = Encoder {
 _side_condition :: Signature -> Formula,
 _gt :: Term -> Term -> Formula,
 _decode :: Model -> Signature -> ReductionOrder
}

encoder :: Class -> [(Term.Term, Term.Term)] -> ReductionOrder.Encoder
encoder KB possible = Encoder {
  _side_condition = KBOEncoding.side_condition possible,
  _gt = KBOEncoding.gt,
  _decode = decode
}
  where
    decode m sig = KBO (KBOEncoding.decode m sig)
encoder LP possible = Encoder {
  _side_condition = SPOEncoding.side_condition [e] possible,
  _gt = SPOEncoding.gt [e],
  _decode = decode
}
  where
    e = Algebra.encoder Algebra.P 1
    decode m sig = LPO (Algebra.toPrecedence (head (SPOEncoding.decode [e] m sig)))
encoder (SP cs) possible = Encoder {
  _side_condition = SPOEncoding.side_condition es possible,
  _gt = SPOEncoding.gt es,
  _decode = decode
}
  where
    decode m sig = SPO (SPOEncoding.decode es m sig)
    es = [ Algebra.encoder ci i | (i, ci) <- zip [0..] cs ]
encoder (GWP c) possible = Encoder {
  _side_condition = GWPOEncoding.side_condition e possible,
  _gt = GWPOEncoding.gt,
  _decode = decode
}
  where
    decode m sig = GWPO (GWPOEncoding.decode e m sig)
    e = Algebra.encoder c 1
encoder (WP c) possible = Encoder {
  _side_condition = MGWPOEncoding.side_condition (e1, e2) possible,
  _gt = MGWPOEncoding.gt (e1, e2),
  _decode = decode
}
  where
    decode m sig = MGWPO (MGWPOEncoding.decode (e1, e2) m sig)
    e1 = Algebra.encoder c 1
    e2 = Algebra.encoder Algebra.P 2
encoder (MGWP c1 c2) possible = Encoder {
  _side_condition = MGWPOEncoding.side_condition (e1, e2) possible,
  _gt = MGWPOEncoding.gt (e1, e2),
  _decode = decode
}
  where
    decode m sig = MGWPO (MGWPOEncoding.decode (e1, e2) m sig)
    e1 = Algebra.encoder c1 1
    e2 = Algebra.encoder c2 2

defaultOrder :: [Class] -> Signature -> [Term] -> ReductionOrder
defaultOrder [KB] sig ts = KBO (KBO.frequencyAsc sig ts)
defaultOrder [LP] sig ts = LPO (LPO.frequencyAsc sig ts) 
defaultOrder [x] _ _ = error ("default is not supported for " ++ show x)
defaultOrder [] _ _ = error "no order class is given"
defaultOrder _ _ _ = error "provide exactly one class"

frequencyAsc, frequencyDesc :: [Class] -> Signature -> [Term] -> ReductionOrder
frequencyAsc [KB] sig ts = KBO (KBO.frequencyAsc sig ts)
frequencyAsc [LP] sig ts = LPO (LPO.frequencyAsc sig ts) 
frequencyAsc [x] _ _ = error ("frequency asc is not supported for " ++ show x)
frequencyAsc [] _ _ = error "no order class is given"
frequencyAsc _ _ _ = error "provide exactly one class"
frequencyDesc [KB] sig ts = KBO (KBO.frequencyDesc sig ts)
frequencyDesc [LP] sig ts = LPO (LPO.frequencyDesc sig ts) 
frequencyDesc [x] _ _ = error ("frequency desc is not supported for " ++ show x)
frequencyDesc [] _ _ = error "no order class is given"
frequencyDesc _ _ _ = error "provide exactly one class"

orientAll :: [Class] -> Signature -> [(Term, Term)] -> IO (Maybe ReductionOrder)
orientAll [] _ _ = error "no order class is given"
orientAll [c] sig rules = do
  result <- SMT.sat "z3" (conj (_side_condition e sig : [ _gt e s t | (s, t) <- rules ]))
  case result of
    Just m -> return (Just (_decode e m sig))
    Nothing -> return Nothing
  where
    e = encoder c rules
orientAll _ _ _ = error "selection among multiple classes is not supported for orient all"

maxOrient :: [Class] -> Signature -> [(Term, Term)] -> IO (Maybe ReductionOrder)
maxOrient [] _ _ = error "no order class is given"
maxOrient [c] sig rules = do
  result <- SMT.maxsat "z3" (_side_condition e sig) [ disj [ _gt e s t, _gt e t s ] | (s, t) <- rules ]
  case result of
    Just m -> return (Just (_decode e m sig))
    Nothing -> return Nothing
  where
    e = encoder c rules
maxOrient _ _ _ = error "selection among multiple classes is not supported for max orient"

-- orient is, for example, to force eq(X, X) > true & eq(s, t) > false & true > false
minimizeCP :: [Class] -> Signature -> [(Term, Term)] -> [(Term, Term)] -> IO (Maybe ReductionOrder)
minimizeCP classes sig rules orient = do
  mos <- mapM invoke classes
  case L.sortOn (\(_, sc, cl) -> (-sc, cl)) (catMaybes mos) of -- the smaller the better
    (o, _, _) : _ -> return (Just o)
    _ -> return Nothing
  where
    invoke cls = do
      let e = encoder cls possible
      let soft = [ SMT.disj [ _gt e r1 l1, _gt e r2 l2 ] | ((r1, l1), (r2, l2)) <- cps ]
      result <- SMT.maxsat "z3" (conj (_side_condition e sig : [ _gt e l r | (l, r) <- orient ] )) soft
      case result of
        Just m -> return (Just (_decode e m sig, score m soft, cls))
        Nothing -> return Nothing
    rules' = rules ++ [ (r, l) | (l, r) <- rules ] 
    cps = concat [ cp rule1' rule2' | rule1 <- rules', rule2 <- rules', let (rule1', rule2') = rename rule1 rule2 ]
    possible = orient ++ [ c | (p1, p2) <- cps, c <- [p1, p2] ]
    cp (l1, r1) (l2, r2) = do
      p <- functionPositions l2
      guard (p /= [] || not (variant (l1, r1) (l2, r2)))
      guard (unifiable l1 (subtermAt l2 p))
      return ((r1, l1), (r2, l2)) -- no critical pair if r1 > l1 or r2 > l2 holds
      -- NOTE, needs rethink: we should not compare instances of rules, otherwise constraint solving takes too much time (?)
      -- sigma <- maybeToList (mgu l1 (subtermAt l2 p))
      -- let subst t = substitute t sigma
      -- let (l1', r1', l2', r2') = (subst l1, subst r1, subst l2, subst r2)
      -- return ([ (r1', l1'), (r2', l2') ], SMT.disj [ _gt e r1' l1', _gt e r2' l2' ])
    score m soft = sum [ if SMT.evalFormula m s then 1 :: Int else 0 | s <- soft ]
    rename (l1, r1) (l2, r2) =
      let vs1 = IS.union (Term.variables l1) (Term.variables r1)
          vs2 = IS.union (Term.variables l2) (Term.variables r2)
          rho1 = IM.fromList (zip (IS.toList vs1) (map V [0..]))
          rho2 = IM.fromList (zip (IS.toList vs2) (map V [IS.size vs1 ..]))
        in ((substitute l1 rho1, substitute r1 rho1), (substitute l2 rho2, substitute r2 rho2))
