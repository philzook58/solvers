module Completion where

import Data.List
import Term
import Rule
import TRS
import Rewriting
import Order
import Control.Monad

data Env = Env { 
  _kOrders :: Int, 
  _nEquations :: Int, 
  _tool :: String,
  _order :: Order.Class
}

-- trsOrSC env E C returns either a complete TRS for E or S(C).
data CompleteTRS_or_Ext = 
    CompleteTRS (TRS, Order.Instance) 
  | Ext TRS deriving Show

type Record = [(Rule, (Int, Int))]

subsumeEq :: Rule -> Rule -> Bool
subsumeEq (s, t) (u, v) =
  match' [] [(s, u), (t, v)] /= Nothing ||
  match' [] [(s, v), (t, u)] /= Nothing

encompassEq :: Rule -> Rule -> Bool
encompassEq e1 e2
  | subsumeEq e1 e2 = True
encompassEq e1 (F h us, F k vs) = 
  h == k && any (encompassEq e1) (zip us vs)
encompassEq _ _ = False

encompassEq' :: Rule -> [Term] -> [Term] -> Bool
encompassEq' e1 (u : us) (v : vs)
  | u == v    = encompassEq' e1 us vs
  | otherwise = encompassEq e1 (u, v) && us == vs
encompassEq' _ _ _ = False

minimal :: TRS -> TRS
minimal []       = []
minimal (e : es) = e : minimal [ e' | e' <- es, not (encompassEq e e') ]

type History = [(Rule, (Int,Int))]

-- Completion without the deduce rule.

interreduce :: Rule -> TRS -> (TRS, TRS)
interreduce _ [] = ([], [])
interreduce rule ((l, r) : trs)
  | l == l'   = (cs, (l, r') : trs')
  | otherwise = ((l', r') : cs, trs')
  where
    l'         = nf [rule] l
    r'         = nf (rule : trs) r
    (cs, trs') = interreduce rule trs

orient :: Order.Instance -> Rule -> (Maybe Rule)
orient oi (s, t)
  | Order.gt oi s t = Just (s, t)
  | Order.gt oi t s = Just (t, s)
  | otherwise       = Nothing

simplify :: Order.Instance -> TRS -> TRS -> TRS -> (TRS, TRS)
simplify _  []       unoriented trs = (unoriented, trs)
simplify oi (e : cs) unoriented trs
  | s == t                    = simplify oi cs unoriented trs
  | Just rule <- orient oi e' =
      let (cs', trs') = interreduce rule trs in
      simplify oi (cs' ++ cs ++ unoriented) [] (rule : trs') 
  | otherwise                 = simplify oi cs (e' : unoriented) trs
  where
    e'@(s, t) = nfEq trs e

psi :: Order.Instance -> TRS -> (TRS, TRS)
psi oi cs = simplify oi cs [] []

select :: Env -> TRS -> TRS
select (Env { _nEquations = n }) cs = 
  take n (sortOn Rule.size cs) 

completeTRS_or_Ext' :: Env -> History -> TRS -> [(TRS,Order.Instance)] -> TRS -> CompleteTRS_or_Ext
completeTRS_or_Ext' env _ cs [] ext =
  Ext (select env (diffES ext cs))
completeTRS_or_Ext' env h cs ((_, oi) : pairs) ext =
  let 
    (cs0, trs') = psi oi cs
    licps = licp trs'
    licps' = normalizeES trs' licps
  in
  if cs0 == [] && licps' == []
    then CompleteTRS (trs', oi)
    else 
      let cs' = nubES (trs' ++ cs0 ++ licps') in
      let ext' = unionES ext cs' in
      completeTRS_or_Ext' env h cs pairs ext'
 
completeTRS_or_Ext :: Env -> History -> TRS -> [(TRS,Order.Instance)] -> CompleteTRS_or_Ext
completeTRS_or_Ext env h cs pairs = completeTRS_or_Ext' env h cs pairs []

-- The main partial function of maximal completion.

elemEq :: Rule -> TRS -> Bool
elemEq (s, t) trs = elem (s, t) trs || elem (t, s) trs

lookupEq :: Rule -> History -> String
lookupEq _    [] = "## ##: "
lookupEq rule ((rule', (j, i)) : a)
  | Rule.variantEq rule rule' = show j ++ " " ++ show i ++ ": "
  | otherwise                 = lookupEq rule a

printC :: History -> TRS -> IO ()
printC h cs = forM_ cs f
  where f e = putStrLn (lookupEq e h ++ "  " ++ showEq e)

phi :: Env -> History -> Order.Class -> Int -> TRS -> TRS -> IO (Maybe (TRS, Order.Instance))
phi env h oc i es cs = do
  pairs <- kOrders (_tool env) oc (_kOrders env) cs
  case pairs of
    [] -> return Nothing
    _ ->
      let trsOrExt = completeTRS_or_Ext env h cs pairs in
      case trsOrExt of
        CompleteTRS pair -> return (Just pair)
        Ext [] -> 
          return Nothing
        Ext ext ->
          let cs' = diffES ext cs in
          let n = length h in
          let h' = h ++ [ (e, (n + j, i)) | (j, e) <- zip [1..] cs' ] in
          let cs'' = unionES cs ext in
          --do printC h' ext
          phi env h' oc (i + 1) es (minimal cs'')

complete :: Env -> TRS -> IO (Maybe (TRS, Order.Instance))
complete env es = do
  m <- phi env h (_order env) 1 es es
  case m of
    Nothing  -> return Nothing
    Just pair -> return (Just pair)
  where 
    h = [ (e, (j, 0)) | (j, e) <- zip [1..] es ]
