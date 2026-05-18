{-# LANGUAGE OverloadedStrings, RecordWildCards #-}
module Discount where

import qualified Data.Heap as H
import Data.IORef
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Data.Maybe
import Control.Monad

import qualified CP
import Proof
import Rewriting
import qualified Rule as R
import Signature
import Term
import ReductionOrder
import qualified TPTP
import TSTP
import qualified RewritingIndexing as RI
import qualified CPIndexing as CPI
import qualified AC
import qualified Equation
import qualified Connectedness

data Config = Config {
  _cp_config :: CPConfig,
  _cp_verbose :: Bool,
  _simplify_per :: Int,
  _profile_per :: Int,
  _fp :: [Position],
  _quiet :: Bool
}

-- A simplified version of Twee's critical pair scoring.
-- We do not care about multiple occurence of subterms,
-- as it is costly in our naive term representation.
data CPConfig =
  CPConfig {
    cfg_bigweight :: Int,
    cfg_smallweight :: Int,
    cfg_funweight :: Int,
    cfg_varweight :: Int,
    cfg_depthweight :: Int }

defaultCPConfig :: CPConfig
defaultCPConfig =
  CPConfig {
    cfg_bigweight = 4,
    cfg_smallweight = 1,
    cfg_funweight = 7,
    cfg_varweight = 6,
    cfg_depthweight = 16 -- 24? (TODO: adjustment, maybe it is nice to encourage to use axioms)
  }

weight :: CPConfig -> Term -> Int
weight c (V _) = cfg_varweight c
weight c (F _ ts) = cfg_funweight c + sum (map (weight c) ts)

-- hook gives special treatment of a critical pair of a certain form
-- (e.g., eq(u, v) -> false with u and v unifiable)
score :: Config -> (Term -> Term -> Maybe Int) -> Term -> Term -> Int -> Int
score c hook s t depth
  | Just n <- hook s t = n
  | otherwise = 
      hw * cfg_bigweight (_cp_config c) +
      lw * cfg_smallweight (_cp_config c) +
      depth * cfg_depthweight (_cp_config c)
  where
    w1 = weight (_cp_config c) s
    w2 = weight (_cp_config c) t
    hw = max w1 w2
    lw = min w1 w2

-- passive fact
data Passive =
  Ax (Term, Term) (Maybe TPTP.Annotation) | -- axiom
  CP (CP.LR Int) Position (CP.LR Int) -- critical pair (id1, position and id2) to be reconstructed

ax2entry :: Config -> (Term -> Term -> Maybe Int) -> (Term, Term) -> Maybe TPTP.Annotation -> H.Entry Int Passive
ax2entry conf hook (l, r) m = H.Entry (score conf hook l r 0) (Ax (l, r) m)

cp2entry :: Config -> (Term -> Term -> Maybe Int) -> (Term, Term) -> CP.CP -> H.Entry Int Passive
cp2entry conf hook (l, r) cp = H.Entry (score conf hook l r (CP._depth cp)) (CP (CP._id1 cp) (CP._position cp) (CP._id2 cp))

passive2eq :: IM.IntMap R.Rule -> Passive -> (Term, Maybe CP.CP, Term)
passive2eq _ (Ax (s, t) _) = (s, Nothing, t)
passive2eq rules (CP i1 p i2) = (CP._left cp, Just cp, CP._right cp)
  where
    getRule (Left i) = Left (rules IM.! i)
    getRule (Right i) = Right (rules IM.! i)
    cp = CP.ecpAt (getRule i1) p (getRule i2)

-- scp2conversion :: CP.CP -> IS.IntSet -> IS.IntSet
-- scp2conversion cp x = IS.insert (CP._id1 cp) (IS.insert (CP._id2 cp) x)

-- prover state
data State = State {
  _idgen :: IORef Int,
  _active :: IM.IntMap R.Rule, -- TODO: active is IntMap but should be maintained as dynamic vector for optimal performance
  _oriented_rw_index :: RI.Index, -- indexing for rewriting with oriented
  _unoriented_rw_index :: RI.Index, -- indexing for rewriting with unorieted (separated so unoriented could be simplified)
  _oriented_cp_index :: CPI.Index, -- indexing for critical pairs with oriented
  _unoriented_cp_index :: CPI.Index, -- indexing for critical pairs with unorieted (separated so unoriented could be simplified)
  _deleted :: [R.Rule],
  _passive :: H.Heap (H.Entry Int Passive),
  _goal :: (Term, Term),
  _used_for_goal :: IS.IntSet, -- rule ids used for simplifying goal
  _A :: IS.IntSet, -- associative symbols
  _C :: IS.IntSet -- commutative symbols
}

discount :: Signature -> ReductionOrder -> Config -> [((Term, Term), Maybe TPTP.Annotation)] -> ((Term, Term), Maybe TPTP.Annotation) -> Maybe TPTP.EncodingInfo -> IO Result
discount sig to conf axioms goal minfo = do
  g <- newIORef 1
  let initialState = State {
    _idgen = g,
    _active = IM.empty,
    _oriented_rw_index = empty_rw_index, 
    _unoriented_rw_index = empty_rw_index,
    _oriented_cp_index = empty_cp_index,
    _unoriented_cp_index = empty_cp_index,
    _deleted = [],
    _passive = initial_passive,
    _goal = fst goal,
    _used_for_goal = IS.empty, -- rule ids used for simplifying goal
    _A = IS.empty, 
    _C = IS.empty
  }
  loop initialState
  where
    printLnUnlessQuiet txt =
      if _quiet conf then return () else TIO.putStrLn txt
    empty_rw_index = RI.empty (_fp conf)
    empty_cp_index = CPI.empty (_fp conf)
    initial_passive = H.fromList [ ax2entry conf hook (l, r) m | ((l, r), m) <- axioms ]
    hook :: Term -> Term -> Maybe Int
    hook -- a critical pair eq(v, w) = false with v and w unifiable immediately proves the goal true = false.
      | Just info <- minfo =
          let eq_id = Signature.findId sig (TPTP._eq info)
              true_id = Signature.findId sig (TPTP._true info)
              false_id = Signature.findId sig (TPTP._false info)
          in \s t -> case (s, t) of
                       (F i1 [s1, s2], F i2 [])
                         | i1 == eq_id, i2 == false_id, unifiable s1 s2 -> return 1
                       (F i1 [], F i2 [t1, t2])
                         | i1 == false_id, i2 == eq_id, unifiable t1 t2 -> return 1
                       (F i1 [], F i2 [])
                         | (i1 == true_id && i2 == false_id) ||  (i1 == false_id && i2 == true_id) ->
                              return 0 -- do not forget, otherwise eq(v, w) = false can be chosen again
                       _ -> Nothing
      | otherwise = \_ _ -> Nothing
    subsumed (t, u) rules unoriented_index =
      listToMaybe [ either id id e | e <- RI.retrieve sig t unoriented_index, check e ]
      where
        check (Left i) = let rl = rules IM.! i in (R._lhs rl, R._rhs rl) `Equation.subsumes` (t, u)
        check (Right i) = let rl = rules IM.! i in (R._rhs rl, R._lhs rl) `Equation.subsumes` (t, u)
    connected _ Nothing _ _ = False
    connected t (Just CP.CP{..}) u State{..} = -- TODO: avoid unneccesary comparison
      gt to _top t && gt to _top u && Connectedness.connected to sig _active _oriented_rw_index _unoriented_rw_index t _top u
    -- TODO: Martin and Nipkow
    redundant (t, u) State{..} =
      t == u || isJust (subsumed (t, u) _active _unoriented_rw_index) || AC.redundant to _A _C (t, u)
    issueId gen = do
      i <- readIORef gen
      modifyIORef gen (+1)
      return i
    orient i t u d rule_ids
      | IS.null rule_ids = error "orient: rule_ids must not be null (bug)"
      | otherwise =
          if gt to u t
            then R.Rule { R._id = i,
                          R._orientation = R.Oriented,
                          R._lhs = u,
                          R._rhs = t,
                          R._proof = Conversion rule_ids,
                          R._depth = d }
            else R.Rule { R._id = i,
                          R._orientation = if gt to t u then R.Oriented else R.Unoriented,
                          R._lhs = t,
                          R._rhs = u,
                          R._proof = Conversion rule_ids,
                          R._depth = d }
    -- input: t' *<-X- t ≈ u -Y->* u, where t ≈ u is axiom or simplified critical pair
    -- output: (parent, child), where child is active rule, and parent is purely for proof reconstruction 
    doOrient idgen (t, x, t') (u, y, u') (Ax _ m) Nothing -- number of calls of t > u could be optimized...
      | IS.null (IS.union x y), not (gt to u t) = do
          i <- issueId idgen
          let rl = R.Rule {
            R._id = i,
            R._orientation = if gt to t u then R.Oriented else R.Unoriented,
            R._lhs = t,
            R._rhs = u,
            R._proof = Axiom m,
            R._depth = 0
          }
          return (rl, Nothing)
      | otherwise = do 
        i1 <- issueId idgen
        let parent = R.Rule {
            R._id = i1,
            R._orientation = R.Unoriented,
            R._lhs = t,
            R._rhs = u,
            R._proof = Axiom m,
            R._depth = 0
          }
        i2 <- issueId idgen
        let rl = orient i2  t' u' 0 (IS.insert i1 (IS.union x y))
        return (rl, Just parent)
    doOrient idgen (_, x, t') (_, y, u') (CP i1 _ i2) (Just cp) = do
      i <- issueId idgen
      let getId = either id id
      let rl = orient i  t' u' (CP._depth cp) (IS.unions [ x, y, IS.fromList [ getId i1, getId i2 ] ])
      -- just for investigating potentially redundant critical pairs
      if _cp_verbose conf && not (R.oriented rl) && gt to (CP._top cp) t' && gt to (CP._top cp) u'
        then printLnUnlessQuiet ("  (" <> T.pack (show i) <> " is potentially connected below " <> Term.pp' sig (nice_varnames [CP._top cp]) (CP._top cp) <> ")")
        else return ()
      if _cp_verbose conf && not (R.oriented rl)
        then printLnUnlessQuiet ("  (" <> T.pack (show i) <> " is from " <> T.pack (show (CP._id1 cp)) <> " and " <> T.pack (show (CP._id2 cp)) <> ")")
        else return ()
      return (rl, Nothing)
    doOrient _ _ _ _ _ = error "doOrient: something wrong happened (bug)"
    reportDeletion i = printLnUnlessQuiet ("  (delete " <> T.pack (show i) <> ")")
    orientedRules rules = [ rule | (_, rule) <- IM.toList rules, R.oriented rule ]
    unorientedRules rules =  [ rule | (_, rule) <- IM.toList rules, not (R.oriented rule) ]
    active2Rules actives = map snd (IM.toList actives)
    insertRule rl rules = IM.insert (R._id rl) rl rules
    nextA as (t, u)
      | Just f <- AC.aof (t, u) = do
          printLnUnlessQuiet ("  (" <> name sig f <> " is associative)")
          return (IS.insert f as)
      | otherwise = return as
    nextC cs (t, u)
      | Just f <- AC.cof (t, u) = do
          printLnUnlessQuiet ("  (" <> name sig f <> " is commutative)")
          return (IS.insert f cs)
      | otherwise = return cs
    hasParents (Ax _ _) _ = True
    hasParents (CP i1 _ i2) active = IM.member (getId i1) active && IM.member (getId i2) active
      where
        getId = either id id
    loop st@State{..} =
      case H.uncons _passive of
        Nothing
          | null (unorientedRules _active) -> return (CounterSatisfiable (orientedRules _active))
          | otherwise -> return (GiveUp (orientedRules _active) (unorientedRules _active))
        Just (H.Entry _ p, passive') ->
          let (t, mcp, u) = passive2eq _active p
              (t', used_t) = nfWithIndex sig (gt to) _active _oriented_rw_index _unoriented_rw_index t
              (u', used_u) = nfWithIndex sig (gt to) _active _oriented_rw_index _unoriented_rw_index u
              st' = State { -- the same except for _passive
                _idgen = _idgen, _active = _active, _oriented_rw_index = _oriented_rw_index,
                _unoriented_rw_index = _unoriented_rw_index, _oriented_cp_index = _oriented_cp_index,
                _unoriented_cp_index = _unoriented_cp_index, _A = _A, _C = _C, _deleted = _deleted,
                _goal = _goal, _used_for_goal = _used_for_goal, _passive = passive'
              }
          in
            if not (hasParents p _active) || redundant (t', u') st || connected t' mcp u' st
              then loop st'
              else do
                (rl, mparent) <- doOrient _idgen (t, used_t, t') (u, used_u, u') p mcp
                let active_next = insertRule rl _active
                let (oriented_rw_index_next, unoriented_rw_index_next) =
                      if R.oriented rl
                        then (RI.insert rl _oriented_rw_index, _unoriented_rw_index)
                        else (_oriented_rw_index, RI.insert rl _unoriented_rw_index)
                let (oriented_cp_index_next, unoriented_cp_index_next) =
                      if R.oriented rl
                        then (CPI.insert rl _oriented_cp_index, _unoriented_cp_index)
                        else (_oriented_cp_index, CPI.insert rl _unoriented_cp_index)
                let deleted_next = maybeToList mparent ++ _deleted
                forM_ mparent (\parent -> printLnUnlessQuiet (R.pp sig parent))
                printLnUnlessQuiet (R.pp sig rl)
                forM_ mparent (\parent -> reportDeletion (R._id parent))
                -- update AC
                _A_next <- nextA _A (t', u')
                _C_next <- nextC _C (t', u')
                -- critical pair generation:
                -- for all critical pairs cp between t = u and R ∪ { t = u }
                --   normalize cp using only the oriented rules of R
                --   add cp to Q if cp is non-trivial
                let cps = [ cp2entry conf hook (l, r) cp
                          | cp <- CP.ecpWithIndex sig (gt to) active_next oriented_cp_index_next unoriented_cp_index_next rl,
                            let (l, _) = nfWithIndex sig (gt to) active_next oriented_rw_index_next empty_rw_index (CP._left cp),
                            let (r, _) = nfWithIndex sig (gt to) active_next oriented_rw_index_next empty_rw_index (CP._right cp),
                            l /= r ]
                let passive_next = foldr H.insert passive' cps
                let (lg, used_l) = nfWithIndex sig (gt to) active_next oriented_rw_index_next unoriented_rw_index_next (fst _goal)
                let (rg, used_r) = nfWithIndex sig (gt to) active_next oriented_rw_index_next unoriented_rw_index_next (snd _goal)
                let used_for_goal_next = IS.unions [ _used_for_goal, used_l, used_r ]
                let nextState = State {
                  _idgen = _idgen, _active = active_next, _oriented_rw_index = oriented_rw_index_next, _unoriented_rw_index = unoriented_rw_index_next,
                  _oriented_cp_index = oriented_cp_index_next, _unoriented_cp_index = unoriented_cp_index_next,
                  _deleted = deleted_next, _passive = passive_next, _goal = (lg, rg), _used_for_goal = used_for_goal_next,
                  _A = _A_next, _C = _C_next
                }
                -- profiling
                if (R._id rl) `mod` (_profile_per conf) == 0
                  then printLnUnlessQuiet ("  (" <> (T.pack (show (IM.size active_next))) <> " actives and " <> (T.pack (show (H.size passive_next))) <> " passives)")
                  else return () 
                if lg == rg
                  then return (Theorem (active2Rules active_next ++ deleted_next) goal minfo used_for_goal_next)
                  else case subsumed (lg, rg) active_next unoriented_rw_index_next of
                        Just i -> return (Theorem (active2Rules active_next ++ deleted_next) goal minfo (IS.insert i used_for_goal_next))
                        -- simplify unoriented rules (sometimes)
                        Nothing -> if (R._id rl) `mod` (_simplify_per conf) == 0 then simplify nextState else loop nextState
    -- simplify all unoriented rules and then go to the next loop
    -- note that it reconstructs rewriting & critical pair indexing (TODO: avoid this)
    simplify State{..} = do
      printLnUnlessQuiet ("  (simplifying unoriented rules...)")
      let unoriented_ids = IS.toList (IS.fromList [ either id id m | m <- RI.toList (_unoriented_rw_index) ])
      simplify' unoriented_ids (State {
        -- initalize
        _unoriented_rw_index = empty_rw_index, _unoriented_cp_index = empty_cp_index,
        -- following are same
        _idgen = _idgen, _oriented_rw_index = _oriented_rw_index, _oriented_cp_index = _oriented_cp_index,
        _goal = _goal, _used_for_goal = _used_for_goal, _passive = _passive,
        _A = _A, _C = _C, _deleted = _deleted, _active = _active
      })
    simplify' [] st = do
      printLnUnlessQuiet ("  (simplified unoriented rules!)")
      loop st
    simplify' (i : rest) st@State{..} = do
      let rl = _active IM.! i
      let (lhs, used_l) = nfWithIndex sig (gt to) _active _oriented_rw_index empty_rw_index (R._lhs rl)
      let (rhs, used_r) = nfWithIndex sig (gt to) _active _oriented_rw_index empty_rw_index (R._rhs rl)
      if redundant (lhs, rhs) st 
        then do
          reportDeletion i
          simplify' rest (State {
            _deleted = rl : _deleted, _active = IM.delete i _active,
            -- following are same
            _idgen = _idgen, _oriented_rw_index = _oriented_rw_index, _oriented_cp_index = _oriented_cp_index,
            _goal = _goal, _used_for_goal = _used_for_goal, _passive = _passive, _A = _A, _C = _C,
            _unoriented_rw_index = _unoriented_rw_index, _unoriented_cp_index = _unoriented_cp_index
          })
        else if IS.null (IS.union used_l used_r) 
          then
            simplify' rest (State {
              _unoriented_rw_index = RI.insert rl _unoriented_rw_index,
              _unoriented_cp_index = CPI.insert rl _unoriented_cp_index,
              -- following are same
              _idgen = _idgen, _oriented_rw_index = _oriented_rw_index, _oriented_cp_index = _oriented_cp_index,
              _goal = _goal, _used_for_goal = _used_for_goal, _passive = _passive, _A = _A, _C = _C,
              _deleted = _deleted, _active = _active
            })
          else do
            reportDeletion i
            i' <- issueId _idgen
            let rl' = orient i' lhs rhs (R._depth rl) (IS.insert i (IS.union used_l used_r))
            printLnUnlessQuiet (R.pp sig rl')
            _A_next <- nextA _A (lhs, rhs)
            _C_next <- nextC _C (lhs, rhs)
            let nextState = State {
              _active = IM.insert i' rl' (IM.delete i _active),
              _deleted = rl : _deleted,
              _oriented_rw_index = if R.oriented rl' then RI.insert rl' _oriented_rw_index else _oriented_rw_index,
              _oriented_cp_index = if R.oriented rl' then CPI.insert rl' _oriented_cp_index else _oriented_cp_index,
              _unoriented_rw_index = if R.oriented rl' then _unoriented_rw_index else RI.insert rl' _unoriented_rw_index,
              _unoriented_cp_index =  if R.oriented rl' then _unoriented_cp_index else CPI.insert rl' _unoriented_cp_index,
              _A = _A_next, _C = _C_next,
              -- following are same
              _idgen = _idgen, _goal = _goal, _used_for_goal = _used_for_goal, _passive = _passive
            }
            simplify' rest nextState
