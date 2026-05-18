{-# LANGUAGE OverloadedStrings #-}
module TSTP where

import qualified Data.IntSet as IS
import qualified Data.Text as T
import qualified Data.Graph as G
import qualified Data.List as L
import qualified Data.Set as S

import qualified Term
import qualified Rule as R
import Proof
import Signature
import qualified TPTP
import qualified Parsing

data Result =
  -- Theorem contains rules (including axioms and generated), goal, and rule ids used to join the goal
  Theorem [R.Rule] ((Term.Term, Term.Term), Maybe TPTP.Annotation) (Maybe TPTP.EncodingInfo) IS.IntSet | 
  CounterSatisfiable [R.Rule] | -- complete term rewrite system (all oriented)
  GiveUp [R.Rule] [R.Rule] -- (oriented, unoriented)

-- assumption: rules are 1-indexed
-- so we can use 0 for the id of the goal.
relevant :: IS.IntSet -> [R.Rule] -> [R.Rule]
relevant gids rules = [ rl | rl <- rules, IS.member (R._id rl) rele ]
  where
    m = maximum [ R._id rl | rl <- rules ]
    extract (Conversion is) = IS.toList is
    extract (Axiom _) = []
    es = [ (0, i) | i <- IS.toList gids ] ++
         [ (R._id rl, i) | rl <- rules, i <- extract (R._proof rl) ]
    rele = IS.fromList (G.reachable (G.buildG (0, m) es) 0)

pp :: Signature -> Result -> T.Text
pp sig (Theorem rls ((gl, gr), goal_annotation) encoding_info gids) =
  case encoding_info of
    Nothing
      | Just ga <- goal_annotation ->
          header <>
          cnf "g" (0 :: Int) "negated_conjecture" (neqn gl gr) (annotation ga) <> "\n" <>
          T.unlines (map rule2cnf rls') <>
          cnf "g" (1 :: Int) "plain" (eqn gl gr) (conversion [ "c" <> T.pack (show i) | i <- IS.toList gids ]) <> "\n" <>
          cnf "g" (2 :: Int) "plain" "$false" (resolution "g0" "g1") <> "\n" <>
          footer
      | otherwise -> error "annotation must be given to goal"
    Just info
      | ((original_left, original_right), Just anno) <- TPTP._original_goal info ->
          header <>
          cnf "g" (0 :: Int) "negated_conjecture" (TPTP.showTerm original_left <> " != " <> TPTP.showTerm original_right) (annotation anno)  <> "\n" <>
          encode_existential (TPTP._eq info) (TPTP._true info) (TPTP._false info) original_left original_right "g0" <> "\n" <>
          cnf "g" (1 :: Int) "plain" (neqn gl gr) split_conjunct <> "\n" <>
          T.unlines (map rule2cnf rls') <>
          cnf "g" (2 :: Int) "plain" (eqn gl gr) (conversion [ "c" <> T.pack (show i) | i <- IS.toList gids ]) <> "\n" <>
          cnf "g" (3 :: Int) "plain" "$false" (resolution "g1" "g2") <> "\n" <>
          footer
      | otherwise -> error "annotation must be given to (original) goal"
  where
    header = "% SZS status Unsatisfiable\n" <> "% SZS output start CNFRefutation\n"
    footer = "% SZS output end CNFRefutation"
    eqn l r = let vmap = Term.nice_varnames [l, r]
                in Term.pp sig vmap l <> " = " <> Term.pp sig vmap r
    neqn l r =  let vmap = Term.nice_varnames [l, r]
                in Term.pp sig vmap l <> " != " <> Term.pp sig vmap r 
    rls' = L.sortBy (\r1 r2 -> compare (R._id r1) (R._id r2)) (relevant gids rls)
    cnf prefix i role f p =
      "cnf(" <> prefix <> T.pack (show i) <> ", " <>
      role <> ", " <>
      f <> ", " <>
      p <> ")."
    conversion ids = "inference(equational, [status(thm)], [" <> T.intercalate "," ids <> "])" -- better name?
    resolution i1 i2 = "inference(resolution, [status(thm)], [" <> i1 <> ", " <> i2 <> "])"
    split_conjunct = "inference(split_conjunct, [status(thm)], [e])"
    annotation (filename, formulaname, _role) = "file(\'" <> filename <> "\', " <> formulaname <>  ")"
    rule2cnf rl = case R._proof rl of
      Axiom m ->
        case m of
          Just anno -> cnf "c" (R._id rl) "axiom" (eqn (R._lhs rl) (R._rhs rl)) (annotation anno)
          Nothing -> cnf "c" (R._id rl) "plain" (eqn (R._lhs rl) (R._rhs rl)) split_conjunct
      Conversion is ->
         cnf "c" (R._id rl) "plain" (eqn (R._lhs rl) (R._rhs rl)) (conversion [ "c" <> T.pack (show i) | i <- IS.toList is ])
    encode_existential eq t f l r pid =
      "fof(e, plain, ![" <> T.intercalate "," (S.toList vs) <> "]: (" <>
        t <> " != " <> f <> " & " <>
        eq <> "(" <> x <> ", " <> x <> ") = " <> t <> " & " <>
        eq <> "(" <> TPTP.showTerm l <> ", " <> TPTP.showTerm r <> ") = " <> f <> "), " <> 
        "inference(encode_existential, [status(esa)], [" <> pid <> "]))."
      where
        vs = S.union (Parsing.variables l) (Parsing.variables r)
        x = head (S.toList vs)
pp sig (CounterSatisfiable rls) =  
  T.unlines [ "% SZS status Satisfiable",
    "The following TRS is a complete presentation of the axioms, but the goal is not joinable." ] <>
  T.unlines (map (R.pp sig) rls)
pp _sig (GiveUp _ _) = "% SZS status GaveUp"
