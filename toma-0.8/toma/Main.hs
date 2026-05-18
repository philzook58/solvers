{-# LANGUAGE OverloadedStrings #-}

import System.Environment
import qualified Data.List as L
import qualified Data.Text.IO as TIO
import qualified Data.Text as Text
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector as V
import Options.Applicative
import Data.Time.Clock (getCurrentTime)

import qualified ARI
import qualified Parsing as P
import qualified TPTP
import Discount
import qualified ReductionOrder as RO
import qualified TSTP
import qualified Term
import Logging
import qualified Indexing
import qualified INF
import Signature
import qualified Rule

data Opt = Opt { 
  _order_class :: String,
  _order_constraint_file :: Maybe String,
  _tptp_file :: Maybe String,
  _inf_file :: Maybe String,
  _order_selection :: String,
  _quiet :: Bool,
  -- expert options
  _fp :: String,
  _simplify_per :: Int,
  _profile_per :: Int,
  _cp_verbose :: Bool, -- detailed information of critical pairs
  _cp_bigweight :: Int,
  _cp_smallweight :: Int,
  _cp_funweight :: Int,
  _cp_varweight :: Int,
  _cp_depthweight :: Int
}

option_spec :: Parser Opt
option_spec = Opt
  <$> strOption 
    (long "order-class"
     <> short 'o'
     <> metavar "CLASS"
     <> value "kbo"
     <> help ("kbo, lpo, wpoA, gwpoA, mgwpoAA, spoA*, where A = L | M | P")
     <> showDefault)
  <*> optional (strOption
    (long "orient"
     <> metavar "TRS"
     <> help "TRS file given in ARI format"))
  <*> optional (strArgument
    (metavar "TARGET"
     <> help "target file in TPTP format"))
  <*> optional (strOption
    (long "inf"
     <> metavar "INF"
     <> help "infeasibility problem given in ARI format"))
  <*> strOption 
    (long "order-selection"
     <> metavar "STRAT"
     <> value "default"
     <> help ("default, mincp, maxorient, freq{asc,desc}, orientall")
     <> showDefault)
  <*> switch
    (long "quiet"
     <> short 'q'
     <> help "whether to be quiet"
     <> showDefault)
  <*> strOption 
    (long "fp"
     <> metavar "FINGERPRINT"
     <> value "6m"
     <> help ("1, 2, 3d, 4m, 5m, 6m, 7, 8x2")
     <> showDefault)
  <*> option auto
    (long "simplify-per"
     <> metavar "N"
     <> help "simplify unoriented with oriented per N new rules"
     <> value 250
     <> showDefault)
  <*> option auto
    (long "profile-per"
     <> metavar "N"
     <> help "report profile per N new rules"
     <> value 100
     <> showDefault)
  <*> switch
    (long "cp-verbose"
     <> help "whether to be verbose about critical pairs"
     <> showDefault)
  <*> option auto
    (long "cp-bigweight"
     <> metavar "N"
     <> help "weight for a bigger term (for critical pair scoring)"
     <> value 4
     <> showDefault)
  <*> option auto
    (long "cp-smallweight"
     <> metavar "N"
     <> help "weight for a smaller term (for critical pair scoring)"
     <> value 1
     <> showDefault)
  <*> option auto
    (long "cp-funweight"
     <> metavar "N"
     <> help "weight for function symbols (for critical pair scoring)"
     <> value 7
     <> showDefault)
  <*> option auto
    (long "cp-varweight"
     <> metavar "N"
     <> help "weight for variables (for critical pair scoring)"
     <> value 6
     <> showDefault)
  <*> option auto
    (long "cp-depthweight"
     <> metavar "N"
     <> help "weight for depth (for critical pair scoring); set larger to encourage axioms"
     <> value 16
     <> showDefault)

version :: String
version = "0.8 (dev)"

opts :: ParserInfo Opt
opts =
  info (helper <*> option_spec)
       (fullDesc <> 
        header ("Toma " ++ version))

main :: IO ()
main = do
  result <- execParser opts
  case (_order_constraint_file result, _tptp_file result, _inf_file result) of
    (Nothing, Just f, Nothing) -> handleTPTP f result
    (Just ari, Nothing, Nothing) -> handleARI ari result
    (Nothing, Nothing, Just inf) -> handleINF inf result
    _ -> error "specify only one TPTP or ARI file"

handleARI :: FilePath -> Opt -> IO ()
handleARI path opt = do
  (_, rules) <- ARI.readTRS path
  let ts = [ t | (l, r) <- rules, t <- [l, r] ]
  let sig = P.signatureOf' ts
  let var_map = M.fromList (zip (S.toList (S.unions [ P.variables t | t <- ts ])) [0..])
  let fun_map = M.fromList [ (f, i) | (i, (f, _)) <- V.toList (V.indexed sig) ]
  let convertTerm = P.convertTerm fun_map var_map 
  let rules' = [ (convertTerm l, convertTerm r) | (l, r) <- rules ]
  result <- RO.orientAll (RO.toClasses (_order_class opt)) sig rules'
  case result of
    Just o ->
      case filter (\(l, r) -> not (RO.gt o l r)) rules' of
        [] -> do
          putStrLn "YES"
          TIO.putStrLn (RO.pp sig o)
        (l, r) : _ -> do
          let varnaming = Term.nice_varnames [l, r]
          TIO.putStrLn (Term.pp sig varnaming l <> " > " <> Term.pp sig varnaming r <> " is not satisfied by the found order")
          TIO.putStrLn (RO.pp sig o)
          error "failed to orient all rules with the found order"
    Nothing -> putStrLn "MAYBE"

printLnUnlessQuiet :: Opt -> Text.Text -> IO ()
printLnUnlessQuiet opt txt =
  if Main._quiet opt then return () else TIO.putStrLn txt

selectOrder :: Opt -> Signature -> (Term.Term, Term.Term) -> [(Term.Term, Term.Term)] -> [(Term.Term, Term.Term)] -> IO RO.ReductionOrder
selectOrder opt sig goal axioms aux = do
  start_order_selection <- getCurrentTime
  o <- select
  end_order_selection <- getCurrentTime
  printLnUnlessQuiet opt (elapsed start_order_selection end_order_selection "order selection")
  printLnUnlessQuiet opt ""
  printLnUnlessQuiet opt "found order:"
  printLnUnlessQuiet opt (RO.pp sig o)
  printLnUnlessQuiet opt ""
  return o
  where
    handle mo = case mo of Just o ->  return o; _ -> error ("failed to find an order satisfying constraints")
    select = case _order_selection opt of
      "default" ->
        return (RO.defaultOrder (RO.toClasses (_order_class opt)) sig [ t | (l, r) <- goal : axioms, t <- [l, r] ] )
      "freqasc" ->
        return (RO.frequencyAsc (RO.toClasses (_order_class opt)) sig [ t | (l, r) <- goal : axioms, t <- [l, r] ] )
      "freqdesc" ->
        return (RO.frequencyDesc (RO.toClasses (_order_class opt)) sig [ t | (l, r) <- goal : axioms, t <- [l, r] ] )
      "mincp" -> do
        mo <- RO.minimizeCP (RO.toClasses (_order_class opt)) sig axioms aux
        handle mo
      "maxorient" -> do
        mo <- RO.maxOrient (RO.toClasses (_order_class opt)) sig (aux ++ axioms)
        handle mo
      "orientall" -> do
        mo <- RO.orientAll (RO.toClasses (_order_class opt)) sig (aux ++ axioms)
        handle mo
      _ -> error ("order selection " ++ _order_selection opt ++ " is not supported")

config :: Opt -> Discount.Config
config opt = Config {
  _cp_config = cpconf,
  Discount._cp_verbose = Main._cp_verbose opt,
  Discount._simplify_per = Main._simplify_per opt,
  Discount._quiet = Main._quiet opt,
  Discount._profile_per = Main._profile_per opt,
  Discount._fp = Indexing.parse (Main._fp opt)
}
  where
    cpconf = CPConfig {
      cfg_bigweight = _cp_bigweight opt,
      cfg_smallweight = _cp_smallweight opt,
      cfg_funweight = _cp_funweight opt,
      cfg_varweight = _cp_varweight opt,
      cfg_depthweight = _cp_depthweight opt
    }

handleINF :: FilePath -> Opt -> IO ()
handleINF path opt = do
  (_, crules, qs) <- ARI.readINF path
  let (rules, (ql, qr)) = INF.transform crules qs
  let ts = ql : qr : [ t | (l, r) <- rules, t <- [l, r] ]
  let sig = P.signatureOf' ts
  let var_map = M.fromList (zip (S.toList (S.unions [ P.variables t | t <- ts ])) [0..])
  let fun_map = M.fromList [ (f, i) | (i, (f, _)) <- V.toList (V.indexed sig) ] 
  let convertTerm = P.convertTerm fun_map var_map
  let axioms = [ ((convertTerm l, convertTerm r), Nothing) | (l, r) <- rules ]
  let goal = ((convertTerm ql, convertTerm qr), Nothing)
  o <- selectOrder opt sig (fst goal) (map fst axioms) []
  res <- discount sig o (config opt) axioms goal Nothing
  -- TODO: implement certificate generation
  case res of
    TSTP.CounterSatisfiable trs -> do
      TIO.putStrLn "YES"
      TIO.putStrLn (Text.unlines (map (Rule.pp sig) trs))
    TSTP.Theorem trs ((lg, rg), _) _ _ -> do
      TIO.putStrLn "MAYBE"
      TIO.putStrLn ("following TRS proves the goal " <> Term.pp sig undefined lg <> " = " <> Term.pp sig undefined rg) -- goal is ground
      TIO.putStrLn (Text.unlines (map (Rule.pp sig) trs))
    TSTP.GiveUp oriented unoriented -> do
      TIO.putStrLn "MAYBE"
      TIO.putStrLn "exhausted all critical pairs"
      TIO.putStrLn "oriented:"
      TIO.putStrLn (Text.unlines (map (Rule.pp sig) oriented))
      TIO.putStrLn "unoriented:"
      TIO.putStrLn (Text.unlines (map (Rule.pp sig) unoriented))
  
handleTPTP :: FilePath -> Opt -> IO ()
handleTPTP fpath opt = do
  ds <- includeDirectories
  formulas <- TPTP.readTPTP ds fpath
  case TPTP.preprocess formulas of
    Nothing -> do
      putStrLn "% SZS status Satisfiable"
      putStrLn "Consider the singleton model."
    Just (_, axioms, goal@((gl, gr), _), encoding_info) -> do
      printLnUnlessQuiet opt (TPTP.tshowProblem axioms goal)
      printLnUnlessQuiet opt ""
      let ts = gl : gr : [ t | ((l, r), _) <- axioms, t <- [l, r] ]
      let sig = P.signatureOf' ts
      let var_map = M.fromList (zip (S.toList (S.unions [ P.variables t | t <- ts ])) [0..])
      let fun_map = M.fromList [ (f, i) | (i, (f, _)) <- V.toList (V.indexed sig) ] 
      let convertTerm = P.convertTerm fun_map var_map 
      let axioms' = [ ((convertTerm l, convertTerm r), m) | ((l, r), m) <- axioms ]
      let goal' = ((convertTerm gl, convertTerm gr), snd goal)
      -- auxilliary constraints (e.g., force eq(X, X) > true & eq(s, t) > false & true > false)
      let aux = case encoding_info of
                  Just inf ->
                    let var = fst (head (M.toList var_map))
                        ((original_left, original_right), _) = TPTP._original_goal inf
                        t = convertTerm (P.F (TPTP._true inf) [])
                        f = convertTerm (P.F (TPTP._false inf) [])
                        aux1 = (convertTerm (P.F (TPTP._eq inf) [P.V var, P.V var]), t)
                        aux2 = (convertTerm (P.F (TPTP._eq inf) [original_left, original_right]), f)
                      in [ aux1, aux2, (t, f) ]
                  Nothing -> [ ]
      o <- selectOrder opt sig (fst goal') (map fst axioms') aux
      res <- discount sig o (config opt) axioms' goal' encoding_info
      TIO.putStrLn (TSTP.pp (V.map (\(f, ar) -> (TPTP.quote f, ar)) sig) res)
  where
    includeDirectories = do
      env <- getEnvironment
      case L.lookup "TPTP" env of
        Nothing  -> return ["."]
        Just dir -> return [".", dir]