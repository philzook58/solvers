module Main where

import System.Environment  
import System.Exit
import TRS
import Parser
import Order
import Completion (Env (..), complete)

version :: String
version = "1.6"

env0 :: Env
env0 = Env { 
  _kOrders    = 2,     {-  2 or  3 -}
  _nEquations = 21,    {- 13 or 10, respectively -}
  _tool       = "z3",
  _order      = ELPOEKBOClass
}

readSpecFile' :: String -> IO TRS
readSpecFile' file = do
  result <- readSpecFile file
  case result of
    Left e -> do
      print e
      exitWith (ExitFailure 1)
    Right trs -> return trs

proveTermination :: Order.Class -> String -> IO ()
proveTermination orderClass filename = do
  trs <- readSpecFile' filename
  result <- Order.terminating "z3" orderClass trs
  case result of
    Nothing -> do 
      putStrLn "MAYBE\n"
      putStrLn (showTRS trs)
    Just order -> do
      putStrLn "verifying"
      let b = all (\(l, r) -> Order.gt order l r) trs
      putStrLn (if b then "YES\n" else "ERROR\n")
      putStrLn "Consider the TRS:\n"
      putStrLn (showTRS trs)
      putStrLn ("Termination is shown by " ++ show order)
      if b then return () else error "bug"

showSpec :: TRS -> String
showSpec trs = show (Spec { _VAR = TRS.variables trs, _RULES = trs })

runCompletion :: Env -> String -> IO ()
runCompletion env filename = do
  es <- readSpecFile' filename
  result <- complete env es
  case result of
    Nothing -> do
      putStrLn "MAYBE"
    Just (trs, oi) -> do
      putStrLn "YES\n"
      putStrLn (showSpec trs)
      putStrLn "(COMMENT"
      putStr   ("Termination is shown by " ++ show oi)
      putStrLn ")"

usage :: String
usage = 
  unlines ["Maxcomp version " ++ version,
           "Usage: maxcomp [option] <file>",
           "Option:",
           "  -t <order>  proves termination by a specified order.",
           "  -c <order>  completes an input equation system.",
           "where <order> ::= lpo | kbo | elpo | ekbo | elpoekbo | gwpo",
           "'maxcomp <file>' is same as 'maxcomp -c elpoekbo <file>'."] 

invalidArgument :: String -> IO ()
invalidArgument s = do
  putStrLn ("Invalid argument: " ++ s)
  putStrLn "Try 'maxcomp -h' for more information."

parseOrder :: Env -> String -> IO Env
parseOrder env "lpo"      = return (env { _order = LPOClass })
parseOrder env "kbo"      = return (env { _order = KBOClass })
parseOrder env "elpo"     = return (env { _order = ELPOClass })
parseOrder env "ekbo"     = return (env { _order = EKBOClass })
parseOrder env "elpoekbo" = return (env { _order = ELPOEKBOClass })
parseOrder env "gwpo" = return (env { _order = SPOClass })
parseOrder _   s      = do
  invalidArgument s
  exitWith (ExitFailure 1)

data Mode = Termination | Completion

parseArgs :: Env -> Mode -> [String] -> IO ()
parseArgs _ _ []                = putStr usage
parseArgs _ _ ("-h" : _)        = putStr usage
parseArgs _ _ ("-help" : _)     = putStr usage
parseArgs env mode ("-k" : s : args) = do
  parseArgs (env { _kOrders = read s }) mode args
parseArgs env mode ("-n" : s : args) = do
  parseArgs (env { _nEquations = read s }) mode args
parseArgs env _ ("-t" : s : args) = do
  env' <- parseOrder env s
  parseArgs env' Termination args
parseArgs env _ ("-c" : s : args) = do
  env' <- parseOrder env s
  parseArgs env' Completion args
parseArgs env Completion [filename] =
  runCompletion env filename
parseArgs env Termination [filename] =
  proveTermination (_order env) filename
parseArgs _ _ args = invalidArgument (unwords args)


main :: IO ()
main = do
  args <- getArgs
  parseArgs env0 Completion args
