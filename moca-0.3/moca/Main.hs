module Main where

import Data.List
import System.Process
import System.Environment
import System.Exit
import Text.ParserCombinators.Parsec

import Lists
import Rules
import TPTP
import Horn
import INF
import ARIParser
import WSTParser
import Parameters
import Messages
import Prover

readINFProblem :: String -> IO (Either ParseError INFProblem)
readINFProblem path = do
  r <- readWST path
  case r of
    Right _ -> return r
    Left _ -> readARI path

-- TODO: the way certification feature is added is hacky...
main = do 
    (files, lprms) <- readCommandArguments
    case (unknownMode lprms, helpMode lprms, files) of
      (Just md,     _,        _) -> putStrLn (unknownMessage md ++ helpMessage)
      (Nothing,  True,        _) -> putStrLn (helpMessage)
      (Nothing, False,       []) -> putStrLn errorMessage_SpecifyFilename
      (Nothing, False, file : _) -> do 
        exitStatus <- system "which z3 > /dev/null"
        if exitStatus /= ExitSuccess then putStrLn errorMessage_NoZ3
        else do
          (maybeWPs, problemType) <- readWordProblems lprms file
          maybeINFProblem <- readINFProblem file
          case maybeWPs of
            Just wps -> do
              if nullHornClause wps then putStrLn resultForTPTP_EmptyInput
              else do
                let wps' = [ if str == "cert"
                              then (str, ((removeTrivialEquations es, [g], i), hc)) -- NOTE: redundantEquationElimination is not supported by CeTA
                              else (str, ((redundantEquationElimination (removeTrivialEquations es), [g], i), hc))
                          | (str, ((es, g, i), hc)) <- wps ]  -- 3rd "hc" is used for displaying proof
                resultStr <- execution [] (cyclic lprms) problemType wps' (certMode lprms) maybeINFProblem
                putStrLn resultStr
  where nullHornClause wps = or [ null hc | (_, (_, hc)) <- wps]

readCommandArguments = do
  args <- getArgs
  let (mds, files) = partition ("-" `isPrefixOf`) args
  let lprms = [ (loop, addModes mds prm) | (loop, prm) <- defaultParameters ]
  return (files, lprms)

readWordProblems lprms file = do
  (maybeHCs, pt) <- readHornClauses file
  case maybeHCs of
    Nothing               -> return (Nothing, pt)
    Just (hc, hc_nocond)  -> return (Just [ ("", (splitIf lprms hc, hc)),
                                            ("nctp", (tupling lprms hc_nocond, hc_nocond)) , 
                                            ("nc", (splitIf lprms hc_nocond, hc_nocond)),
                                            ("tp", (tupling lprms hc, hc)),
                                            ("msi", (multiSplitIf lprms hc, hc)),
                                            -- TODO: completely ignoring conditions is sometimes useful (e.g., COPS #853 and #857)
                                            -- ("cert", (splitIf_cert lprms hc_nocond, hc_nocond))
                                            ("cert", (splitIf_cert lprms hc, hc))
                                          ],
                                     pt)

readHornClauses file = do
  maybeINFProblem <- readINFProblem file
  case maybeINFProblem of
    Right infp  -> return (Just (encodeINF infp, encodeINF_noCondition infp), "INF")
    Left error1 -> do
      dirs <- includeDirectoriesForTPTP
      maybeTPTP <- readTPTP dirs file
      case maybeTPTP of
        Left error2 -> do
          print error1
          print error2
          return (Nothing, "")
        Right tptp -> 
          case encodeTPTP tptp of 
            Just hornClauses -> return (Just (hornClauses, hornClauses), "TPTP")
            Nothing          -> return (Nothing, "TPTP")
      
includeDirectoriesForTPTP :: IO ([String])
includeDirectoriesForTPTP = do
  env <- getEnvironment
  let dirs | Just str <- lookup "TPTP" env = [".", str]
           | otherwise                     = ["."]
  return dirs
