module Messages where

import Terms
import Rules
import TPTP
import Horn
import Certificate
import INF
import Text.ParserCombinators.Parsec
import Approximation

unknownMessage str = "moca: unknown option '" ++ str ++ "'.\n"

helpMessage = "Moca v0.3\n"++ 
            "Usage: ./moca <options> <file>\n\n" ++ 
              "\t--siav:\t\tuse the split-if encoding using all variables in s = t => u = v  \n" ++
              "\t--smsi:\t\tskip execution for parameters with the multi-split-if encoding mode\n" ++
              "\t-nap:\t\texecute without approximations by projection\n" ++
              "\t-nag:\t\texecute without approximations by generalization\n" ++
              "\t--cert:\t\tgenerate a certificate in CPF3 (cannot be combined with other options)\n" ++
              "\t-help:\t\tDisplay this list of options\n" ++
              "\t--help:\t\tDisplay this list of options\n" 

errorMessage_SpecifyFilename = "Please specify filename. For Instance \n  $ ./moca problem.trs"

errorMessage_NoZ3 = "Z3 cannot be found."

resultForINF_Infeasible :: [HornClause Atom] -> ES -> ES -> OTRS -> [Projection] -> String
resultForINF_Infeasible hc es gs otrs proj = "YES\n\n" ++ 
  "proof:\n" ++ 
  "The input problem is infeasible because\n\n" ++
  "[1] the following set of Horn clauses is satisfiable:\n\n"++
  showHornClause hc ++ "\n\n" ++
  "This holds because\n\n" ++
  "[2] the following E does not entail the following G (Claessen-Smallbone's transformation (2018)):\n\n" ++
  "E:\n" ++ showES es ++ "\nG:\n" ++ showES gs ++ "\n\n" ++
  "This holds because\n\n" ++
  "[3] the following ground-complete ordered TRS entails E but does not entail G:\n" ++
  showOTRS otrs ++ "\n" ++
  remarkForCollapsing proj

resultForINF_Infeasible_cert :: [HornClause Atom] -> ES -> ES -> OTRS -> [Projection] ->
  Maybe CertInfo -> Either ParseError INFProblem -> String
resultForINF_Infeasible_cert hc es gs otrs@([], _, _) proj (Just i) (Right p) =
  "YES\n" ++ certificate p otrs i proj
resultForINF_Infeasible_cert hc es gs otrs@(_ : _, _, _) proj (Just i) (Right p) =
  "MAYBE\nthe obtained ground-complete system contains an unorientable equation and currently such a system is not certifiable\n"
resultForINF_Infeasible_cert _ _ _ _ _ _ _ = error "CertInfo and INFProblem need be provided"

resultForINF_Maybe :: OTRS -> [Projection] -> String
resultForINF_Maybe otrs proj = "MAYBE\n" ++ remarkForCollapsing proj

resultForINF_EmptyInput :: String 
resultForINF_EmptyInput = "ERROR\nNo condition."



resultForTPTP_SAT :: [HornClause Atom] -> ES -> ES -> OTRS -> [Projection] -> String
resultForTPTP_SAT hc es gs otrs proj =
  "% SZS status Satisfiable\n" ++
  "% SZS output start Proof\n" ++
  "The input problem is satisfiable because\n\n" ++
  "[1] the following set of Horn clauses is satisfiable:\n\n"++
  showHornClause hc ++ "\n\n" ++
  "This holds because\n\n" ++
  "[2] the following E does not entail the following G (Claessen-Smallbone's transformation (2018)):\n\n" ++
  "E:\n" ++ showES es ++ "\nG:\n" ++ showES gs ++ "\n\n" ++
  "This holds because\n\n" ++
  "[3] the following ground-complete ordered TRS entails E but does not entail G:\n\n" ++
  showOTRS otrs ++ "\n" ++
  remarkForCollapsing proj ++ "\n" ++
  "% SZS output end Proof\n"

resultForTPTP_UNSAT :: [HornClause Atom] -> ES -> ES -> OTRS -> [Projection] -> String
resultForTPTP_UNSAT hc es gs otrs proj =
  "% SZS status Unsatisfiable\n" ++
  "% SZS output start Proof\n" ++
  "The input problem is unsatisfiable because\n\n" ++
  "[1] the following set of Horn clauses is unsatisfiable:\n\n"++
  showHornClause hc ++ "\n\n" ++
  "This holds because\n\n" ++
  "[2] the following E entails the following G (Claessen-Smallbone's transformation (2018)):\n\n" ++
  "E:\n" ++ showES es ++ "\nG:\n" ++ showES gs ++ "\n\n" ++
  "This holds because\n\n" ++
  "[3] E entails the following ordered TRS and the lhs and rhs of G join by the TRS:\n\n" ++
  showOTRS otrs ++ "\n" ++
  remarkForCollapsing proj ++ "\n" ++
  "% SZS output end Proof\n"

resultForTPTP_EmptyInput :: String 
resultForTPTP_EmptyInput = 
  "% SZS status Satisfiable\n" ++ 
  "% SZS output start Proof\n" ++
  "There is no formula in the input." ++
  "% SZS output end Proof\n"



  