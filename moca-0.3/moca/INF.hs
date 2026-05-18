module INF where

import Rules
import Terms

type InputData = (String, [String], CES, [String], ES)

data INFProblem = SemiEquational (CES, ES) | Join (CES, ES) | Oriented (CES, ES)
-- the second argument of the tuple is CONDITION (existential closure of the conjunction of conditions)

-- TODO: broken?
instance Show INFProblem where
  show (SemiEquational (ces, es)) = showCES ces ++ "\n@" ++ showES es ++ "\n(<->^*)\n" 
  show (Join (ces, es)) = showCES ces ++ "\n@" ++ showES es  ++ "\n(->^* <-^*)\n"
  show (Oriented (ces, es)) = showCES ces ++ "\n@" ++ showES es ++ "\n(->^*)\n"

