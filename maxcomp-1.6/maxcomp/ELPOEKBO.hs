module ELPOEKBO where

import Term
import qualified ELPO
import qualified EKBO

data Parameter = ELPO ELPO.Parameter | EKBO EKBO.Parameter

instance Show Parameter where
  show (ELPO param) = ELPO.showParameter param
  show (EKBO param) = EKBO.showParameter param

-- Comparison

gt :: Parameter -> Term -> Term -> Bool
gt (ELPO param) s t = ELPO.gt param s t
gt (EKBO param) s t = EKBO.gtEKBO param s t
