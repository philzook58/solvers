module Substitutions where

import Terms

type Subst = [(String, Term)]
  

-- do substitution (t sigma)
substitute :: Term -> Subst -> Term
substitute (F f ts) sgm                           = F f [ substitute t sgm | t <- ts ]
substitute (V x)    sgm | Just t <- lookup x sgm  = t
                        | otherwise               = V x

substituteEquation :: Equation -> Subst -> Equation
substituteEquation (s, t) sgm = (substitute s sgm, substitute t sgm)

substituteES :: ES -> Subst -> ES
substituteES ps sgm = [ substituteEquation p sgm | p <- ps ]



-- update substitution ({x |-> t}(sgm))
update :: String -> Term -> Subst -> Subst
update x t sgm = [ (x', substitute t' [(x, t)]) | (x', t') <- sgm' ]
  where sgm' | elem x [ y | (y, _) <- sgm ] = sgm
             | otherwise                    = (x, (V x)):sgm



renameEquation :: String -> Equation -> Equation
renameEquation x' e = substituteEquation e sgm
  where sgm = [ (x, V (x' ++ show i)) | (i, x) <- zip [0..] (varsInEquation e) ]

renameES :: String -> ES -> ES
renameES x es = [ renameEquation x e | e <- es ]



domain :: Subst -> [String]
domain sgm = [ x | (x, _) <- sgm ]
