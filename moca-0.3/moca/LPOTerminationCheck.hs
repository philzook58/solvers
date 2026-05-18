module LPOTerminationCheck where

import Terms
import Substitutions
import Rules
import Debug.Trace

-- check order for two function symbols
gt_func :: Precedence -> String -> String -> Bool
gt_func p f g = index f < index g
  where index h | j:_ <- [i | (i, sym) <- zip [0..] p, sym == h]  = j

-- s >_lpo t.
gt_lpo :: Precedence -> Term -> Term -> Bool
gt_lpo p s t = gt_lpo1 p s t || gt_lpo2 p s t

-- s >=_lpo t.
gtOrEq_lpo p s t = gt_lpo p s t || s == t

-- 1st condition of LPO
gt_lpo1 :: Precedence -> Term -> Term -> Bool
gt_lpo1 p s t@(V x) = occurs x s && s /= t
gt_lpo1 p s t       = False

-- 2nd condition of LPO
gt_lpo2 :: Precedence -> Term -> Term -> Bool
gt_lpo2 p s@(F f tsS) t@(F g tsT) = gl2a || gl2b || gl2c
  where gl2a = or [ gtOrEq_lpo p si t | si <- tsS ]
        gl2b = gt_func p f g && and [ gt_lpo p s ti | ti <- tsT ]
        gl2c = f == g        && and [ gt_lpo p s ti | ti <- tsT ]
                             && or [ take i tsS == take i tsT 
                                     && gt_lpo p (tsS !! i) (tsT !! i)
                                   | i <- [0..length tsS - 1] ]
gt_lpo2 p s t = False

-- l >_lpo r for all rules l -> r in the TRS
lpoTerminating :: Precedence -> TRS -> Bool
lpoTerminating p trs = and [ gt_lpo p rL rR | (rL, rR) <- trs ]

-- take the smallest constant in predcedence (we need the set of constants of precedence as an input)
minimumConstant :: Precedence -> [String] -> Maybe String
minimumConstant prec fs | cs /= []  = Just (last cs)
                        | otherwise = Nothing
  where cs =  [ f | f <- prec, f `elem` fs ]


-- extendedLPO
gt_exfunc :: [Precedence] -> String -> String -> Bool
gt_exfunc ps f g = or [ gt_func p f g | p <- ps, f `elem` p, g `elem` p ]
  
gt_exlpo :: [Precedence] -> Term -> Term -> Bool
gt_exlpo ps s t = gt_exlpo1 ps s t || gt_exlpo2 ps s t

gtOrEq_exlpo ps s t = gt_exlpo ps s t || s == t

gt_exlpo1 :: [Precedence] -> Term -> Term -> Bool
gt_exlpo1 ps s t@(V x) = occurs x s && s /= t
gt_exlpo1 ps s t       = False

gt_exlpo2 :: [Precedence] -> Term -> Term -> Bool
gt_exlpo2 ps s@(F f tsS) t@(F g tsT) = gl2a || gl2b || gl2c
  where gl2a = or [ gtOrEq_exlpo ps si t | si <- tsS ]
        gl2b = gt_exfunc ps f g 
               && and [ gt_exlpo ps s ti | ti <- tsT ]
        gl2c = f == g 
               && and [ gt_exlpo ps s ti | ti <- tsT ]
               && or [ take i tsS == take i tsT 
                       && gt_exlpo ps (tsS !! i) (tsT !! i)
                     | i <- [0..length tsS - 1] ]
gt_exlpo2 ps s t = False


orientable :: Precedence -> Equation -> Bool
orientable prec (s, t) = gt_lpo prec s t

unorientable :: Precedence -> Equation -> Bool
unorientable prec e = not (orientable prec e)


ex_orientable :: [Precedence] -> Equation -> Bool
ex_orientable precs (s, t) = gt_exlpo precs s t

ex_unorientable :: [Precedence] -> Equation -> Bool
ex_unorientable precs e = not (ex_orientable precs e)
