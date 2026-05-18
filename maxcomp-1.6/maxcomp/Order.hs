module Order where

import Data.List
import Term
import Rule
import TRS
import SMT
import qualified LPO
import qualified KBO
import qualified ELPO
import qualified EKBO
import qualified ELPOEKBO
import qualified SPO
import EncodingLPOKBO
import EncodingELPOEKBO
import Precedence
import EncodingSPO

-- interface

data Class =
    LPOClass
  | KBOClass
  | ELPOClass
  | EKBOClass
  | ELPOEKBOClass
  | SPOClass

data Instance =
    LPOInstance      Precedence
  | KBOInstance      KBO.Parameter
  | ELPOInstance     ELPO.Parameter 
  | EKBOInstance     EKBO.Parameter
  | ELPOEKBOInstance ELPOEKBO.Parameter
  | SPOInstance      SPO.Parameter

instance Show Instance where
  show (LPOInstance parameter)      = LPO.showParameter parameter
  show (KBOInstance parameter)      = KBO.showParameter parameter
  show (ELPOInstance parameter)     = ELPO.showParameter parameter
  show (EKBOInstance parameter)     = EKBO.showParameter parameter
  show (ELPOEKBOInstance parameter) = show parameter
  show (SPOInstance parameter)      = SPO.showParameter parameter

data Encoding = Orientable | Reducible | CPReducible deriving Show

encode :: Class -> Signature -> TRS -> (Formula, [(Rule, Formula)])
encode LPOClass      sig trs = encodeLPO  sig trs
encode KBOClass      sig trs = encodeKBO  sig trs
encode ELPOClass     sig trs = encodeELPO sig trs
encode EKBOClass     sig trs = encodeEKBO sig trs
encode ELPOEKBOClass sig trs = encodeELPOEKBO sig trs
encode SPOClass      sig trs = encodeSPO  sig trs

decode :: Class -> Model -> Signature -> Instance
decode LPOClass      model sig = LPOInstance      (decodeLPO      model sig)
decode KBOClass      model sig = KBOInstance      (decodeKBO      model sig)
decode ELPOClass     model sig = ELPOInstance     (decodeELPO     model sig)
decode EKBOClass     model sig = EKBOInstance     (decodeEKBO     model sig)
decode ELPOEKBOClass model sig = ELPOEKBOInstance (decodeELPOEKBO model sig)
decode SPOClass      model sig = SPOInstance      (decodeSPO      model sig)

gt :: Instance -> Term -> Term -> Bool
gt (LPOInstance param)      s t = LPO.gtLPO   param s t
gt (KBOInstance param)      s t = KBO.gtKBO   param s t
gt (ELPOInstance param)     s t = ELPO.gt     param s t
gt (EKBOInstance param)     s t = EKBO.gtKBO  param s t
gt (ELPOEKBOInstance param) s t = ELPOEKBO.gt param s t
gt (SPOInstance param)      s t = SPO.gt param s t

-- Proving termination

terminating :: String -> Class -> TRS -> IO (Maybe Instance)
terminating tool order trs = do
  smtOutput <- sat tool (conj (hard : [ f | (_, f) <- a ]))
  case smtOutput of
    Nothing    -> return Nothing
    Just model -> return (Just (decode order model sig)) 
  where
    (hard, a) = encode order (TRS.signatureOf trs) trs
    sig = TRS.signatureOf trs

-- Find k maximal subsystems

rewriteRules :: TRS -> TRS
rewriteRules es =
  nubBy Rule.variant
    [ rule | (s, t) <- es, rule <- [(s, t), (t, s)], Rule.variableCondition rule ]

excludeTRSs :: [(Rule, Formula)] -> [TRS] -> Formula
excludeTRSs a trss =
  conj [ disj [ f | (rule, f) <- a, not (any (Rule.variant rule) trs) ]
       | trs <- trss ]

reducibleTerm :: [(Rule, Formula)] -> Term -> Formula
reducibleTerm a t =
  disj [ f | (rule, f) <- a, reducible [rule] t ]

reducibleEq :: [(Rule, Formula)] -> Rule -> Formula
reducibleEq a (s, t)
  | s == t    = top
  | otherwise = disj [ f | (rule, f) <- a, reducible [rule] s || reducible [rule] t ]

orientableEq :: [(Rule, Formula)] -> Rule -> Formula
orientableEq a (s, t) =
  disj [ f | (rule, f) <- a, rule == (s, t) || rule == (t, s) ]

redundant :: [(Rule, Formula)] -> Rule -> Formula
redundant a (s, t)
  | s == t    = top
  | otherwise = 
      conj [ neg f 
           | rule <- [(s,t),(t,s)], 
             Just f <- [lookup rule a] ] 

orientableRule :: Rule -> Bool
orientableRule rule@(_, r) =
  Rule.variableCondition rule &&
  not (reducible [rule] r)

orientableRules :: TRS -> TRS
orientableRules cs = [ rule | rule <- rewriteRules cs, orientableRule rule ]

constraints :: Class -> Signature -> TRS -> [TRS] -> ([(Rule,Formula)], Formula, [Formula])
constraints oc sig cs trss =
  (a, conj (orderConstraint : exclusion : reducibilities),
   [ redundant a e | e <- cs ])
  where
    (orderConstraint, a) = encode oc sig (orientableRules cs)
    exclusion = excludeTRSs a trss
    reducibilities = [ reducibleEq a e | e <- cs ]

showA :: (Model, [(Rule, Formula)]) -> String
showA (m, a) =
  unlines [ showRule rule ++ ": " ++ show f  ++ " = " ++ show (evalFormula m f)
          | (rule, f) <- a ]

newOrder :: String -> Class -> Signature -> TRS -> [TRS] -> IO (Maybe (TRS, Instance))
newOrder tool oc sig cs trss = do
  smtOutput <- maxsat tool hard softs
  case smtOutput of
    Nothing -> return Nothing
    Just model -> 
      case [ rule | (rule, f) <- a, evalFormula model f ] of
        []  -> return Nothing
        trs -> do
          let oi = decode oc model sig
          case [ (l, r) | (l, r) <- trs, not (Order.gt oi l r) ] of
            [] -> return (Just (trs, oi))
            rule : _ -> do
              putStrLn "ERROR"
              putStrLn ""
              putStrLn (showES cs)
              putStrLn (showA (model, a))
              putStrLn (show oi)
              putStrLn "The next rule is not oriented:\n"
              putStrLn ("  " ++ showRule rule)
              putStrLn "\n" 
              error "bug"
  where
    (a, hard, softs) = constraints oc sig cs trss

kOrders' :: String -> Class -> Int -> Signature -> TRS -> [(TRS, Instance)] -> IO [(TRS, Instance)]
kOrders' _    _  0 _   _  pairs = return pairs
kOrders' tool oc k sig cs pairs = do
  result <- newOrder tool oc sig cs [ trs | (trs, _) <- pairs ]
  case result of
    Nothing        -> return pairs
    Just (trs, oi) -> kOrders' tool oc (k - 1) sig cs (pairs ++ [(trs, oi)])

kOrders :: String -> Class -> Int -> TRS -> IO [(TRS, Instance)]
kOrders tool oc k cs =
  kOrders' tool oc k (TRS.signatureOf cs) cs []
