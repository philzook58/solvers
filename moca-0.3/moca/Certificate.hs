module Certificate where

import Prelude hiding (product, sum)
import Terms
import Text.XML.Light
import Rules
import Horn
import INF hiding (term, rule, conditions, condition)
import Approximation

funapp :: String -> [Content] -> Content
funapp nam content = Elem $ unode "funapp" (Elem (unode "name" nam) : content)

var :: String -> Content
var x = Elem (unode "var" x)

rule :: Content -> Content -> Element
rule s t = unode "rule" [s, t]

term :: Term -> Content
term (V x) = var x
term (F f ts) = funapp f (map term ts)

-- TODO: abolish term without ' ???
term' :: Term -> Element
term' (V x) = unode "var" x
term' (F f ts) = unode "funapp" (Elem (name f) : (map (Elem . term') ts))

-- should be [(Term, Term)] -> ... or something?
rules :: [(Content, Content)] -> Element
rules trs = unode "rules" [ rule l r | (l, r) <- trs ]


condition :: (Term, Term) -> Element
condition (s, t) = unode "condition" [ term' s, term' t ] 

conditions :: [(Term, Term)] -> Element
conditions cs = unode "conditions" [ condition c | c <- cs ]

-- for inlining
inlinedConditions :: [(Term, Term)] -> Element
inlinedConditions cs = unode "inlinedConditions" [ condition c | c <- cs ]

crule :: CEquation -> Element
crule (cs, (l, r)) =
  unode "rule" [ term' l, term' r, conditions cs ]

crules :: CES -> Element
crules ces = unode "rules" [ crule c | c <- ces ]

trs :: TRS -> Element
trs x = unode "trs" (rules [ (term l, term r) | (l, r) <- x ])

-- NOTE: type is a keyword...
typ :: Element
typ = unode "type" (unode "polynomial" [unode "domain" (unode "naturals" ()), unode "degree" "1"])

variable :: Int -> Element
variable x = unode "variable" (show x)

integer :: Int -> Element
integer c = unode "integer" (show c)

-- proper naming?
-- c x
-- where c is a coefficient and x is a variable
monomial:: Int -> Int -> Element
monomial c x = unode "product" [integer c, variable x]

name :: String -> Element
name f = unode "name" f

unsharp :: String -> String
unsharp "" = error "empty string cannnot be unsharped!"
unsharp [c] = if c == '#' then "" else error "cannnot unsharp a string without # at the end"
unsharp (c : s@(_ : _)) = c : unsharp s

sharped_name :: String -> Content
sharped_name f = Elem (unode "sharp" (unode "name" (unsharp f)))

-- FIXME: hacky implementation, would not work this function symbols ending with #
fname :: String -> TRS -> Content
fname f trs 
  | elem f (map fst (signatureOf trs)) = Elem (name f)
  | otherwise = sharped_name f -- drop sharp symbol

-- FIXME: hacky implementation, would not work this function symbols ending with #
arity :: String -> TRS -> Content
arity f trs
  | elem f (map fst (signatureOf trs)) = Elem (unode "arity" (show (Terms.arity f trs)))
  | otherwise = Elem (unode "arity" (show (Terms.arity (unsharp f) trs))) -- drop sharp symbol

interpret :: [Content] -> Element
interpret es = Element (unqual "interpret") [] es Nothing

linear_expression :: (Int, [Int]) -> Content
linear_expression (c, []) = Elem (integer c)
linear_expression (c, cs) =
  Elem (unode "sum" (integer c : [ monomial ci xi | (ci, xi) <- zip cs [1..]  ]))

linear_interpretation :: TRS -> [(String, (Int, [Int]))] -> Element
linear_interpretation trs alg =
  unode "interpretation" (typ : interps)
  where
    interps = [ interpret [ fname f trs, Certificate.arity f trs, linear_expression (c0, cs) ] | (f, (c0, cs)) <- alg ]

maxplus_expression :: (Int, [(Int, Int)]) -> Content
maxplus_expression (c0, cds) = Elem (unode "maxExt" (unode "min" (show c0) : [ entry i c d | (i, (c, d)) <- zip [1..] cds ]))
  where
    entry i c d = unode "maxExtEntry" [ unode "intercept" (show c), unode "slope" (show d), variable i ]

maxplus_interpretation :: TRS -> [(String, (Int, [(Int, Int)]))] -> Element
maxplus_interpretation trs alg =
  unode "maxMonus"  [ interpret [ fname f trs, Certificate.arity f trs, maxplus_expression (c0, cds) ]
                    | (f, (c0, cds)) <- alg ]

-- interpretation :: TRS -> Algebra -> Element
-- interpretation trs (LinearAlgebra a) = linear_interpretation trs a
-- interpretation trs (MaxPlusAlgebra a) = maxplus_interpretation trs a

precedence :: Int -> Content
precedence n = Elem (unode "precedence" (show n))

statusPrecedence :: TRS -> Precedence -> Element
statusPrecedence trs prec =
  unode "statusPrecedence" (do {
    (n, f) <-  zip [0..] (reverse prec);
    return (unode "statusPrecedenceEntry" [
      Elem (name f),
      Certificate.arity f trs,
      Certificate.precedence n,
      Elem (unode "lex" ())
    ])})

termination_proof :: OTRS -> Content
termination_proof ([], trs, prec) = Elem (unode "trsTerminationProof" ruleRemoval)
  where
    ruleRemoval =  Element (unqual "ruleRemoval") []
      [
        Elem (unode "recursivePathOrder" [ statusPrecedence trs prec ]),
        Elem (unode "trs" (rules [ (term l, term r) | (l, r) <- trs ])),
        Elem (unode "trsTerminationProof" (unode "rIsEmpty" ()))
      ]
      Nothing
termination_proof _ = error "non-orientable equations are found" 

normalUnravelingEntry :: SplitIfEntry -> Content
normalUnravelingEntry (rule', f, ts) = 
  Elem (unode "normalUnravelingEntry" (Elem (crule rule') : Elem (name f) : [ term t | t <- ts ]))

splitIfInformation :: SplitIfInfo -> Content
splitIfInformation info =
  Elem (unode "splitIfInformation" (term trueTerm : term falseTerm : [ normalUnravelingEntry e | e <- info ] ))

wcrProof :: Content
wcrProof = Elem (unode "wcrProof" (unode "joinAutoNF" ()))

approxCompletionProof :: OTRS -> Content
approxCompletionProof otrs = Elem (unode "approxCompletionProof" [ wcrProof, termination_proof otrs ])

approxAndCompletionAndNormalization :: OTRS -> Content
approxAndCompletionAndNormalization otrs@(_, r, _) =
  Elem (unode "approxAndCompletionAndNormalization" [ Elem (trs r), approxCompletionProof otrs ]) -- FIXME: implement trs otrs

nonreachabilityProof :: OTRS -> Content
nonreachabilityProof otrs =
  Elem (unode "nonreachabilityProof" (unode "nonreachableEquationalDisproof" (unode "equationalDisproof" (approxAndCompletionAndNormalization otrs))))


inlinedRule :: (CEquation, [(Term, Term)]) -> Element
inlinedRule (rule, cs) =
  unode "inlinedRule" [ crule rule, inlinedConditions cs ]

inlinedRules :: [(CEquation, [(Term, Term)])] -> Element
inlinedRules es = unode "inlinedRules" (map inlinedRule es)

infeasibilityProof :: OTRS -> CertInfo -> Content
infeasibilityProof otrs (sinfo, rinfo@(ctrs, inline_info)) = 
  Elem (unode "proof" (unode "infeasibilityProof" lifting))
  where
    lifting = unode "infeasibleGoalLifting" [ Elem (name trueSymbol), Elem (name falseSymbol), Elem r]
    -- HACK: Certification fails if this unneccesary equation is included.
    -- introduced by liftHornClause, but just deleting it does not work...
    strangeCeq = ([(trueTerm, falseTerm)], (falseTerm, trueTerm))
    ctrs' = filter (/= strangeCeq)  ctrs
    r = unode "infeasibilityProof" (unode "rightInlineConditions" [ crules ctrs',  inlinedRules inline_info, s])
    s = unode "infeasibilityProof" (unode "infeasibleSplitIf" [ splitIfInformation sinfo, nonreachabilityProof otrs ])


conditionType :: INFProblem -> Content
conditionType (Oriented _) =
  Elem (unode "conditionType" (unode "oriented" ()))
-- join and semi-equational are not supported by CeTA, actually
conditionType (Join _) =
  Elem (unode "conditionType" (unode "join" ()))
conditionType (SemiEquational _) =
  Elem (unode "conditionType" (unode "semiEquational" ()))

infeasibilityQuery :: ES -> Content
infeasibilityQuery qs = Elem (unode "infeasibilityQuery" [ rule (term l) (term r) | (l, r) <- qs ])

infeasibilityInput :: INFProblem -> Content
infeasibilityInput p@(Oriented (ces, q)) =
  Elem (unode "infeasibilityInput" [ Elem (unode "ctrs" [ conditionType p, Elem (crules ces) ]), infeasibilityQuery q ])
infeasibilityInput _ = error "CeTA does not support join or semi-equational CTRSs"

arityINF' :: String -> (CES, ES) -> Int
arityINF' f (ces, es) = Terms.arity f (concat (map fst ces) ++ map snd ces ++ es)

arityINF :: String -> INFProblem -> Int
arityINF f (Oriented x) = arityINF' f x
arityINF f (SemiEquational x) = arityINF' f x
arityINF f (Join x) = arityINF' f x

metaInfo :: Content
metaInfo =
  Elem (unode "metaInformation" (unode "toolInfos" (unode "toolInfo" "Moca")))

certificate :: INFProblem -> OTRS -> CertInfo -> [Projection] -> String
certificate infp (es,trs,prec) cinfo proj =
  showTopElement (Element
    (unqual "certificationProblem")
    [ Attr (unqual "xmlns:xsi") "http://www.w3.org/2001/XMLSchema-instance",
      Attr (QName "noNamespaceSchemaLocation" Nothing (Just "xsi")) "cpf3.xsd"
    ]
    [ Elem (unode "cpfVersion" "3.0"),
      Elem (unode "lookupTables" ()),
      Elem (unode "input" (infeasibilityInput infp)),
      Elem (unode "property" (unode "infeasibility" ())),
      Elem (unode "answer" (unode "yes" ())),
      infeasibilityProof (es, trs', prec) cinfo
    ]
    Nothing)
  where
    trs' = trs ++ [ (F f [ V ("x" ++ show k) | k <- [0..(n-1)]] , V ("x" ++ show i)) | (f, i) <- proj, let n = arityINF f infp ]
