(* File: flags.ml *)
(* Author: Chad E Brown *)
(* Created: September 2010 *)

exception NotFlag of string

let   bool_flags : (string,  bool ref) Hashtbl.t = Hashtbl.create 20
let    int_flags : (string,   int ref) Hashtbl.t = Hashtbl.create 50
let  float_flags : (string, float ref) Hashtbl.t = Hashtbl.create 20

let hashtbl_set tbl k v =
  try (Hashtbl.find tbl k) := v
  with Not_found -> raise (NotFlag k)

let get_bool_flag k = !(Hashtbl.find bool_flags k)
let set_bool_flag = hashtbl_set bool_flags

let get_int_flag k = !(Hashtbl.find int_flags k)
let set_int_flag = hashtbl_set int_flags

let get_float_flag k = !(Hashtbl.find float_flags k)
let set_float_flag = hashtbl_set float_flags

let set_flag flagname l =
  try set_bool_flag flagname (bool_of_string l)
  with _ -> try set_float_flag flagname (float_of_string l)
  with _ -> set_int_flag flagname (int_of_string l)

let print_flags () =
  Hashtbl.iter (fun x y -> Printf.printf "%s: %B\n" x !y) bool_flags;
  Hashtbl.iter (fun x y -> Printf.printf "%s: %d\n" x !y) int_flags;
  Hashtbl.iter (fun x y -> Printf.printf "%s: %f\n" x !y) float_flags

let add_bool_flag n v = let r = ref v in Hashtbl.add bool_flags n r; r;;
let add_int_flag n v = let r = ref v in Hashtbl.add int_flags n r; r;;
let add_float_flag n v = let r = ref v in Hashtbl.add float_flags n r; r;;

let init_flags () = ();;

(*** The following flags control search. ***)
add_bool_flag "ENABLE_PATTERN_CLAUSES" false;;
add_bool_flag "PATTERN_CLAUSES_EARLY" false;; (*** Dec 2012 - If true, make a pattern clause for the formula when it's assigned a literal instead of when it's processed. ***)
add_bool_flag "APPLY_PATTERN_CLAUSES_EARLY" false;; (*** Nov 2015 - Resolve the pattern clause with other pattern clauses when it is created instead of when the corresponding proposition is processed. ***)
add_bool_flag "DYNAMIC_PATTERN_CLAUSES" true;; (*** Create pattern clauses from universally quantified formulas during search. - Chad, April 6, 2011 ***)
add_bool_flag "PATTERN_CLAUSES_TRANSITIVITY_EQ" false;; (*** Make pattern clauses for transitivity of equality. ***)
add_bool_flag "PATTERN_CLAUSES_FORALL_AS_LIT" true;;
add_int_flag "PATTERN_CLAUSES_DELAY" 1;;
add_int_flag "PATTERN_CLAUSES_EQN_DELAY" 1;;
add_bool_flag "PATTERN_CLAUSES_ONLYALLSTRICT" false;; (*** If true, only apply pattern clauses with a lit that contains all strict variables.  This is the first half of simulating pattern rules from Satallax 1.* ***)
add_bool_flag "PATTERN_CLAUSES_EQNLITS" false;; (*** If true, do rewriting with eqn lits in pattern clauses.  This is the other half of simulating pattern rules from Satallax 1.* ***)
add_bool_flag "SPLIT_GLOBAL_DISJUNCTIONS" false;;
add_bool_flag "FILTER_UNIV_USABLE" false;;
add_bool_flag "FILTER_UNIV" false;;
add_bool_flag "FILTER_POSATM_USABLE" false;;
add_bool_flag "FILTER_POSATM" false;;
add_bool_flag "FILTER_NEGATM_USABLE" false;;
add_bool_flag "FILTER_NEGATM" false;;
add_bool_flag "FILTER_POSEQ_USABLE" false;;
add_bool_flag "FILTER_POSEQ" false;;
add_bool_flag "FILTER_NEGEQ_USABLE" false;;
add_bool_flag "FILTER_NEGEQ" false;;
add_int_flag "FILTER_START" 5;;
let fiFILTER_INCR = add_int_flag "FILTER_INCR" 5;;
add_bool_flag "SYM_EQ" true;;
add_bool_flag "INSTANTIATE_WITH_FUNC_DISEQN_SIDES" true;;
add_bool_flag "IMITATE_DEFNS" true;;
add_int_flag "EXISTS_DELAY" 1;;
add_int_flag "FORALL_DELAY" 1;;
add_int_flag "DEFAULTELT_DELAY" 30;;
add_int_flag "DEFAULTELTINST_DELAY" 30;;
let fiCONFR_DIFF_DELAY = add_int_flag "CONFR_DIFF_DELAY" 100;;
let fiCONFR_SAME1_DELAY = add_int_flag "CONFR_SAME1_DELAY" 5;;
let fiCONFR_SAME2_DELAY = add_int_flag "CONFR_SAME2_DELAY" 0;;
add_int_flag "ENUM_START" 20;;
let fiENUM_ARROW = add_int_flag "ENUM_ARROW" 10;;
add_int_flag "ENUM_O" 5;;
add_int_flag "ENUM_SORT" 2;;
let fiENUM_NEG = add_int_flag "ENUM_NEG" 5;;
let fiENUM_IMP = add_int_flag "ENUM_IMP" 20;;
let fiENUM_FALSE = add_int_flag "ENUM_FALSE" 20;;
let fiENUM_CHOICE = add_int_flag "ENUM_CHOICE" 0;;
let fiENUM_FORALL = add_int_flag "ENUM_FORALL" 50;; (*** New in Satallax 2.0 ***)
let fiENUM_EQ = add_int_flag "ENUM_EQ" 5;;
add_bool_flag "ENUM_ITER_DEEP" false;;
let fiENUM_ITER_DEEP_DELAY = add_int_flag "ENUM_ITER_DEEP_DELAY" 100;;
add_int_flag "ENUM_ITER_DEEP_INIT" 1;;
let fiENUM_ITER_DEEP_INCR = add_int_flag "ENUM_ITER_DEEP_INCR" 0;;
add_bool_flag "LEIBEQ_TO_PRIMEQ" false;;
add_bool_flag "CHOICE_AS_DEFAULT" false;;
add_int_flag "IMITATE_DEFN_DELAY" 0;;
add_int_flag "IMITATE_DELAY" 10;;
let fiPROJECT_DELAY = add_int_flag "PROJECT_DELAY" 10;;
add_int_flag "NEW_HEAD_ENUM_DELAY" 10;;
add_int_flag "CHOICE_EMPTY_DELAY" 0;;
add_int_flag "CHOICE_IN_DELAY" 0;;
add_int_flag "POST_OR_L_DELAY" 0;;
add_int_flag "POST_OR_R_DELAY" 0;;
add_int_flag "POST_NOR_L_DELAY" 0;;
add_int_flag "POST_NOR_R_DELAY" 0;;
add_int_flag "POST_EQO_L_DELAY" 0;;
add_int_flag "POST_EQO_R_DELAY" 0;;
add_int_flag "POST_EQO_NL_DELAY" 0;;
add_int_flag "POST_EQO_NR_DELAY" 0;;
add_int_flag "POST_NEQO_L_DELAY" 0;;
add_int_flag "POST_NEQO_R_DELAY" 0;;
add_int_flag "POST_NEQO_NL_DELAY" 0;;
add_int_flag "POST_NEQO_NR_DELAY" 0;;
add_int_flag "POST_DEC_DELAY" 0;;
add_int_flag "PRE_MATING_DELAY_POS" 0;;  (*** New in Satallax 2.0 ***)
add_int_flag "PRE_MATING_DELAY_NEG" 0;;  (*** New in Satallax 2.0 ***)
add_int_flag "PRE_CHOICE_MATING_DELAY_POS" 0;;  (*** New in Satallax 2.0 ***)
add_int_flag "PRE_CHOICE_MATING_DELAY_NEG" 0;;  (*** New in Satallax 2.0 ***)
add_int_flag "POST_MATING_DELAY" 0;;
add_int_flag "POST_FEQ_DELAY" 0;;
add_int_flag "POST_NFEQ_DELAY" 0;;
let fiPOST_CONFRONT1_DELAY = add_int_flag "POST_CONFRONT1_DELAY" 0;;
let fiPOST_CONFRONT2_DELAY = add_int_flag "POST_CONFRONT2_DELAY" 0;;
let fiPOST_CONFRONT3_DELAY = add_int_flag "POST_CONFRONT3_DELAY" 0;;
let fiPOST_CONFRONT4_DELAY = add_int_flag "POST_CONFRONT4_DELAY" 0;;
add_bool_flag "INITIAL_SUBTERMS_AS_INSTANTIATIONS" false;;
let fiPRIORITY_QUEUE_IMPL = add_int_flag "PRIORITY_QUEUE_IMPL" 0;; (*** Which version of priority queue implementation to use ***)
add_bool_flag "PREPROCESS_BEFORE_SPLIT" false;;
add_bool_flag "TREAT_CONJECTURE_AS_SPECIAL" false;;
add_int_flag "AXIOM_DELAY" 0;; (*** Set this to > 0 to work on the negated conjecture first ***)
add_int_flag "RELEVANCE_DELAY" 0;; (*** Set this to > 0 to delay axioms that do not share names with the negated conjecture. Only has an effect if TREAT_CONJECTURE_SPECIAL is true ***)
add_bool_flag "ALL_DEFS_AS_EQNS" false;;

add_bool_flag "EAGERLY_PROCESS_INSTANTIATIONS" true;;
add_int_flag "INSTANTIATION_DELAY" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
let fiARTP_WEIGHT = add_int_flag "ARTP_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
let fiBASETP_WEIGHT = add_int_flag "BASETP_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
let fiOTP_WEIGHT = add_int_flag "OTP_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "AP_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "LAM_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "LAM_TP_WEIGHT_FAC" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "NAME_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "NAME_TP_WEIGHT_FAC" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "DB_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "DB_TP_WEIGHT_FAC" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "FALSE_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "IMP_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "FORALL_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "FORALL_TP_WEIGHT_FAC" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "EQ_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "EQ_TP_WEIGHT_FAC" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "CHOICE_WEIGHT" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)
add_int_flag "CHOICE_TP_WEIGHT_FAC" 1;; (*** If EAGERLY_PROCESS_INSTANTIATIONS is false ***)

add_int_flag "NOT_IN_PROP_MODEL_DELAY" 0;; (*** Nov 2011: Use propositional approximation to focus work on those true in the current propositional model. Koen Claessen suggested this at CADE 23. ***)
add_bool_flag "HOUNIF1" false;; (*** Mar 2012 - use HO unification to suggest instantiations during search ***)
add_bool_flag "HOUNIF1MATE" false;;
add_bool_flag "HOUNIF1MATEBELOWEQUIV" true;;
add_int_flag "HOUNIF1MAXMATES" 1;;
add_int_flag "HOUNIF1BOUND" 4;;
add_int_flag "HOUNIF1PROJECT" 1;;
add_int_flag "HOUNIF1IMITATE" 1;;
add_bool_flag "HOUNIF1MATENONLITS" false;; (*** Nov 2015 - When using HO Unif to suggest instantiations, try to mate on nonliterals. ***)
add_bool_flag "HOUNIF1NEGFLEX" false;; (*** Nov 2015 - simplify dpairs like ~P... =? s where s is not a negation to be P... =? ~s;; building double negation reduction into unification ***)
add_bool_flag "EXISTSTOCHOICE" false;; (*** Mar 2012 - Get rid of existentials during preprocessing ***)

(*** The following flags should only be changed when trying to disprove ***)
add_bool_flag "BASETYPESTOPROP" false;; (*** when true, change all base types to be o -- equivalent to making them all a type with 2 elts. ***)
add_bool_flag "BASETYPESFINITE" false;; (*** when true (and BASETYPESTOPROP false), assume all base types are finite of size <= BASETYPEMAXSIZE and do it. ***)
add_int_flag "BASETYPESMAXSIZE" 3;; (*** Assume all base types have size <= this number ***)

(*** The following flags control translation to proof terms. ***)
add_bool_flag "PFTRM_ADD_SYM_CLAUSES" true;;
add_bool_flag "PFTRM_PRESORT_CLAUSES" true;;
add_bool_flag "PFTRM_REMOVE_INDEPENDENT" true;;

(*** The flag MINISAT_SEARCH_PERIOD controls how often MiniSat asked to search for unsatisfiability.
     Default of 1 means every time a new clause is given to MiniSat. ***)
add_int_flag "MINISAT_SEARCH_PERIOD" 1;;

(*** Send first-order formulas to E with timeout of E_TIMEOUT seconds every E_PERIOD times a first-order formula is encountered. ***)
add_bool_flag "USE_E" false;;
    (*
add_bool_flag "USE_EHOH" false;;
    *)
add_int_flag "E_PERIOD" 100;;
add_int_flag "E_TIMEOUT" 1;;
add_bool_flag "E_EQO_EQUIV" false;;
add_bool_flag "E_AUTOSCHEDULE" false;;

(*** Feb 18 2013
 - INSTANTIATION_ORDER_CYCLE - how long to cycle a stack/queue switching pattern.
 - INSTANTIATION_ORDER_MASK - integer describing the stack/queue switching pattern. ***)
add_int_flag "INSTANTIATION_ORDER_CYCLE" 1;;
add_int_flag "INSTANTIATION_ORDER_MASK" 0;;

(*** Nov 13 2015 DELAY_FO delay processing first-order formulas;; with the idea that E or pattern clauses can handle this part of the search. ***)
add_int_flag "DELAY_FO" 0;; (*** by default, no delay ***)
add_int_flag "DELAY_FO_CLAUSE" 0;; (*** by default, no delay ***)
add_int_flag "DELAY_FO_LIT" 0;; (*** by default, no delay ***)

    
    (*** Mar/Apr 2016 ***)
add_bool_flag "USE_MODELS" false;;
add_int_flag "MAX_INTERPS_PER_AXIOM" 3;; (*** for each axiom/negated conjecture, try to find MAX_INTERPS_PER_AXIOM interpretations of the constants in the frames with 1,2,4 base type elts making the axiom true;; these will be used to help guide the search if USE_MODELS is true ***)
add_int_flag "DELAY_SEMANTIC_EQUIV_INSTANTIATION" 0;; (*** by default, no delay, so don't bother evaluating in a model ***)
let fiDELAY_TRUE_IN_MODELS = add_int_flag "DELAY_TRUE_IN_MODELS" 0;; (*** delay processing a proposition based on how often it is true in a model, the idea being that those that are false are more likely to contribute to a refutation ***)
let fiDELAY_FALSE_IN_MODELS = add_int_flag "DELAY_FALSE_IN_MODELS" 0;; (*** delay processing a proposition based on how often it is false in a model ***)
let fiDELAY_UNINFORMATIVE_IN_MODELS = add_int_flag "DELAY_UNINFORMATIVE_IN_MODELS" 0;; (*** delay those that are true in all models or false in all models ***)
add_float_flag "MODEL_SEARCH_TIMEOUT" 1.;; (*** number of seconds to search for models before giving up, useful in case some axioms are easy to find models for but others aren't ***)

    (*** Dec 2016 ***)
add_bool_flag "ONTOLOGY_DEFS_TRANSLUCENT" false;;
let fiTRANSLUCENT_EXPAND_DELAY = add_int_flag "TRANSLUCENT_EXPAND_DELAY" 5;;

    (*** Jan 2017 ***)
add_bool_flag "NONFORALL_PATTERN_CLAUSES_USABLE" false;;

    (*** May 2019 ***)
add_bool_flag "USE_SINE" false;;
add_float_flag "SINE_TOLERANCE" 1.2;; (* must be >= 1.0 *)
add_int_flag "SINE_GENERALITY_THRESHOLD" 0;; (* must be >= 0 *)
add_float_flag "SINE_RANK_LIMIT" 3.;;
add_int_flag "SINE_DEPTH" 0;; (* if 0, then unlimited depth *)
