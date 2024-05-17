(* Lash *)
(* ported from Satallax file: *)
(* File: flags.mli *)
(* Author: Chad E Brown *)
(* Created: September 2010 *)
(* but Lash has major changes to make flag retrieval fast *)

exception NotFlag of string

val get_bool_flag : string -> bool
val set_bool_flag : string -> bool -> unit
val get_int_flag : string -> int
val set_int_flag : string -> int -> unit
val get_float_flag : string -> float
val set_float_flag : string -> float -> unit
val set_flag : string -> string -> unit
val print_flags : unit -> unit
val init_flags : unit -> unit

val fiSPLIT_GLOBAL_DISJUNCTIONS_LIMIT : int ref
val fbSPLIT_GLOBAL_DISJUNCTIONS_IMP : bool ref
val fbSPLIT_GLOBAL_DISJUNCTIONS_EQO : bool ref
val fiCONFR_SAME2_DELAY : int ref;;
val fiCONFR_SAME1_DELAY : int ref;;
val fiCONFR_DIFF_DELAY : int ref;;
val fiPOST_MATING_DELAY : int ref;;
val fiPOST_CONFRONT1_DELAY : int ref;;
val fiPOST_CONFRONT2_DELAY : int ref;;
val fiPOST_CONFRONT3_DELAY : int ref;;
val fiPOST_CONFRONT4_DELAY : int ref;;
val fbINITIAL_SUBTERMS_AS_INSTANTIATIONS : bool ref;;
val fbINITIAL_SUBTERMS_AS_INSTANTIATIONS_O : bool ref;;
val fiPRIORITY_QUEUE_IMPL : int ref;;
val fiMINISAT_SEARCH_PERIOD : int ref;;
val fiMINISAT_SEARCH_PERIOD_FACTOR : int ref;;
val fiMINISAT_SEARCH_DELAY : int ref;;
val fiDELAY_TRUE_IN_MODELS : int ref;;
val fiDELAY_FALSE_IN_MODELS : int ref;;
val fiDELAY_UNINFORMATIVE_IN_MODELS : int ref;;

val fiARTP_WEIGHT : int ref;;
val fiBASETP_WEIGHT : int ref;;
val fiOTP_WEIGHT : int ref;;

val fiTRANSLUCENT_EXPAND_DELAY : int ref;;
val fiCHOICE : bool ref;;
val fiENUM_ITER_DEEP_DELAY : int ref;;
val fiENUM_ITER_DEEP_INCR : int ref;;
val fiENUM_MASK : int ref;;
val fiENUM_ARROW : int ref;;
val fiENUM_CHOICE : int ref;;
val fiENUM_IMP : int ref;;
val fiENUM_FALSE : int ref;;
val fiENUM_NEG : int ref;;
val fiENUM_FORALL : int ref;;
val fiENUM_EQ : int ref;;
val fiPROJECT_DELAY : int ref;;
val fiFILTER_INCR : int ref;;
val fiSYM_EQ : bool ref;;

val fiPOST_OR_L_DELAY : int ref;;
val fiPOST_OR_R_DELAY : int ref;;
val fiPOST_NOR_L_DELAY : int ref;;
val fiPOST_NOR_R_DELAY : int ref;;
val fiPOST_EQO_L_DELAY : int ref;;
val fiPOST_EQO_R_DELAY : int ref;;
val fiPOST_EQO_NL_DELAY : int ref;;
val fiPOST_EQO_NR_DELAY : int ref;;
val fiFORALL_DELAY : int ref;;
val fbFILTER_UNIV : bool ref;;

val fiINSTANTIATION_ORDER_CYCLE : int ref;;
val fiINSTANTIATION_ORDER_MASK : int ref;;
val fiINSTANTIATION_DELAY : int ref;;
val fiPOST_DEC_DELAY : int ref;;
val fbEAGERLY_PROCESS_INSTANTIATIONS : bool ref;;

val fiDUALQUEUE_MOD : int ref;;

val fiPOST_NEQO_L_DELAY : int ref;;
val fiPOST_NEQO_R_DELAY : int ref;;
val fiPOST_NEQO_NL_DELAY : int ref;;
val fiPOST_NEQO_NR_DELAY : int ref;;

val fbFILTER_POSATM : bool ref;;
val fbFILTER_NEGATM : bool ref;;
val fiPRE_MATING_DELAY_POS : int ref;;
val fiPRE_MATING_DELAY_NEG : int ref;;

val fbDYNAMIC_SYMBRELN : bool ref;;
val fiSYMBRELN_DELAY : int ref;;
val fbDYNAMIC_IRREFBRELN : bool ref;;
val fiIRREFBRELN_DELAY : int ref;;
val fbDYNAMIC_COV1BRELN : bool ref;;
val fiCOV1BRELN_DELAY1 : int ref;;
val fiCOV1BRELN_DELAY2 : int ref;;
val fbDYNAMIC_NOCL1BRELN : bool ref;;
val fiNOCL1BRELN_DELAY : int ref;;
