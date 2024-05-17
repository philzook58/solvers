(* File: flags.mli *)
(* Author: Chad E Brown *)
(* Created: September 2010 *)

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

val fiCONFR_SAME2_DELAY : int ref;;
val fiCONFR_SAME1_DELAY : int ref;;
val fiCONFR_DIFF_DELAY : int ref;;
val fiPOST_CONFRONT1_DELAY : int ref;;
val fiPOST_CONFRONT2_DELAY : int ref;;
val fiPOST_CONFRONT3_DELAY : int ref;;
val fiPOST_CONFRONT4_DELAY : int ref;;
val fiPRIORITY_QUEUE_IMPL : int ref;;
val fiDELAY_TRUE_IN_MODELS : int ref;;
val fiDELAY_FALSE_IN_MODELS : int ref;;
val fiDELAY_UNINFORMATIVE_IN_MODELS : int ref;;

val fiARTP_WEIGHT : int ref;;
val fiBASETP_WEIGHT : int ref;;
val fiOTP_WEIGHT : int ref;;
val fiTRANSLUCENT_EXPAND_DELAY : int ref;;
val fiENUM_ITER_DEEP_DELAY : int ref;;
val fiENUM_ITER_DEEP_INCR : int ref;;
val fiENUM_ARROW : int ref;;
val fiENUM_CHOICE : int ref;;
val fiENUM_IMP : int ref;;
val fiENUM_FALSE : int ref;;
val fiENUM_NEG : int ref;;
val fiENUM_FORALL : int ref;;
val fiENUM_EQ : int ref;;
val fiPROJECT_DELAY : int ref;;
val fiFILTER_INCR : int ref;;
