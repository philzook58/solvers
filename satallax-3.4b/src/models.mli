open Term
open Big_int

exception UninterpretedName of string * stp

type frame_2 = string -> big_int
type interp_2_names = string -> stp -> big_int
type interp_2 = frame_2 * interp_2_names
val current_interp_2s_1 : (interp_2 * (string,unit) Hashtbl.t) list ref
val current_interp_2s_2 : (interp_2 * (string,unit) Hashtbl.t) list ref
val current_interp_2s_4 : (interp_2 * (string,unit) Hashtbl.t) list ref
val current_interp_2s : unit -> (interp_2 * (string,unit) Hashtbl.t) list
val fr1: frame_2
val fr2: frame_2
val fr4: frame_2
val empty_name_interp : interp_2_names
val default_to_zero : interp_2_names -> string -> stp -> big_int
val print_interp_name_info : ctx -> interp_2_names -> unit
val print_interp_trm_info : trm -> interp_2 -> unit
val frame_2_dom_logsize : frame_2 -> stp -> big_int
val frame_2_dom_size : frame_2 -> stp -> big_int
val eval_interp_2 : interp_2 -> big_int list -> trm -> big_int
val search_interp_extensions_val : trm -> big_int -> interp_2 -> int -> interp_2 list
val count_true_false_interps : trm -> interp_2 list -> int * int
