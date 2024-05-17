open Preterm

type stp = Base of string | Prop | Ar of (stp * stp)

exception ExpectedTypeError of pretrm * stp * stp

type ctx = (string * stp) list

type trm =
    Name of string * stp
  | False | Imp | Forall of stp | Eq of stp | Choice of stp
  | True | Neg | Or | And | Iff | Exists of stp (*** These are normalized away. ***)
  | DB of int * stp
  | Lam of stp * trm
  | Ap of trm * trm


val imp:trm -> trm -> trm
val preneg:trm -> trm
val neg:trm -> trm
val normneg:trm -> trm
val disj:trm -> trm -> trm
val conj:trm -> trm -> trm
val iff:trm -> trm -> trm
val eq:stp -> trm -> trm -> trm
val ueq:trm -> trm -> trm
val forall:stp -> trm -> trm
val exists:stp -> trm -> trm
val choice:stp -> trm -> trm

val stp_str:stp -> string
val stp_contains : stp -> stp -> bool
val trm_str:trm -> string
val next_var_name : stp -> string list -> string list -> string
val trm_str_nice_rec:trm -> string list -> string list -> string * int
val trm_str_nice:trm -> string (*** gives a version with named vars and ~, ->, ! intended to be more readable for the humans ***)

val tpof:trm -> stp

(*** This builds an application after checking the types agree. ***)
val ap:trm * trm -> trm

val print_stp_coq:out_channel -> stp -> (string,string) Hashtbl.t -> bool -> unit
val print_stp_isar:out_channel -> stp -> (* (string,string) Hashtbl.t -> *) bool -> unit
val print_stp_coq2:out_channel -> stp -> bool -> unit



val shift:trm -> int -> int -> trm
val subst:trm -> int -> trm -> trm
val simulsubst:trm -> trm list -> trm
val namesubst:trm -> string -> trm -> trm
val gen_lam_body:stp -> trm -> trm
val termNotFreeIn:trm -> int -> bool
val termNotFreeInL:trm -> int list -> bool
val termNoDBs:trm -> bool
val norm1:(string,trm) Hashtbl.t -> trm -> trm * bool
val norm:(string,trm) Hashtbl.t -> trm -> trm
val betanorm:(string,trm) Hashtbl.t -> trm -> trm
val onlybetanorm1:trm -> trm * bool
val onlybetanorm:trm -> trm
val negnorm1 : trm -> trm * bool
val onlynegnorm : trm -> trm
val logicnorm:trm -> trm

val basetypestobool : bool ref

val to_stp:pretrm -> stp
val to_trm:(string,(trm * stp) * bool ref) Hashtbl.t -> ctx -> pretrm -> stp option -> trm * stp

val neg_p:trm -> bool
val neg_body:trm -> trm option
val eq_body:trm -> (stp * trm * trm) option

val bounded_head_spine: int -> trm -> trm * trm list
val head_spine: trm -> trm * trm list

val rtp : stp -> stp
val argtps_rtp : stp -> stp list * stp

val consts_of_trm : ctx -> trm -> ctx
val base_types : string list -> stp -> string list
val base_types_of_trm : string list -> trm -> string list

val make_fresh_name : int -> string
val normalize_fresh_uni : trm -> trm
val normalize_fresh_asc : trm -> ((string * int) list * int) * trm
val normalize_asc : trm -> ((string * int) list * int) * trm
val contains_fresh_names : trm -> bool
