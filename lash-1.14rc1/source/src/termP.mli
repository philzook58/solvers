open Term

val coq_used_names : (string,unit) Hashtbl.t
val coq_names : (string,string) Hashtbl.t
val coq_hyp_names : (string,string) Hashtbl.t

module Variables:
sig
  (** next variable counter and list of used variable names**)
  type t = int * (string list)
  val make : unit -> t
  val push : t -> t
  val top : t -> string
  val get : int -> 'a * 'b list -> 'b
end

val termP_init : unit -> unit

val tstpizename : string -> string
val trm_to_coq : out_channel -> trm -> int * string list -> int -> int -> unit
val trm_to_isar : out_channel -> trm -> int * string list -> unit
