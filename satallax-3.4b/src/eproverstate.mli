open Foform
open Syntax

val prop_fo_forms : (int * foform) list ref
val stp_fo_forms : (stp,int * foform) Hashtbl.t
val fo_types_h : (stp,unit) Hashtbl.t
val fo_types : stp list ref
val fo_ecounter : (stp,int ref) Hashtbl.t
val atom_fof : (Atom.atom, foform) Hashtbl.t
val lfth_ecounter : int ref

val reset_eprover_state : unit -> unit
