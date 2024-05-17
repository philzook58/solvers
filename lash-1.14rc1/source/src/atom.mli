(* Lash *)
(* ported from Satallax file: atom.mli *)

open Syntax

type atom = int
type literal = int

val max_atom : unit -> atom
val atom_to_trm : atom -> ftm

(*val assignedp : ftm -> bool*)

val get_literal : ftm -> literal
val literal_to_trm : literal -> ftm

val print_model : (atom -> int) -> bool -> unit
