open Syntax

type atom = int
type literal = int

val max_atom : unit -> atom

val new_atom_actions : (Syntax.trm -> atom -> unit) list ref

val atom_to_trm : atom -> trm

val assignedp : trm -> bool

val get_literal : trm -> literal
val literal_to_trm : literal -> trm

val print_model : (atom -> int) -> bool -> unit
