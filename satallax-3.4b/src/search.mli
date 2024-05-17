(* File: search.ml *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open Flags
open State
open Syntax

val enable_pattern_clauses : bool ref

val preprocess : trm -> trm

val decompose : int -> trm list -> trm list -> Refut.ruleinfo option -> unit
val confront : stp -> int -> trm -> trm -> int -> trm -> trm -> trm list
val mate : int -> int -> trm list -> trm list -> trm list
val forall_rule : int -> stp -> trm -> trm -> trm
val negforall_rule : int -> stp -> trm -> trm
val process_unprocessed_prop : int -> trm -> unit

val search : unit -> unit
