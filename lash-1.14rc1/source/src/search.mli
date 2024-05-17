(* Lash *)
(* ported from Satallax file: *)
(* File: search.ml *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open Flags
open State
open Syntax

val enable_pattern_clauses : bool ref

val preprocess : ftm -> ftm

val decompose : int -> stp -> ftm list -> ftm list -> Refut.ruleinfo option -> unit
val confront : int -> int -> ftm -> ftm -> int -> ftm -> ftm -> unit
val forall_rule : int -> int -> ftm -> ftm -> unit
val negforall_rule : int -> int -> ftm -> unit
val process_unprocessed_prop : int -> ftm -> unit

val search : unit -> unit
