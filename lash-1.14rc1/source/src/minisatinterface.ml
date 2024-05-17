(* File: minisatinterface.ml *)
(* Author: Chad E Brown *)
(* Created: November 2010 *)

external minisat_init        : int -> unit = "minisat_init" [@@noalloc];;
external minisat_addClause   : int list -> bool = "minisat_addClause" [@@noalloc];;
external minisat_search      : unit -> bool = "minisat_search";;
external minisat_search1     : int -> bool = "minisat_search1";;
external minisat_modelValue  : int -> int = "modelValue" [@@noalloc];;

