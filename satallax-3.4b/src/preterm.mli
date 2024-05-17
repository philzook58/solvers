(* File: syntax.mli *)
(* Author: Chad E Brown *)
(* Created: March 2008/September 2008/September 2010 *)

open String

exception ParsingError of int * int * int * int * string
exception GenericSyntaxError of string
exception DeclareInd
exception Polymorphism

type pretrm =
    PName of string
  | PType | PPropTp | PIndTp | PIntTp | PRealTp | PTrue | PFalse | PIff | PNIff | PImplies | PRevImplies | POr | PNOr | PAnd | PNAnd | PEq | PNEq | PNeg | PForall | PExists
  | PInt of int
  | PReal of float
  | PAp of pretrm * pretrm
  | PULam of string list * pretrm
  | PLam of ((string * pretrm) list) * pretrm
  | PAll of ((string * pretrm) list) * pretrm
  | PEx of ((string * pretrm) list) * pretrm
  | PExU of string * pretrm * pretrm
  | PChoice of (string * pretrm) * pretrm
  | PAr of pretrm * pretrm
  | POf of pretrm * pretrm
  | PDef of pretrm * pretrm
  | PLet of string * pretrm * pretrm
  | PTLet of string * pretrm * pretrm * pretrm

type prectx = (string option * pretrm option * pretrm option) list

val prectx_lam : prectx -> pretrm -> pretrm

val prectx_all : prectx -> pretrm -> pretrm

val prectx_ar : prectx -> pretrm -> pretrm

val pretrm_str:pretrm -> string

type input =
    DeclareTHF of string * string * pretrm
  | Include of string


val coqify_name : string -> (string,string) Hashtbl.t -> (string,unit) Hashtbl.t -> string
val print_pretrm_coq:out_channel -> pretrm -> (string,string) Hashtbl.t -> (string,unit) Hashtbl.t -> int -> int -> unit
val print_pretrm_isar:out_channel -> pretrm -> (string,string) Hashtbl.t -> (string,unit) Hashtbl.t -> int -> int -> unit
val print_pretrm_coq2:out_channel -> pretrm -> int -> int -> unit
