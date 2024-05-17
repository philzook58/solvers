(* File: refut.mli *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open Term
open Atom

type clause = literal list

type ruleinfo =
 (*** NegPropRule(m) For rules requiring one negative formula in the head, except negated forall ***)
    NegPropRule of trm
 (*** PosPropRule(m) For rules requiring one positive formula in the head, except forall ***)
  | PosPropRule of trm
 (*** InstRule(a,m,n) For instantiating a Ap(Forall(a),m) with n:a ***)
  | InstRule of stp * trm * trm
 (*** FreshRule(a,m,x) For producing a witness x for Ap(Neg,Ap(Forall(a),m)) ***)
  | FreshRule of stp * trm * string
 (*** MatingRule(plit,nlit) For mating rule, only save the literals here ***)
  | MatingRule of literal * literal
 (*** ConfrontationRule(plit,nlit) For confrontation rule, only save the literals here ***)
  | ConfrontationRule of literal * literal
 (*** ChoiceRule(eps,pred) ***)
  | ChoiceRule of trm * trm
 (*** Known(lit,coqname,stp list) ***)
  | Known of literal * string * stp list
 (*** Delta Rule (expansion of some defns) ***)
  | DeltaRule

type refut =
    NegImpR of trm * trm * refut
  | ImpR of trm * trm * refut * refut
  | FalseR
  | NegReflR of trm
  | NegAllR of stp * trm * string * refut
  | NegEqFR of stp * stp * trm * trm * refut
  | EqOR of trm * trm * refut * refut
  | NegEqOR of trm * trm * refut * refut
  | SearchR of clause list * (clause -> ruleinfo)
  | AssumptionConflictR of int
 (*** Eprover ***)
  | Eprover of clause list * (clause -> ruleinfo) * int list * string list

val ruleinfo_str : ruleinfo -> string

val print_refut : refut -> unit (*** Only for debugging. ***)

val base_types_of_ruleinfo : string list -> ruleinfo -> string list
val base_types_of_refut : string list -> refut -> string list
val consts_of_ruleinfo : ctx -> ruleinfo -> ctx
val consts_of_refut : ctx -> refut -> ctx

type refutsiginfo = {
    basetypes : (string,unit) Hashtbl.t;
    consttypes : (string,stp) Hashtbl.t;
    eigendefs : (string,trm) Hashtbl.t;
    propreferenced : (int,unit) Hashtbl.t
  }
      
val refutsiginfo_init : unit -> refutsiginfo
val refutsiginfo_of_ruleinfo : refutsiginfo -> ruleinfo -> unit
val refutsiginfo_of_refut : refutsiginfo -> refut -> unit

exception Unsatisfiable of refut option
exception Satisfiable
