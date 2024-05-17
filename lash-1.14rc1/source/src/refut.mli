(* Lash *)
(* ported from Satallax file: *)
(* File: refut.mli *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open Ftm
open Term
open Atom

type clause = literal list

type ruleinfo =
 (*** NegPropRule(m) For rules requiring one negative formula in the head, except negated forall ***)
    NegPropRule of ftm
 (*** PosPropRule(m) For rules requiring one positive formula in the head, except forall ***)
  | PosPropRule of ftm
 (*** InstRule(a,m,n) For instantiating a Ap(Forall(a),m) with n:a ***)
  | InstRule of int * ftm * ftm
 (*** FreshRule(a,m,x) For producing a witness x for Ap(Neg,Ap(Forall(a),m)) ***)
  | FreshRule of int * ftm * string
 (*** MatingRule(plit,nlit) For mating rule, only save the literals here ***)
  | MatingRule of int * int
 (*** ConfrontationRule(plit,nlit) For confrontation rule, only save the literals here ***)
  | ConfrontationRule of int * int
 (*** ChoiceRule(eps,pred) ***)
  | ChoiceRule of ftm * ftm
 (*** Known(lit,coqname,stp list) ***)
  | Known of int * string * stp list
 (*** Delta Rule (expansion of some defns) ***)
  | DeltaRule

type refut =
    NegImpR of ftm * ftm * ftm * trm * trm * refut
  | ImpR of ftm * ftm * ftm * trm * trm * refut * refut
  | FalseR
  | NegReflR of ftm * trm
  | NegAllR of stp * ftm * ftm * trm * string * refut
  | NegEqFR of stp * stp * ftm * ftm * trm * trm * refut
  | EqOR of ftm * ftm * ftm * trm * trm * refut * refut
  | NegEqOR of ftm * ftm * ftm * trm * trm * refut * refut
  | SearchR of clause list * (clause -> ruleinfo)
  | AssumptionConflictR of int

val ruleinfo_str : ruleinfo -> string

val print_refut : refut -> unit (*** Only for debugging. ***)

type refutsiginfo = {
    basetypes : (int,unit) Hashtbl.t;
    consttypes : (int,stp) Hashtbl.t;
    eigendefs : (string,trm) Hashtbl.t;
    propreferenced : (int,unit) Hashtbl.t
  }
      
val refutsiginfo_init : unit -> refutsiginfo
val refutsiginfo_of_ruleinfo : (int,int) Hashtbl.t -> refutsiginfo -> ruleinfo -> unit
val refutsiginfo_of_refut : (int,int) Hashtbl.t -> refutsiginfo -> refut -> unit

exception Unsatisfiable of (unit -> refut) option
exception Satisfiable
