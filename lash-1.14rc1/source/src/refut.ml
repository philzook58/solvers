(* Lash *)
(* ported from Satallax file: *)
(* File: refut.ml *)
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

(*** For printing a ruleinfo - helpful for debugging. - Chad, Oct 2010 ***)
let ruleinfo_str s =
  match s with
  | NegPropRule(m) -> ("NegPropRule(" ^ (ftm_str m) ^ ")")
  | PosPropRule(m) -> ("PosPropRule(" ^ (ftm_str m) ^ ")")
  | InstRule(a,m,n) -> ("InstRule(" ^ (stp_str (ty_f_rev a)) ^ "," ^ (ftm_str m) ^ "," ^ (ftm_str n) ^ ")")
  | FreshRule(a,m,x) -> ("FreshRule(" ^ (stp_str (ty_f_rev a)) ^ "," ^ (ftm_str m) ^ "," ^ x ^ ")")
  | MatingRule(plit,nlit) -> "MatingRule(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ConfrontationRule(plit,nlit) -> "ConfrontationRule(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ChoiceRule(eps,pred) -> "ChoiceRule(" ^ (ftm_str eps) ^ "," ^ (ftm_str pred) ^ ")"
  | Known(l,cname,al) -> "Known(" ^ (string_of_int l) ^ "," ^ cname ^ ")"
  | DeltaRule -> "DeltaRule"

(*** For printing the refutation - helpful for debugging. - Chad, Oct 2010 ***)
let rec print_refut r =
  match r with
  | NegImpR(_,_,_,m,n,r1) ->
      Printf.printf "NegImpR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1
  | ImpR(_,_,_,m,n,r1,r2) ->
      Printf.printf "ImpR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | FalseR ->
      Printf.printf "FalseR\n"
  | NegReflR(_) ->
      Printf.printf "NegReflR\n"
  | NegAllR(a,_,_,m,x,r) ->
      Printf.printf "NegAllR\n  fresh var:%s\n  stp: %s\n   body: %s\n" x (stp_str a) (trm_str m);
      print_refut r
  | NegEqFR(a,b,_,_,m,n,r) ->
      Printf.printf "NegEqFR\n  stp: (%s)   ->   (%s)\nleft: %s\n  right: %s\n" (stp_str a) (stp_str b) (trm_str m) (trm_str n);
  | EqOR(_,_,_,m,n,r1,r2) ->
      Printf.printf "EqOR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | NegEqOR(_,_,_,m,n,r1,r2) ->
      Printf.printf "NegEqOR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | AssumptionConflictR(i) ->
      Printf.printf "AssumptionConflictR %d\n" i;
  | SearchR(cl,cr) ->
      Printf.printf "SearchR\n  clauses with search options:\n";
      List.iter
	(fun c ->
	  Printf.printf "%s\n" (String.concat " " (List.map string_of_int c));
	  List.iter
	    (fun z -> (Printf.printf "Atom %d: %s\n" (abs z) (ftm_str (Atom.atom_to_trm (abs z)))))
	    c;
	  try Printf.printf "associated rule: %s\n" (ruleinfo_str (cr c))
	  with Not_found -> Printf.printf "no associated rule\n"
	)
	cl
	
(** Extraction of constants and types from different kinds of types. **)

let fold_clause f =
  List.fold_right (fun z acc -> f acc (Atom.atom_to_trm (abs z)))

let fold_searchr ft fr cl cr =
  List.fold_right (fun c acc ->
    let acc' = fold_clause ft c acc in
    try fr acc' (cr c) with Not_found -> acc') cl

type refutsiginfo = {
    basetypes : (int,unit) Hashtbl.t;
    consttypes : (int,stp) Hashtbl.t;
    eigendefs : (string,trm) Hashtbl.t;
    propreferenced : (int,unit) Hashtbl.t
  }
      
let refutsiginfo_init () : refutsiginfo =
  { basetypes = Hashtbl.create 2;
    consttypes = Hashtbl.create 100;
    eigendefs = Hashtbl.create 30;
    propreferenced = Hashtbl.create 100
  }
    
let refutsiginfo_of_ruleinfo nh {basetypes;consttypes;eigendefs;propreferenced} : ruleinfo -> unit = function
    NegPropRule t
  | PosPropRule t ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (List.map (fun (x,a) -> (x,ty_f_rev a)) (consts_of_ftm nh [] t))
  | FreshRule (a, t, x) ->
       if not (Hashtbl.mem eigendefs x) then (let a = ty_f_rev a in Hashtbl.add eigendefs x (Ap(Choice(a),Lam(a,Ap(Ap(Imp,gen_lam_body a (ftm_trm_2 nh [] t)),False)))));
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] (ty_f_rev a));
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (List.map (fun (x,a) -> (x,ty_f_rev a)) (consts_of_ftm nh [] t))
  | InstRule (a, t1, t2) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] (ty_f_rev a));
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t2);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (List.map (fun (x,a) -> (x,ty_f_rev a)) (consts_of_ftm nh [] t1));
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (List.map (fun (x,a) -> (x,ty_f_rev a)) (consts_of_ftm nh [] t2))
  | Known(_,_,al) ->
      List.iter (fun a -> List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] a)) al
  | ChoiceRule (t1, t2) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t2);
      List.iter (fun (c,a) -> let a = ty_f_rev a in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_ftm nh [] t1);
      List.iter (fun (c,a) -> let a = ty_f_rev a in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_ftm nh [] t2)
  | ConfrontationRule (_, _)
  | MatingRule (_, _)
  | DeltaRule -> ()
    
let rec refutsiginfo_of_refut nh {basetypes;consttypes;eigendefs;propreferenced} : refut -> unit = function
    NegImpR (_, _, _, t1, t2, r)
  | NegEqFR (_, _, _, _, t1, t2, r) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t2);
      List.iter (fun (c,a) -> let c = name_no c in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t1);
      List.iter (fun (c,a) -> let c = name_no c in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t2);
      refutsiginfo_of_refut nh {basetypes;consttypes;eigendefs;propreferenced} r
  | NegAllR (a, _, _, t, w, r) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] a);
      let w = name_no w in
      if not (Hashtbl.mem consttypes w) then Hashtbl.add consttypes w a;
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> let c = name_no c in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t);
      refutsiginfo_of_refut nh {basetypes;consttypes;eigendefs;propreferenced} r
  | EqOR (_, _, _, t1, t2, r1, r2)
  | NegEqOR (_, _, _, t1, t2, r1, r2)
  | ImpR (_, _, _, t1, t2, r1, r2) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t2);
      List.iter (fun (c,a) -> let c = name_no c in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t1);
      List.iter (fun (c,a) -> let c = name_no c in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t2);
      refutsiginfo_of_refut nh {basetypes;consttypes;eigendefs;propreferenced} r1;
      refutsiginfo_of_refut nh {basetypes;consttypes;eigendefs;propreferenced} r2
  | FalseR -> ()
  | NegReflR(_, t) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> let c = name_no c in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t)
  | AssumptionConflictR(l) ->
      let a = if l > 0 then l else -l in
      if not (Hashtbl.mem propreferenced a) then Hashtbl.add propreferenced a ();
      let t = atom_to_trm a in
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm_f [] t);
      List.iter (fun (c,a) -> let a = ty_f_rev a in if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_ftm nh [] t)
  | SearchR (cl, cr) ->
      List.iter
	(fun c ->
	  List.iter
	    (fun l ->
	      let a = if l > 0 then l else -l in
	      if not (Hashtbl.mem propreferenced a) then Hashtbl.add propreferenced a ()) c;
	  try
	    refutsiginfo_of_ruleinfo nh {basetypes;consttypes;eigendefs;propreferenced} (cr c)
	  with Not_found -> ())
	cl

exception Unsatisfiable of (unit -> refut) option
exception Satisfiable
