(* File: refut.ml *)
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

(*** For printing a ruleinfo - helpful for debugging. - Chad, Oct 2010 ***)
let ruleinfo_str s =
  match s with
  | NegPropRule(m) -> ("NegPropRule(" ^ (trm_str m) ^ ")")
  | PosPropRule(m) -> ("PosPropRule(" ^ (trm_str m) ^ ")")
  | InstRule(a,m,n) -> ("InstRule(" ^ (stp_str a) ^ "," ^ (trm_str m) ^ "," ^ (trm_str n) ^ ")")
  | FreshRule(a,m,x) -> ("FreshRule(" ^ (stp_str a) ^ "," ^ (trm_str m) ^ "," ^ x ^ ")")
  | MatingRule(plit,nlit) -> "MatingRule(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ConfrontationRule(plit,nlit) -> "ConfrontationRule(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ChoiceRule(eps,pred) -> "ChoiceRule(" ^ (trm_str eps) ^ "," ^ (trm_str pred) ^ ")"
  | Known(l,cname,al) -> "Known(" ^ (string_of_int l) ^ "," ^ cname ^ ")"
  | DeltaRule -> "DeltaRule"

(*** For printing the refutation - helpful for debugging. - Chad, Oct 2010 ***)
let rec print_refut r =
  match r with
  | NegImpR(m,n,r1) ->
      Printf.printf "NegImpR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1
  | ImpR(m,n,r1,r2) ->
      Printf.printf "ImpR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | FalseR ->
      Printf.printf "FalseR\n"
  | NegReflR(_) ->
      Printf.printf "NegReflR\n"
  | NegAllR(a,m,x,r) ->
      Printf.printf "NegAllR\n  fresh var:%s\n  stp: %s\n   body: %s\n" x (stp_str a) (trm_str m);
      print_refut r
  | NegEqFR(a,b,m,n,r) ->
      Printf.printf "NegEqFR\n  stp: (%s)   ->   (%s)\nleft: %s\n  right: %s\n" (stp_str a) (stp_str b) (trm_str m) (trm_str n);
  | EqOR(m,n,r1,r2) ->
      Printf.printf "EqOR\n  left: %s\n  right: %s\n" (trm_str m) (trm_str n);
      print_refut r1;
      print_refut r2
  | NegEqOR(m,n,r1,r2) ->
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
	    (fun z -> (Printf.printf "Atom %d: %s\n" (abs z) (trm_str (Atom.atom_to_trm (abs z)))))
	    c;
	  try Printf.printf "associated rule: %s\n" (ruleinfo_str (cr c))
	  with Not_found -> Printf.printf "no associated rule\n"
	)
	cl
  | Eprover(pcore,cr,fcore,elines) ->
      Printf.printf "Eprover\n";
      List.iter (fun l -> Printf.printf "%s\n" l) elines;
      Printf.printf " propositional part:";
      List.iter
	(fun c ->
	  Printf.printf "%s\n" (String.concat " " (List.map string_of_int c));
	  List.iter
	    (fun z -> (Printf.printf "Atom %d: %s\n" (abs z) (trm_str (Atom.atom_to_trm (abs z)))))
	    c;
	  try Printf.printf "associated rule: %s\n" (ruleinfo_str (cr c))
	  with Not_found -> Printf.printf "no associated rule\n"
	)
	pcore;
      Printf.printf "\n first-order part: ";
      List.iter
	(fun a -> Printf.printf " %d" a)
	fcore;
      Printf.printf "\n"
	
(** Extraction of constants and types from different kinds of types. **)

(*List the constants that occur in a rule-info, as name-type pairs.
  NOTE the resulting list doesn't contain duplicate constants.*)
let rec consts_of_ruleinfo acc : ruleinfo -> ctx = function
    NegPropRule t
  | PosPropRule t
  | FreshRule (_, t, _) -> consts_of_trm acc t
  | InstRule (_, t1, t2)
  | ChoiceRule (t1, t2) ->
    let acc' = consts_of_trm acc t1
    in consts_of_trm acc' t2
  | ConfrontationRule (_, _)
  | MatingRule (_, _)
  | Known (_, _, _) -> acc
  | DeltaRule -> acc

let fold_clause f =
  List.fold_right (fun z acc -> f acc (Atom.atom_to_trm (abs z)))

let fold_searchr ft fr cl cr =
  List.fold_right (fun c acc ->
    let acc' = fold_clause ft c acc in
    try fr acc' (cr c) with Not_found -> acc') cl

(*List the constants that occur in a refutation, as name-type pairs.
  NOTE the resulting list doesn't contain duplicate constants.*)
let rec consts_of_refut acc : refut -> ctx = function
    NegImpR (t1, t2, r)
  | NegEqFR (_, _, t1, t2, r) ->
    let acc' = consts_of_trm acc t1 in
    let acc'' = consts_of_trm acc' t2 in
    consts_of_refut acc'' r
  | NegAllR (stp, t, name, r) ->
    let acc' =
      begin
(*        print_endline name; *)
      try
        let stp' = List.assoc name acc
        in
          if stp' <> stp then failwith "Different types for same constant?"
          else acc
      with Not_found ->
        (name, stp) :: acc
      end in
    let acc'' = consts_of_trm acc' t in
    consts_of_refut acc'' r
  | EqOR (t1, t2, r1, r2)
  | NegEqOR (t1, t2, r1, r2)
  | ImpR (t1, t2, r1, r2) ->
    let acc' = consts_of_trm acc t1 in
    let acc'' = consts_of_trm acc' t2 in
    let acc''' = consts_of_refut acc'' r1 in
    consts_of_refut acc''' r2
  | FalseR
  | NegReflR(_)
  | AssumptionConflictR(_) -> acc
  | SearchR (cl, cr) -> fold_searchr consts_of_trm consts_of_ruleinfo cl cr acc
  | Eprover(pcore,cr,fcore,elines) -> fold_searchr consts_of_trm consts_of_ruleinfo pcore cr acc (*** ignoring fcore, questionable ***)

(*List the base types that are referenced in a rule-info.
  NOTE the resulting list doesn't contain duplicate elements.*)
let rec base_types_of_ruleinfo acc : ruleinfo -> string list = function
    NegPropRule t
  | PosPropRule t -> base_types_of_trm acc t
  | FreshRule (stp, t, _) ->
    let acc' = base_types acc stp
    in base_types_of_trm acc' t
  | InstRule (stp, t1, t2) ->
    let acc' = base_types_of_trm acc t1 in
    let acc'' = base_types_of_trm acc' t2
    in base_types acc'' stp
  | Known (_, _, stps) ->
    List.fold_right (fun x y -> base_types y x) stps acc
  | ChoiceRule (t1, t2) ->
    let acc' = base_types_of_trm acc t1
    in base_types_of_trm acc' t2
  | ConfrontationRule (_, _)
  | MatingRule (_, _) -> acc
  | DeltaRule -> acc

(*List the base types that are referenced in a refutation.
  NOTE the resulting list doesn't contain duplicate elements.*)
let rec base_types_of_refut acc : refut -> string list = function
    NegImpR (t1, t2, r) ->
    let acc' = base_types_of_trm acc t1 in
    let acc'' = base_types_of_trm acc' t2 in
    base_types_of_refut acc'' r
  | NegEqFR (stp1, stp2, t1, t2, r) ->
    let acc' = base_types_of_trm acc t1 in
    let acc'' = base_types_of_trm acc' t2 in
    let acc3 = base_types acc'' stp1 in
    let acc4 = base_types acc3 stp2 in
    base_types_of_refut acc4 r
  | NegAllR (stp, t, _, r) ->
    let acc' = base_types acc stp in
    let acc'' = base_types_of_trm acc' t in
    base_types_of_refut acc'' r
  | EqOR (t1, t2, r1, r2)
  | NegEqOR (t1, t2, r1, r2)
  | ImpR (t1, t2, r1, r2) ->
    let acc' = base_types_of_trm acc t1 in
    let acc'' = base_types_of_trm acc' t2 in
    let acc''' = base_types_of_refut acc'' r1 in
    base_types_of_refut acc''' r2
  | FalseR
  | NegReflR(_)
  | AssumptionConflictR(_) -> acc
  | SearchR (cl, cr) -> fold_searchr base_types_of_trm base_types_of_ruleinfo cl cr acc
  | Eprover(pcore,cr,fcore,elines) -> fold_searchr base_types_of_trm base_types_of_ruleinfo pcore cr acc (*** ignoring fcore; questionable ***)

type refutsiginfo = {
    basetypes : (string,unit) Hashtbl.t;
    consttypes : (string,stp) Hashtbl.t;
    eigendefs : (string,trm) Hashtbl.t;
    propreferenced : (int,unit) Hashtbl.t
  }
      
let refutsiginfo_init () : refutsiginfo =
  { basetypes = Hashtbl.create 2;
    consttypes = Hashtbl.create 100;
    eigendefs = Hashtbl.create 30;
    propreferenced = Hashtbl.create 100
  }
    
let refutsiginfo_of_ruleinfo {basetypes;consttypes;eigendefs;propreferenced} : ruleinfo -> unit = function
    NegPropRule t
  | PosPropRule t ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t)
  | FreshRule (a, t, x) ->
      if not (Hashtbl.mem eigendefs x) then Hashtbl.add eigendefs x (Ap(Choice(a),Lam(a,Ap(Ap(Imp,gen_lam_body a t),False))));
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] a);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t)
  | InstRule (a, t1, t2) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] a);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t2);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t1);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t2)
  | Known(_,_,al) ->
      List.iter (fun a -> List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] a)) al
  | ChoiceRule (t1, t2) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t2);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t1);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t2)
  | ConfrontationRule (_, _)
  | MatingRule (_, _)
  | DeltaRule -> ()
    
let rec refutsiginfo_of_refut {basetypes;consttypes;eigendefs;propreferenced} : refut -> unit = function
    NegImpR (t1, t2, r)
  | NegEqFR (_, _, t1, t2, r) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t2);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t1);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t2);
      refutsiginfo_of_refut {basetypes;consttypes;eigendefs;propreferenced} r
  | NegAllR (a, t, w, r) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types [] a);
      if not (Hashtbl.mem consttypes w) then Hashtbl.add consttypes w a;
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t);
      refutsiginfo_of_refut {basetypes;consttypes;eigendefs;propreferenced} r
  | EqOR (t1, t2, r1, r2)
  | NegEqOR (t1, t2, r1, r2)
  | ImpR (t1, t2, r1, r2) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t1);
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t2);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t1);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t2);
      refutsiginfo_of_refut {basetypes;consttypes;eigendefs;propreferenced} r1;
      refutsiginfo_of_refut {basetypes;consttypes;eigendefs;propreferenced} r2
  | FalseR -> ()
  | NegReflR(t) ->
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t)
  | AssumptionConflictR(l) ->
      let a = if l > 0 then l else -l in
      if not (Hashtbl.mem propreferenced a) then Hashtbl.add propreferenced a ();
      let t = atom_to_trm a in
      List.iter (fun x -> if not (Hashtbl.mem basetypes x) then Hashtbl.add basetypes x ()) (base_types_of_trm [] t);
      List.iter (fun (c,a) -> if not (Hashtbl.mem consttypes c) then Hashtbl.add consttypes c a) (consts_of_trm [] t)
  | SearchR (cl, cr) ->
      List.iter
	(fun c ->
	  List.iter
	    (fun l ->
	      let a = if l > 0 then l else -l in
	      if not (Hashtbl.mem propreferenced a) then Hashtbl.add propreferenced a ()) c;
	  try
	    refutsiginfo_of_ruleinfo {basetypes;consttypes;eigendefs;propreferenced} (cr c)
	  with Not_found -> ())
	cl
  | Eprover(pcore,cr,fcore,elines) ->
      List.iter
	(fun c ->
	  List.iter
	    (fun l ->
	      let a = if l > 0 then l else -l in
	      if not (Hashtbl.mem propreferenced a) then Hashtbl.add propreferenced a ()) c;
	  try
	    refutsiginfo_of_ruleinfo {basetypes;consttypes;eigendefs;propreferenced} (cr c)
	  with Not_found -> ())
	pcore;
      List.iter
	(fun l ->
	  let a = if l > 0 then l else -l in
	  if not (Hashtbl.mem propreferenced a) then Hashtbl.add propreferenced a ())
	fcore

exception Unsatisfiable of refut option
exception Satisfiable
