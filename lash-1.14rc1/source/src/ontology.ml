(* Treatment of the ontological relations "is_of" and "all_of",
 * as present in "NUM007^0.ax"
 *)

open Term
open Flags
open Log

let recognize_hashroots = ref false

let is_of_names : string list ref = ref []
let all_of_names : string list ref = ref []
let is_of_name : (string,unit) Hashtbl.t = Hashtbl.create 1
let all_of_name : (string,unit) Hashtbl.t = Hashtbl.create 1

let  is_of_type = mk_ar (mk_base tyname_dollar_i) (mk_ar (mk_ar (mk_base tyname_dollar_i) (mk_prop)) (mk_prop))
let all_of_type = mk_ar (mk_ar (mk_base tyname_dollar_i) (mk_prop)) (mk_ar (mk_ar (mk_base tyname_dollar_i) (mk_prop)) (mk_prop))

(* TODO: I (Michael Faerber) changed the pattern match in all_of_p below.
 * Should I now also adapt all_of_hashroot?
 *)
let  is_of_hashroot = "01b8315391fd465f550f1a3788664028f3a6126b6bded775854e3b7d33765cd9"
let all_of_hashroot = "67f26991e531d6c57a2161d295d3cdf1f416713aa711d23ccb703b2431633300"

let is_of_p m =
  match m with
  | Name(x,t) when t = is_of_type -> Hashtbl.mem is_of_name x
  | Lam(a1,Lam(a2,Ap(DB(0,a3),DB(1,a4)))) ->
     is_base a1 && ty_get_no a1 = tyname_dollar_i && is_ar a2 && ty_get_l a2 = a1 && ty_get_r a2 = mk_prop && a2 = a3 && a4 = a1
  | _ -> false

let all_of_p m =
  match m with
  | Name(x,t) when t = all_of_type -> Hashtbl.mem all_of_name x
  | Lam(a1,Lam(a2,Ap(Forall(a3),Lam(a4,Ap(Ap(Imp,Ap(Ap(m1,DB(0,a5)),DB(2,a6))),Ap(DB(1,a7),DB(0,a8))))))) ->
     if is_ar a1 then
       let a1a = ty_get_l a1 in
       is_base a1a && ty_get_no a1a = tyname_dollar_i && ty_get_r a1 = mk_prop && a1 = a2 && a1 = a6 && a1 = a7 && a3 = a1a && a4 = a1a && a5 = a1a && a8 = a1a
     else
       false
  | _ -> false

let rec ontology_prop_p m =
  match m with
  | Ap(Ap(Name(x,t),m1),m2) when t = is_of_type && Hashtbl.mem is_of_name x -> true
  | Ap(Ap(Name(x,t),m1),m2) when t = all_of_type && Hashtbl.mem all_of_name x ->
      ontology_prop_p (gen_lam_body (mk_base tyname_dollar_i) m2)
  | Ap(Forall(a),m1) -> ontology_prop_p (gen_lam_body a m1)
  | Ap(Ap(Imp,m1),m2) -> ontology_prop_p m2
  | _ -> false

let translucent_defn_p m =
  get_bool_flag "ONTOLOGY_DEFS_TRANSLUCENT" && is_of_p m

let add_is_of_name x =
  if !verbosity > 20 then Format.printf "is_of relation found: %s\n%!" x;
  is_of_names := x::!is_of_names;
  Hashtbl.add is_of_name x ()

let add_all_of_name x =
  if !verbosity > 20 then Format.printf "all_of relation found: %s\n%!" x;
  all_of_names := x::!all_of_names;
  Hashtbl.add all_of_name x ()

let add_ontology_type x tp al =
  if !recognize_hashroots then begin
    if tp = is_of_type && List.mem ("hashroot", is_of_hashroot) al (*** this annotation signals the prover to treat the name as the ontological "is_of" relation ***)
    then add_is_of_name x
    else if tp = all_of_type && List.mem ("hashroot", all_of_hashroot) al (*** this annotation signals the prover to treat the name as the ontological "all_of" quantifier ***)
    then add_all_of_name x
  end

let add_ontology_term x tm =
  if is_of_p tm then add_is_of_name x
  else if all_of_p tm then add_all_of_name x
