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

let  is_of_type = Ar(Base("$i"),Ar(Ar(Base("$i"),Prop),Prop))
let all_of_type = Ar(Ar(Base("$i"),Prop),Ar(Ar(Base("$i"),Prop),Prop))

(* TODO: I (Michael Faerber) changed the pattern match in all_of_p below.
 * Should I now also adapt all_of_hashroot?
 *)
let  is_of_hashroot = "01b8315391fd465f550f1a3788664028f3a6126b6bded775854e3b7d33765cd9"
let all_of_hashroot = "67f26991e531d6c57a2161d295d3cdf1f416713aa711d23ccb703b2431633300"

let is_of_p m =
  match m with
  | Name(x,t) when t = is_of_type -> Hashtbl.mem is_of_name x
  | Lam(Base("$i"),Lam(Ar(Base("$i"),Prop),Ap(DB(0,Ar(Base("$i"),Prop)),DB(1,Base("$i"))))) -> true
  | _ -> false

let all_of_p m =
  match m with
  | Name(x,t) when t = all_of_type -> Hashtbl.mem all_of_name x
  | Lam(Ar(Base("$i"),Prop),Lam(Ar(Base("$i"),Prop),Ap(Forall(Base("$i")),Lam(Base("$i"),Ap(Ap(Imp,Ap(Ap(m1,DB(0,Base("$i"))),DB(2,Ar(Base("$i"),Prop)))),Ap(DB(1,Ar(Base("$i"),Prop)),DB(0,Base("$i")))))))) ->
      is_of_p m1
  | _ -> false

let rec ontology_prop_p m =
  match m with
  | Ap(Ap(Name(x,t),m1),m2) when t = is_of_type && Hashtbl.mem is_of_name x -> true
  | Ap(Ap(Name(x,t),m1),m2) when t = all_of_type && Hashtbl.mem all_of_name x ->
      ontology_prop_p (gen_lam_body (Base("$i")) m2)
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
