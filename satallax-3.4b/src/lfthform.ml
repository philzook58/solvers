open Syntax
open Printf

(* lambda-free typed higher-order formulas *)
type lfthterm =
    LFTHVar of int * lfthterm list
  | LFTHFun of string * stp * lfthterm list
type lfthform =
    LFTHEq of lfthterm * lfthterm (* term equivalence *)
  | LFTHPred of string * stp * lfthterm list
  | LFTHImp of lfthform * lfthform (* implication *)
  | LFTHEqu of lfthform * lfthform (* logical equivalence *)
  | LFTHAll of int * stp * lfthform
  | LFTHFal (* false *)

exception NotLFTH

let lfthfneg lfthf =
  match lfthf with
  | LFTHImp(m,LFTHFal) -> m
  | _ -> LFTHImp(lfthf,LFTHFal)


let iter_lfthterm_consts f =
  let rec aux lftht = match lftht with
    LFTHVar _ -> ()
  | LFTHFun (x, i, al) -> f x i; List.iter aux al
  in aux

let iter_lfthform_consts f =
  let rec aux lfthf = match lfthf with
    LFTHEq (t1, t2) -> iter_lfthterm_consts f t1; iter_lfthterm_consts f t2
  | LFTHPred (x, i, al) -> f x i; List.iter (iter_lfthterm_consts f) al
  | LFTHImp (f1, f2)
  | LFTHEqu (f1, f2) -> aux f1; aux f2
  | LFTHAll (x, i, frm) -> aux frm
  | LFTHFal -> ()
  in aux


(* variables must not contain Prop anywhere in their types *)
let lfth_var_type a = not (stp_contains Prop a)
(* constants may contain Prop, but only as final return value *)
let rec lfth_const_type = function
    Ar (a, b) -> (not (stp_contains Prop a)) && lfth_const_type b
  | _ -> true

let rec trm_to_lfthterm vl (ml:trm list) m =
  match m with
  | Name(x,a) when lfth_const_type a ->
      LFTHFun (x, a, List.map (trm_to_lfthterm vl []) ml)
  | DB(j,a) when lfth_var_type a ->
      LFTHVar (List.nth vl j, List.map (trm_to_lfthterm vl []) ml)
  | Ap(m1,m2) -> trm_to_lfthterm vl (m2::ml) m1
  | _ -> raise NotLFTH

let rec trm_to_lfthatom vl (ml:trm list) m =
  match m with
  | Name(x,a) when lfth_const_type a ->
      LFTHPred(x, a, List.map (trm_to_lfthterm vl []) ml)
  | Ap(m1,m2) -> trm_to_lfthatom vl (m2::ml) m1
  | _ -> raise NotLFTH

let rec trm_to_lfthform eqoequiv vl p =
  match p with
  | False -> LFTHFal
  | Ap(Forall(a),Lam(_,p1)) when lfth_var_type a ->
      let x = List.length vl in
      LFTHAll(x, a, trm_to_lfthform eqoequiv (x::vl) p1)
  | Ap(Ap(Imp,p1),p2) ->
      LFTHImp (trm_to_lfthform eqoequiv vl p1,
               trm_to_lfthform eqoequiv vl p2)
  | Ap(Ap(Eq(Prop),p1),p2) when eqoequiv ->
      LFTHEqu (trm_to_lfthform eqoequiv vl p1,
               trm_to_lfthform eqoequiv vl p2)
  | Ap(Ap(Eq(a),m1),m2) when lfth_var_type a ->
      LFTHEq (trm_to_lfthterm vl [] m1,
              trm_to_lfthterm vl [] m2)
  | _ -> trm_to_lfthatom vl [] p


let fprintf_ap c f head l =
  let rec aux = function
    [] -> ()
  | x::xs -> fprintf c " @ "; f c x; aux xs
  in
    if l <> [] then fprintf c "(";
    fprintf c "%s" head; aux l;
    if l <> [] then fprintf c ")"

let rec fprintf_lfthterm c m =
  match m with
  | LFTHVar(x, al) -> fprintf_ap c fprintf_lfthterm ("X" ^ string_of_int x) al
  | LFTHFun(f, _, al) -> fprintf_ap c fprintf_lfthterm ("f" ^ f) al

let rec fprintf_lfthf c m =
  match m with
  | LFTHEq(t1,t2) ->
      fprintf c "(";
      fprintf_lfthterm c t1;
      fprintf c " = ";
      fprintf_lfthterm c t2;
      fprintf c ")";
  | LFTHPred(p, _, al) ->
      fprintf_ap c fprintf_lfthterm ("f" ^ p) al;
  | LFTHImp(m1,LFTHFal) -> (*** handle this as negation because => $false seems to confuse E ***)
      fprintf c "(~ ";
      fprintf_lfthf c m1;      
      fprintf c ")";
  | LFTHImp(m1,m2) ->
      fprintf c "(";
      fprintf_lfthf c m1;
      fprintf c " => ";
      fprintf_lfthf c m2;
      fprintf c ")";
  | LFTHEqu(m1,m2) ->
      fprintf c "(";
      fprintf_lfthf c m1;
      fprintf c " <=> ";
      fprintf_lfthf c m2;
      fprintf c ")";
  | LFTHAll(x, a, m1) ->
      fprintf c "( ! [X%d : %s] : " x (stp_str a);
      fprintf_lfthf c m1;
      fprintf c ")";
  | LFTHFal ->
      fprintf c "$false"

let rec fprintf_lfthf_neg c m =
  match m with
  | LFTHAll(x,a,m1) ->
      fprintf c "( ? [X%d: %s] : " x (stp_str a);
      fprintf_lfthf_neg c m1;
      fprintf c ")"
  | _ ->
      fprintf c "(~ ";
      fprintf_lfthf c m;
      fprintf c ")"
