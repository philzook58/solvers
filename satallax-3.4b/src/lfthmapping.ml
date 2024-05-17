open Atom
open Lfthform
open Flags
open Log
open State
open Syntax
open Printf

let eeqoequiv = ref false

let lfth_forms = ref []
let lfth_consts = Hashtbl.create 10

let hashtbl_add_if_new tbl x y =
  if Hashtbl.mem tbl x then ()
  else Hashtbl.add tbl x y

(* Remember if a is LFTH, so I can send this to E.
 * Send it to E every E_PERIOD times. *)
let new_possible_lfth_formula_1 m a =
  let lfthf = trm_to_lfthform (!eeqoequiv) [] m in
  if (!verbosity > 4) then
    Printf.printf "Adding LFTHF for: %s\n%!" (trm_str m);

  (* collect constants appearing in formula *)
  iter_lfthform_consts (hashtbl_add_if_new lfth_consts) lfthf;

  if a > 0 then lfth_forms := (a,lfthf)::!lfth_forms
  (* shouldn't happen, but just in case *)
  else lfth_forms := (-a,lfthfneg lfthf)::!lfth_forms

let plit_lfth_str a =
  if a > 0 then "p" ^ (string_of_int a)
  else "~ (p" ^ (string_of_int (- a)) ^ ")"


let fprintf_lfthf_axiom_pos c (p, thf) =
  fprintf c "thf(pax%d,axiom,( p%d => " p p;
  fprintf_lfthf c thf;
  fprintf c ")).\n"

let fprintf_lfthf_axiom_neg c (p, thf) =
  fprintf c "thf(nax%d,axiom,( p%d <= " p p;
  fprintf_lfthf c thf;
  fprintf c ")).\n"

let fprintf_lfthf_matrix_types c =
  let m = Atom.max_atom () in
  for i = 1 to m
  do
    fprintf c "thf(p%d,type,( p%d : $o )).\n" i i;
  done

let fprintf_lfthf_const_types c =
  Hashtbl.iter (fun x i -> fprintf c "thf(f%s,type,( f%s : %s )).\n" x x (stp_str i)) lfth_consts 


let force_in_propmatrix : (int,unit) Hashtbl.t = Hashtbl.create 100
let omit_from_propmatrix : (Refut.clause,unit) Hashtbl.t = Hashtbl.create 100

let forced_into_propmatrix c =
  try
    ignore (List.find (fun n -> if n > 0 then Hashtbl.mem force_in_propmatrix n else Hashtbl.mem force_in_propmatrix (-n)) c);
    true
  with Not_found -> false

let force_into_propmatrix n =
  if n > 0 then
    Hashtbl.add force_in_propmatrix n ()
  else
    Hashtbl.add force_in_propmatrix (-n) ()

let clause_considered cl =
  forced_into_propmatrix cl ||
  not (Hashtbl.mem omit_from_propmatrix cl)

let filter_unnec_from_propmatrix pcore =
  List.iteri (fun axc cl ->
    if not (List.mem axc pcore)
    then Hashtbl.add omit_from_propmatrix cl ()
  ) (List.filter clause_considered !clauses)

let propmatrixh : (int,literal list) Hashtbl.t = Hashtbl.create 100;;

let fprintf_lfth_propclause c axc cl =
  assert (cl <> []);
  Hashtbl.add propmatrixh axc cl;
  let clstr = String.concat " | " (List.map plit_lfth_str cl) in
  Printf.fprintf c "thf(ax%d,axiom,( %s )).\n" axc clstr

let fprintf_lfth_propmatrix c =
  Hashtbl.clear propmatrixh;
  List.iteri (fprintf_lfth_propclause c) (List.filter clause_considered !clauses)


let fprintf_lfthf_axiom c (p, thf) =
  fprintf_lfthf_axiom_pos c (p, thf);
  fprintf_lfthf_axiom_neg c (p, thf)

let fprintf_lfth_problem c =
  fprintf_lfthf_const_types c;
  fprintf_lfthf_matrix_types c;
  (* Send all propositional clauses we've sent to MiniSat.
   * This contains the propositional structure of the problem. *)
  fprintf_lfth_propmatrix c;
  (* Relate propositional literals to LFTH formulas. *)
  List.iter (fprintf_lfthf_axiom c) (!lfth_forms)

let setup_fomapping () =
  eeqoequiv := get_bool_flag "E_EQO_EQUIV"
