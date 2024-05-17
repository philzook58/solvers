open Atom
open Foform
open Eproverstate (* TODO: move this to fomapping.ml *)
open Flags
open Log
open State
open Syntax

let eeqoequiv = ref false

(*** Remember if a is FO, so I can send this to E. Send it to E every E_PERIOD times. ***)
let new_possible_fo_formula_1 m a f =
  match trm_to_foform_stp m (!eeqoequiv) with
  | (fof,Some b) ->
      if (not (Hashtbl.mem fo_types_h b)) then
	begin
	  if (!verbosity > 4) then (Printf.printf "New FO type: %s\n" (stp_str b); flush stdout);
	  Hashtbl.add fo_types_h b ();
	  fo_types := b::!fo_types;
	  Hashtbl.add fo_ecounter b (ref 0);
	end;
      if (!verbosity > 4) then (Printf.printf "Adding FOF for type %s: %s\n" (stp_str b) (trm_str m); flush stdout);
      if a > 0 then
	(Hashtbl.add stp_fo_forms b (a,fof); Hashtbl.add atom_fof a fof)
      else
        (Hashtbl.add stp_fo_forms b (-a,foneg fof); Hashtbl.add atom_fof (-a) fof); (*** shouldn't happen, but just in case ***)
      f b;
      fof
  | (fof,None) ->
      if (!verbosity > 4) then (Printf.printf "Adding prop FOF: %s\n" (trm_str m); flush stdout);
      if a > 0 then
	(prop_fo_forms := ((a,fof)::!prop_fo_forms); Hashtbl.add atom_fof a fof)
      else
	(prop_fo_forms := ((-a,foneg fof)::!prop_fo_forms); Hashtbl.add atom_fof a fof); (*** shouldn't happen, but just in case ***)
      fof

let get_fof a s =
  try
    if a > 0 then
      Hashtbl.find atom_fof a
    else
      FOImp(Hashtbl.find atom_fof (-a),FOFal)
  with Not_found ->
    new_possible_fo_formula_1 s a (fun b -> ())
      
let plit_fo_str a =
  if a > 0 then
    "p" ^ (string_of_int a)
  else
    "~ p" ^ (string_of_int (- a))


let rec printf_fof_neg_alls s m =
  match m with
  | FOAll(x,m1) ->
      Printf.fprintf s "( ? [%s] : " x;
      printf_fof_neg_alls s m1;
      Printf.fprintf s ")"
  | _ ->
      Printf.fprintf s "(~ ";
      printf_fof s m;
      Printf.fprintf s ")"

let printf_fof_pol_ax s p m =
  if p > 0 then
    let fof = get_fof p m in
    begin
      Printf.fprintf s "fof(pax%d,axiom,( p%d => " p p;
      printf_fof s fof;
      Printf.fprintf s ")).\n";
    end
  else
    let fof = get_fof (-p) (normneg m) in
    begin
      Printf.fprintf s "fof(nax%d,axiom,( p%d <= " (-p) (-p);
      printf_fof s fof;
      Printf.fprintf s ")).\n";
    end

let printf_fof_question s n m =
  let fof = get_fof n m in
  Printf.fprintf s "fof(q,question,";
  printf_fof_neg_alls s fof;
  Printf.fprintf s ").\n"

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

let filter_unnec_from_propmatrix pcore =
  let axc = ref 0 in
  List.iter
    (fun c ->
      if forced_into_propmatrix c || not (Hashtbl.mem omit_from_propmatrix c) then
	begin
	  incr axc;
	  if not (List.mem !axc pcore) then Hashtbl.add omit_from_propmatrix c ()
	end
      )
    !clauses

let propmatrixh : (int,literal list) Hashtbl.t = Hashtbl.create 100;;

let printf_fof_file_propmatrix s =
  Hashtbl.clear propmatrixh;
  let axc = ref 0 in
  List.iter (fun c ->
    match c with
    | (l1::ll) ->
	if forced_into_propmatrix c || not (Hashtbl.mem omit_from_propmatrix c) then
	  begin
	    incr axc;
	    Hashtbl.add propmatrixh !axc (l1::ll);
	    Printf.fprintf s "fof(ax%d,axiom,( %s " (!axc) (plit_fo_str l1);
	    List.iter (fun l2 -> Printf.fprintf s " | %s" (plit_fo_str l2)) ll;
	    Printf.fprintf s ")).\n"
	  end
    | [] -> () (*** should never happen ***)
	  )
    !clauses

let printf_fof_file s b =
	   (*** Send all propositional clauses we've sent to MiniSat. This contains the propositional structure of the problem. ***)
  printf_fof_file_propmatrix s;
	   (*** Relate Some propositional literals to first order formulas. ***)
	   (*** First the ones that are really propositional. ***)
           (*** Mar 2016: Split equivalences into two implications, so the proof gives more information to help with reconstruction. ***)
  (* TODO: remove code duplication below *)
  List.iter (fun (p,fof) ->
    Printf.fprintf s "fof(pax%d,axiom,( p%d => " p p;
    printf_fof s fof;
    Printf.fprintf s ")).\n";
    Printf.fprintf s "fof(nax%d,axiom,( p%d <= " p p;
    printf_fof s fof;
    Printf.fprintf s ")).\n";
      )
    (!prop_fo_forms);
	   (*** Finally the ones that are specifically viewed as first order via the current type b. ***)
           (*** Mar 2016: Split equivalences into two implications, so the proof gives more information to help with reconstruction. ***)
  List.iter (fun (p,fof) ->
    Printf.fprintf s "fof(pax%d,axiom,( p%d => " p p;
    printf_fof s fof;
    Printf.fprintf s ")).\n";
    Printf.fprintf s "fof(nax%d,axiom,( p%d <= " p p;
    printf_fof s fof;
    Printf.fprintf s ")).\n";
    )
    (Hashtbl.find_all stp_fo_forms b)

(*** Output FOF as Sexpr -- just for debugging BEGIN ***)
let printf_fs_file s b =
  let axc = ref 0 in
	   (*** Send all propositional clauses we've sent to MiniSat. This contains the propositional structure of the problem. ***)
  List.iter (fun c ->
    match c with
    | (l1::ll) ->
	incr axc;
	Printf.fprintf s "(AXIOM %d (|%s|" (!axc) (plit_fo_str l1);
	List.iter (fun l2 -> Printf.fprintf s " |%s|" (plit_fo_str l2)) ll;
	Printf.fprintf s "))\n";
    | [] -> () (*** should never happen ***)
	  )
    !clauses;
	   (*** Relate Some propositional literals to first order formulas. ***)
	   (*** First the ones that are really propositional. ***)
  List.iter (fun (p,fof) ->
    incr axc;
    Printf.fprintf s "(EAXIOM %d |%s| " (!axc) (plit_fo_str p);
    printf_fs s fof;
    Printf.fprintf s ")\n"
      )
    (!prop_fo_forms);
	   (*** Finally the ones that are specifically viewed as first order via the current type b. ***)
  List.iter (fun (p,fof) ->
    incr axc;
    Printf.fprintf s "(EAXIOM %d |%s| " (!axc) (plit_fo_str p);
    printf_fs s fof;
    Printf.fprintf s ")\n"
      )
    (Hashtbl.find_all stp_fo_forms b)
(*** Output FOF as Sexpr -- just for debugging END ***)

let setup_fomapping () =
  eeqoequiv := get_bool_flag "E_EQO_EQUIV"
