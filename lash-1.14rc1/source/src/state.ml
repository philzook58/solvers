(* Lash *)
(* ported from Satallax file: *)
(* File: state.ml *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open String
open Flags
open Syntax
open Refut
open Log
open Error
open Minisat
open Ontology
open TermP

let minisat_tm = ref 0.0

exception CoqProofTooBig of int

let clauses : clause list ref = ref [];;

(*
Ftm.clausetable_make (1 lsl 20);;
let clausesTableO = Hashtbl.create (1 lsl 10);;
let clausesTable_add_wasthere c =
  let len = List.length c in
  if len <= 5 then Ftm.clausetable_add_wasthere len c
  else
    if Hashtbl.mem clausesTableO c then true else
    (Hashtbl.add clausesTableO c (); false);;
let clausesTable_clear () = Ftm.clausetable_clear (); Hashtbl.clear clausesTableO;;
 *)

let slaveargs = ref [Sys.argv.(0)];;
let mode : string list ref = ref []
let timeout : float option ref = ref None
let hardtimeout : float option ref = ref None
let nontheorem : bool ref = ref false (*** March 2012 - Know if you're explicitly trying to determine Satisfiable/CounterSatisfiable ***)
let coq = ref false
let coq2 = ref false
let problemfile = ref ""
let coqlocalfile = ref false
let coqglobalfile = ref false
let coqinchannel : in_channel ref = ref stdin
let coqoutchannel : out_channel ref = ref stdout
let coqinticks : ((out_channel -> unit) option * int) list ref = ref []
let coqoutfn1 = ref (fun c -> ())
let coqctx : (string option * pretrm option * pretrm option) list ref = ref []
let coqglobalsectionstack : (string * (out_channel -> unit) * (string option * pretrm option * pretrm option) list) list ref = ref []

let coqknown (x,y) =
  if (!coq2) then y else x

type probitem =
  | ProbDef of string * stp * trm * (string * string) list * float
  | ProbAx of string * string * trm * (string * string) list * float
  | ProbConj of string * trm * (string * string) list * float
let probitem_weight = function
    ProbDef(_,_,_,_,w) -> w
  | ProbAx (_,_,_,_,w) -> w
  | ProbConj (_,_,_,w) -> w
let probsig : probitem list ref = ref []

let rec updatecoqglobalsectionstack cx cgss co =
  match cgss with
  | ((secname,cfn,lcx)::cgss') -> ((secname,co cx cfn,lcx)::(updatecoqglobalsectionstack (List.append cx lcx) cgss' co))
  | [] -> []

let conjecturenames : string list ref = ref []
let conjecture : (ftm * ftm) list ref = ref []
type proofkind = TSTP | CoqScript | CoqSPfTerm | HOCore | Model | ModelTrue | IsarScript | PfInfo | PfUseful | PfFormdeps
let mkproofterm = ref None
let mkprooftermp () = match !mkproofterm with None -> false | _ -> true
let pfusefulout = ref None
let pfformdepsout = ref None
let slave = ref false
let coqsig_base : string list ref = ref []
let coqsig_const : (string * stp) list ref = ref []
let coqsig_def : (string * pretrm) list ref = ref []
let coqsig_def_trm : (string * trm) list ref = ref []
let coqsig_hyp : (string * pretrm) list ref = ref []
let coqsig_hyp_trm : (string * trm) list ref = ref []
let name_base : (string,unit) Hashtbl.t = Hashtbl.create 10
let name_base_list : int list ref = ref []
let name_tp : stp Vector.t = Vector.make 100 (-1)
let name_tp_f : (int,stp) Hashtbl.t = Hashtbl.create 100
let name_trm : (string,(trm * stp) * bool ref) Hashtbl.t = Hashtbl.create 100
let name_trm_f : (int,(ftm * stp) * bool ref) Hashtbl.t = Hashtbl.create 100
let name_trm_list : (int * ftm * stp) list ref = ref []
let translucent_defns : bool ref = ref false
let name_def_empty : (int,trm) Hashtbl.t = Hashtbl.create 1
let name_def_prenorm : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_def : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_def_f : (int,ftm) Hashtbl.t = Hashtbl.create 100
let name_def_all : (int,trm) Hashtbl.t = Hashtbl.create 100
let name_hyp : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_hyp_f : (string,ftm) Hashtbl.t = Hashtbl.create 100
let name_hyp_inv : (ftm,string) Hashtbl.t = Hashtbl.create 100 (*** associate a normalized/logic normalized term with the name of the assumption it came from and its original prenormalized form ***)
let assumption_lit : (int,ftm * ftm) Hashtbl.t = Hashtbl.create 100 (*** associate assumption literals with their term after preprocessing and before preprocessing ***)
let preprocess_ftm : (ftm,ftm) Hashtbl.t = Hashtbl.create 100 (*** associate ftm with preprocessed form, needed for proofs ***)

let mult_timeout f =
  match (!timeout) with
  | Some tm -> timeout := Some (tm *. f)
  | None -> ()

let requireSet0a () =
  let a = mk_base tyname_set in
  let b = PName "set" in
  Hashtbl.add coq_used_names "In" ();
  Hashtbl.add coq_used_names "Subq" ();
  Hashtbl.add coq_names "In" "In";
  Hashtbl.add coq_names "Subq" "Subq";
  coqsig_const := ("In",mk_ar a (mk_ar a mk_prop))::!coqsig_const;
  coqsig_const := ("Subq",mk_ar a (mk_ar a mk_prop))::!coqsig_const;
  coqsig_def := ("Subq",PLam([("x",b);("y",b)],PAll(["z",b],PAp(PAp(PImplies,PAp(PAp(PName "In",PName "z"),PName "x")),PAp(PAp(PName "In",PName "z"),PName "y")))))::!coqsig_def;
  coqsig_def_trm := ("Subq",Lam(a,Lam(a,Ap(Forall(a),Lam(a,Ap(Ap(Imp,Ap(Ap(Name("In",mk_ar a (mk_ar a mk_prop)),DB(0,a)),DB(2,a))),Ap(Ap(Name("In",mk_ar a (mk_ar a mk_prop)),DB(0,a)),DB(1,a))))))))::!coqsig_def_trm;
  ()

let required : string ref = ref ""

let require x =
  if (!verbosity > 5) then Printf.printf "Requiring %s\n" x;
  required := x;
  let f = !coqoutfn1 in
  begin
    coqoutfn1 := (fun c -> f c; Printf.fprintf c "Require Export %s.\n" x);
    match x with
    | "set0a" -> requireSet0a()
    | "set0" -> raise (GenericError "set0 is not yet supported.")
    | "set1" -> raise (GenericError "set1 is not yet supported.")
    | _ -> ()
  end

let declare_name_type x tp =
  let xn = name_no x in
  let trm = mk_name xn in
  Vector.set name_tp xn tp;
  Hashtbl.add name_tp_f xn (ty_f tp);
  Hashtbl.add name_trm x ((Name(x,tp),tp),ref false);
  Hashtbl.add name_trm_f xn ((trm, tp), ref false);
  name_trm_list := (xn, trm, tp)::!name_trm_list

(*** March 31, 2011 - Chad - THF policy regarding definitions. (See comments before declare_definition_real below. ***)
exception TreatAsAssumption

let next_fresh_name : int ref = ref 0

let rec get_fresh_name a =
  let x = make_fresh_name !next_fresh_name in
  let xn = name_no x in
  incr next_fresh_name;
  if !coq then ignore (coqify_name x coq_names coq_used_names);
  if ((Hashtbl.mem name_base x) || (Vector.get_default name_tp xn (-1) >= 0)) then
    get_fresh_name a
  else
    begin
      declare_name_type x a;
      (x, mk_name xn)
    end


let initial_branch : ftm list ref = ref []
let initial_branch_prenorm : trm list ref = ref [];;

Ftm.processed_make 1024;;
let clause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref = ref (Hashtbl.create 100)

let allclauses : clause list ref = ref [] (* allclauses is only used if formdeps is activated, in which case someone wants useless information. it contains all the clauses that were used in all searches across different subgoals; doesn't get reset. Aug 2016 *)
let allclause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref = ref (Hashtbl.create 100)

exception DuplicateClause

let insert_clause c r =
(*  if clausesTable_add_wasthere c then raise DuplicateClause;*)
(* Chad 2022: Removing clauses table and check for duplicates; careful below not to overwrite the rule info if it is a duplicate [and if a proof is requested] *)
(***  (Printf.printf "inserting search clause %s: %s\n" (List.fold_left (fun x y -> if ((String.length x) == 0) then (string_of_int y) else (x ^ " " ^ (string_of_int y))) "" c) (match r with (Some r) -> (ruleinfo_str r) | _ -> "None"); flush stdout); ***)
    (*** Chad: April 4, 2011: Check if the clause has already been added before.  If it has, raise DuplicateClause. (Otherwise, we may end up with bad rule info -- e.g., a later rule which will violate freshness) ***)
(*** Printf.printf "duplicate clause %s: %s\n%!" (List.fold_left (fun x y -> if ((String.length x) == 0) then (string_of_int y) else (x ^ " " ^ (string_of_int y))) "" c) (match r with (Some r) -> (ruleinfo_str r) | _ -> "None"); ***)
  (match !mkproofterm with Some _ -> clauses := c::!clauses | _ -> ());
  (match !mkproofterm with Some(PfFormdeps) -> allclauses := c::!allclauses | _ -> ());
  match r with
  | Some(r) ->
     if not (Hashtbl.mem (!clause_ruleinfo) c) then Hashtbl.add (!clause_ruleinfo) c r; (* Chad 2022: if clause is duplicate, do not overwrite the rule info *)
     (match !mkproofterm with Some(PfFormdeps) -> Hashtbl.add (!allclause_ruleinfo) c r | _ -> ())
  | None -> ()



let print_subproof_info minclauses cri =
  begin
    if (!verbosity > 0) then
      begin
	List.iter
	  (fun c ->
	    try
	      match (Hashtbl.find cri c) with
	      | InstRule(a,m,n) ->
		  begin
(***
		    match a with
		    | Ar(_,_) -> Printf.printf "HO Instantiation of type %s for\n%s:\n* %s\n" (stp_str a) (trm_str m) (trm_str n)
		    | _ -> () (*** Printf.printf "FO Instantiation of type %s for\n%s:\n* %s\n" (stp_str a) (trm_str m) (trm_str n) ***)
***)
		  end
	      | _ -> ()
	    with
	    | Not_found -> ())
	  minclauses;
      end
  end


let print_proof_statistics minclauses =
  let numassumptionclauses = ref 0 in
  let numsearchclauses = ref 0 in
  let assumptionlits = ref [] in
  let searchlits = Hashtbl.create 100 in
  List.iter
    (fun c ->
       if Hashtbl.mem (!clause_ruleinfo) c then
       begin
         incr numsearchclauses;
         List.iter (fun x -> if (not (Hashtbl.mem searchlits (abs x))) then Hashtbl.add searchlits (abs x) ()) c
       end
       else
       begin
         incr numassumptionclauses;
         match c with
         | [x] -> assumptionlits := ((abs x)::(!assumptionlits))
         | _ -> raise (GenericError "Assumption clause is not a unit clause?")
       end
    )
    minclauses;
  List.iter (Hashtbl.remove searchlits) (!assumptionlits);
  if (!verbosity > 3) then
  begin
    Printf.printf "Refutation Statistics:\n";
    Printf.printf "Number of assumptions %d\n" (!numassumptionclauses);
    Printf.printf "Number of search clauses %d\n" (!numsearchclauses);
    Printf.printf "Number of search literals %d\n" (Hashtbl.length searchlits);
  end


let new_assumption_lit l =
  try
    let c = [l] in
    insert_clause c None;
    if not (add_clauses c) || not (minisat_search_period ()) then
      raise (Unsatisfiable None)
  with
  | DuplicateClause -> ()
  | (Unsatisfiable _) ->
      if (!verbosity > 20) then Printf.printf "Proof found with assumption clauses only (no search)...%d clauses\n%!" (List.length (!clauses));
      if (mkprooftermp ()) then
	raise (Unsatisfiable (Some (fun () -> AssumptionConflictR(l))))
      else
	raise (Unsatisfiable None)

let new_search_clause c r =
  try
    insert_clause c r;
    if not (add_clauses c) || not (minisat_search_period ()) then
      raise (Unsatisfiable None);
  with
  | DuplicateClause -> ()
  | (Unsatisfiable _) ->
      if (!verbosity > 3) then Printf.printf "Proof found for a goal...%d clauses\n%!" (List.length !clauses);
      if (mkprooftermp ()) then
	let cri = !clause_ruleinfo in (*** remember the clauses and this hashtable for them ***)
(*** To test with minimal unsatisfiable core: ***)
	let minclauses = Unsatcore.minimal_unsatisfiable_core (!clauses) in
	if (!verbosity > 3) then Printf.printf "Reduced to %d clauses\n%!" (List.length minclauses);
(*** To test all clauses: ***)
(***	    let minclauses = !clauses in ***)
	print_subproof_info minclauses cri;
        if (!verbosity > 0) then print_proof_statistics minclauses;
	raise (Unsatisfiable (Some (fun () -> SearchR (minclauses, Hashtbl.find cri))))
      else
	raise (Unsatisfiable None)

let patoms : ((int * (ftm list)) list) Vector.t = Vector.make 10 []
let natoms : ((int * (ftm list)) list) Vector.t = Vector.make 10 []

let pchoiceatoms : ((int * (ftm list)) list) Vector.t = Vector.make 10 []
let nchoiceatoms : ((int * (ftm list)) list) Vector.t = Vector.make 10 []

let peqns : ((int * ftm * ftm) list) Vector.t = Vector.make 10 []
let neqns : ((int * ftm * ftm) list) Vector.t = Vector.make 10 []

let univpreds : ((int * ftm) list) Vector.t = Vector.make 10 []
let instantiations : (int * ftm,unit) Hashtbl.t = Hashtbl.create 10
let instantiationslist : (ftm list) Vector.t = Vector.make 10 []
let default_elts : (int,ftm) Hashtbl.t = Hashtbl.create 10

let set_default_elt ano x = Hashtbl.add default_elts ano x

let set_default_elt_if_needed a x =
  let a = ty_f_rev a in
  if is_base a then
    let ano = ty_get_no a in
    if (not (Hashtbl.mem default_elts ano)) then set_default_elt ano x

let default_elt ano =
  try
    Hashtbl.find default_elts ano
  with
  | Not_found ->
      let a = mk_base ano in
      let (_,x) = get_fresh_name a in
      begin
	set_default_elt ano x;
	x
      end

let default_elt_p ano =
  Hashtbl.mem default_elts ano

let get_instantiations a = Vector.get_default instantiationslist a [];;

let known_instantiation a k =
  Hashtbl.mem instantiations (a,k)

let cons_instantiation m ml =
    if (!fiINSTANTIATION_ORDER_CYCLE < 2) then
      begin
	if (!fiINSTANTIATION_ORDER_MASK mod 2 = 0) then
	  (m::ml)
	else
	  (ml @ [m])
      end
    else
      let j = List.length ml mod !fiINSTANTIATION_ORDER_CYCLE in
      begin
	if ((!fiINSTANTIATION_ORDER_MASK lsr j) mod 2 = 0) then
	  (m::ml)
	else
	  (ml @ [m])
      end

let add_instantiation_2 a m =
  Vector.update instantiationslist a (cons_instantiation m);;

let add_instantiation a m =
  if not (Hashtbl.mem instantiations (a,m)) then
    begin
      Hashtbl.replace instantiations (a,m) ();
      add_instantiation_2 a m;
      set_default_elt_if_needed a m
    end

let choiceopnames : (int,(stp * trm * trm)) Hashtbl.t = Hashtbl.create 10
let choiceopnames_f : (int,(int * ftm)) Hashtbl.t = Hashtbl.create 10

let choiceop_axiom m =
  match m with
  | Ap (Forall (ao),
	Lam (_,
	     Ap (Forall _,
		 Lam (_,
		      Ap (Ap (Imp, Ap (DB (1, _), DB (0, _))),
			  Ap (DB (1, _),
			      Ap (Name (x, _),
				  DB (1, _))))))))
    ->
     begin
       match ty_pred_over ao with
       | Some(a) -> Some(x,a)
       | None -> None
     end
  | Ap (Forall (ao),
	Lam (_,
	     Ap
	       (Ap (Imp,
		    Ap
		      (Ap (Imp,
			   Ap (Forall _,
			       Lam (_,
				    Ap (Ap (Imp, Ap (DB (1, _), DB (0, _))),
					False)))),
		       False)),
		Ap (DB (0, _),
		    Ap (Name (x, _),
			DB (0, _))))))
    ->
     begin
       match ty_pred_over ao with
       | Some(a) -> Some(x,a)
       | None -> None
     end
  | _ -> None

let fchoiceop_axiom m =
  match get_tag m with
  | FT_All ->
     let m1 = get_l m in
     begin
       match get_tag m1 with
       | FT_All ->
          let a2 = get_no m1 in
          let m2 = get_l m1 in
          begin
            match get_tag m2 with
            | FT_Imp ->
               let m3 = get_l m2 in
               let m4 = get_r m2 in
               begin
                 match get_tag m3,get_tag m4 with
                 | FT_Ap,FT_Ap ->
                    let m3a = get_l m3 in
                    let m3b = get_r m3 in
                    let m4a = get_l m4 in
                    let m4b = get_r m4 in
                    if ftm_db_p 1 m3a && ftm_db_p 0 m3b && ftm_db_p 1 m4a then
                      match get_tag m4b with
                      | FT_Ap ->
                         let m5 = get_l m4b in
                         let m6 = get_r m4b in
                         if ftm_db_p 1 m6 then
                           match get_tag m5 with
                           | FT_Name -> Some(get_no m5,ty_f_rev a2)
                           | _ -> None
                         else
                           None
                      | _ -> None
                    else
                      None
                 | _,_ -> None
               end
            | _ -> None
          end
       | FT_Imp ->
          let m1a = get_l m1 in
          let m1b = get_r m1 in
          begin
            match get_tag m1a with
            | FT_Imp ->
               if get_r m1a = mk_false then
                 let m2 = get_l m1a in
                 begin
                   match get_tag m2 with
                   | FT_All ->
                      let a2 = get_no m2 in
                      let m3 = get_l m2 in
                      begin
                        match get_tag m3 with
                        | FT_Imp ->
                           if get_r m3 = mk_false then
                             let m4 = get_l m3 in
                             begin
                               match get_tag m4,get_tag m1b with
                               | FT_Ap,FT_Ap ->
                                  if ftm_db_p 1 (get_l m4) && ftm_db_p 0 (get_r m4) && ftm_db_p 0 (get_l m1b) then
                                    let m5 = get_r m1b in
                                    begin
                                      match get_tag m5 with
                                      | FT_Ap ->
                                         let m6 = get_l m5 in
                                         let m7 = get_r m5 in
                                         if ftm_db_p 0 m7 then
                                           match get_tag m6 with
                                           | FT_Name -> Some(get_no m6,ty_f_rev a2)
                                           | _ -> None
                                         else
                                           None
                                      | _ -> None
                                    end
                                  else
                                    None
                               | _,_ -> None
                             end
                           else
                             None
                        | _ -> None
                      end
                   | _ -> None              
                 end
               else
                 None
            | _ -> None
          end
       | _ -> None
     end
  | _ -> None

let firrefbreln_axiom_real m =
  match get_tag m with
  | FT_All ->
     let a = get_no m in
     let m2 = get_l m in
     begin
       match get_tag m2 with
       | FT_Imp ->
          if get_r m2 = mk_false then
            begin
              let m3 = get_l m2 in
              match get_tag m3 with
              | FT_Ap ->
                 if ftm_db_p 0 (get_r m3) then
                   begin
                     let m3a = get_l m3 in
                     match get_tag m3a with
                     | FT_Ap ->
                        if ftm_db_p 0 (get_r m3a) then
                          let m3aa = get_l m3a in
                          begin
                            match get_tag m3aa with
                            | FT_Name -> Some(get_no m3aa,ty_f_rev a)
                            | _ -> None
                          end
                        else
                          None
                     | _ -> None
                   end
                 else
                   None
              | _ -> None
            end
          else
            None
       | _ -> None
     end
  | _ -> None

let fsymbreln_axiom_real m =
  match get_tag m with
  | FT_All ->
     let a1 = get_no m in
     let m1 = get_l m in
     begin
       match get_tag m1 with
       | FT_All ->
          let a2 = get_no m1 in
          let m2 = get_l m1 in
          if a1 = a2 then
            begin
              match get_tag m2 with
              | FT_Imp ->
                 let m3 = get_l m2 in
                 let m4 = get_r m2 in
                 begin
                   match get_tag m3,get_tag m4 with
                   | FT_Ap,FT_Ap ->
                      let m3a = get_l m3 in
                      let m3b = get_r m3 in
                      let m4a = get_l m4 in
                      let m4b = get_r m4 in
                      begin
                        match get_tag m3a,get_tag m4a with
                        | FT_Ap,FT_Ap ->
                           let m3aa = get_l m3a in
                           let m3ab = get_r m3a in
                           let m4aa = get_l m4a in
                           let m4ab = get_r m4a in
                           if m3aa = m4aa then
                             if ftm_db_p 0 m3ab && ftm_db_p 1 m3b && ftm_db_p 1 m4ab && ftm_db_p 0 m4b then
                               begin
                                 match get_tag m3aa with
                                 | FT_Name -> Some(get_no m3aa,ty_f_rev a1)
                                 | _ -> None
                               end
                             else if ftm_db_p 1 m3ab && ftm_db_p 0 m3b && ftm_db_p 0 m4ab && ftm_db_p 1 m4b then
                               begin
                                 match get_tag m3aa with
                                 | FT_Name -> Some(get_no m3aa,ty_f_rev a1)
                                 | _ -> None
                               end
                             else
                               None
                           else
                             None
                        | _,_ -> None
                      end
                   | _,_ -> None
                 end
              | _ -> None
            end
          else
            None
       | _ -> None
     end
  | _ -> None

let fimp_inv m =
  match get_tag m with
  | FT_Imp -> (get_l m,get_r m)
  | _ -> raise Not_found

let fneg_inv m =
  match get_tag m with
  | FT_Imp -> if get_r m = mk_false then get_l m else raise Not_found
  | _ -> raise Not_found

let fap_inv m =
  match get_tag m with
  | FT_Ap -> (get_l m,get_r m)
  | _ -> raise Not_found

let fdb_inv m =
  match get_tag m with
  | FT_DB -> get_no m
  | _ -> raise Not_found

let fname_inv m =
  match get_tag m with
  | FT_Name -> get_no m
  | _ -> raise Not_found

let feq_inv m =
  match get_tag m with
  | FT_Eq -> (get_no m,get_l m,get_r m)
  | _ -> raise Not_found

let fcov1breln_axiom_real m =
  match get_tag m with
  | FT_All ->
     let a1 = get_no m in
     let m1 = get_l m in
     begin
       match get_tag m1 with
       | FT_All ->
          let a2 = get_no m1 in
          let m2 = get_l m1 in
          if a1 = a2 then
            begin
              try
                let (m3,m4) = fimp_inv m2 in
                let m3n = fneg_inv m3 in
                try
                  let (_,u,v) = feq_inv m3n in
                  if not (fdb_inv u = 1 && fdb_inv v = 0) then raise Not_found;
                  let (m5,m6) = fimp_inv m4 in
                  let m5n = fneg_inv m5 in
                  let (m5a,m5b) = fap_inv m5n in
                  let (m5aa,m5ab) = fap_inv m5a in
                  if not (fdb_inv m5ab = 1 && fdb_inv m5b = 0) then raise Not_found;
                  let (m6a,m6b) = fap_inv m6 in
                  let (m6aa,m6ab) = fap_inv m6a in
                  if not (fdb_inv m6ab = 1 && fdb_inv m6b = 0) then raise Not_found;
                  let r = fname_inv m6aa in
                  let s = fname_inv m5aa in
                  Some(r,a1,s)
                with Not_found ->
                  let (m5,m6) = fimp_inv m3n in
                  let (m4a,m4b) = fap_inv m4 in
                  let (m4aa,m4ab) = fap_inv m4a in
                  let r = fname_inv m4aa in
                  let m5n = fneg_inv m5 in
                  let (_,u,v) = feq_inv m5n in
                  if not (fdb_inv u = 1 && fdb_inv v = 0) then raise Not_found;
                  let (m6a,m6b) = fap_inv m6 in
                  let (m6aa,m6ab) = fap_inv m6a in
                  if not (fdb_inv m6ab = 1 && fdb_inv m6b = 0) then raise Not_found;
                  let s = fname_inv m6aa in
                  Some(r,a1,s)
              with Not_found -> None
            end
          else
            None
       | _ -> None
     end
  | _ -> None

let fsymbreln_axiom m =
  if !fbDYNAMIC_SYMBRELN then
    fsymbreln_axiom_real m
  else
    None

let firrefbreln_axiom m =
  if !fbDYNAMIC_IRREFBRELN then
    firrefbreln_axiom_real m
  else
    None

let fcov1breln_axiom m =
  if !fbDYNAMIC_COV1BRELN then
    fcov1breln_axiom_real m
  else
    None

let fnocl1breln_axiom_real_4 n da =
  try
    for i = 0 to n-1 do
      if not da.(i) then raise Exit
    done;
    true
  with Exit -> false

let rec fnocl1breln_axiom_real_5 ls m a n r l extras =
  if m = mk_false then
    begin
      fnocl1breln_axiom_real_5b ls a n r l extras
    end
  else
    begin
      match get_tag m with
      | FT_Imp ->
         let m1 = get_l m in
         let m2 = get_r m in
         fnocl1breln_axiom_real_5 (m1::ls) m2 a n r l extras
      | _ -> raise Not_found
    end
and fnocl1breln_axiom_real_5a ls m a n r l extras =
  match get_tag m with
  | FT_Imp ->
     let m1 = get_l m in
     let m2 = get_r m in
     if m2 = mk_false then
       fnocl1breln_axiom_real_5 ls m1 a n r l extras
     else
       raise Not_found
  | _ ->
     let (m5a,m5b) = fap_inv m in
     let (m5aa,m5ab) = fap_inv m5a in
     if get_tag m5aa = FT_Name && get_no m5aa = r && get_tag m5ab = FT_DB && get_tag m5b = FT_DB then
       begin
         let i = get_no m5ab in
         let j = get_no m5b in
         fnocl1breln_axiom_real_5b ls a n r l ((i,j)::extras)
       end
     else
       raise Not_found
and fnocl1breln_axiom_real_5b ls a n r l extras =
  match ls with
  | (m::lr) ->
     fnocl1breln_axiom_real_5a lr m a n r l extras
  | [] ->
     (r,a,l,extras)

let rec fnocl1breln_axiom_real_3 ls m a n da r l =
  if m = mk_false then
    begin
      fnocl1breln_axiom_real_3b ls a n da r l
    end
  else
    begin
      match get_tag m with
      | FT_Imp ->
         let m1 = get_l m in
         let m2 = get_r m in
         fnocl1breln_axiom_real_3 (m1::ls) m2 a n da r l
      | _ -> raise Not_found
    end
and fnocl1breln_axiom_real_3a ls m a n da r l =
  match get_tag m with
  | FT_Imp ->
     let m1 = get_l m in
     let m2 = get_r m in
     if m2 = mk_false then
       fnocl1breln_axiom_real_3 ls m1 a n da r l
     else
       raise Not_found
  | _ ->
     let (m5a,m5b) = fap_inv m in
     let (m5aa,m5ab) = fap_inv m5a in
     if get_tag m5aa = FT_Name && get_no m5aa = r && get_tag m5ab = FT_DB && get_tag m5b = FT_DB then
       begin
         let i = get_no m5ab in
         let j = get_no m5b in
         da.(i) <- true;
         da.(j) <- true;
         if fnocl1breln_axiom_real_4 n da then
           fnocl1breln_axiom_real_5b ls a n r ((i,j)::l) []
         else if List.length l < 2 then
           fnocl1breln_axiom_real_3b ls a n da r ((i,j)::l)
         else
           raise Not_found
       end
     else
       raise Not_found
and fnocl1breln_axiom_real_3b ls a n da r l =
  fnocl1breln_axiom_real_3c ls [] a n da r l
and fnocl1breln_axiom_real_3c ls rr a n da r l =
  match ls with
  | (m::lr) ->
     begin
       let da2 = Array.copy da in
       try
         fnocl1breln_axiom_real_3a (rr @ lr) m a n da r l
       with Not_found ->
         fnocl1breln_axiom_real_3c lr (m::rr) a n da2 r l
     end
  | [] ->
     if rr = [] && fnocl1breln_axiom_real_4 n da then
       (r,a,l,[])
     else
       raise Not_found

let rec fnocl1breln_axiom_real_2 ls m a n da =
  if m = mk_false then
    fnocl1breln_axiom_real_2b ls a n da
  else
    begin
      match get_tag m with
      | FT_Imp ->
         let m1 = get_l m in
         let m2 = get_r m in
         fnocl1breln_axiom_real_2 (m1::ls) m2 a n da
      | _ -> raise Not_found
    end
and fnocl1breln_axiom_real_2a ls m a n da =
  match get_tag m with
  | FT_Imp ->
     let m1 = get_l m in
     let m2 = get_r m in
     if m2 = mk_false then
       fnocl1breln_axiom_real_2a ls m1 a n da
     else
       raise Not_found
  | _ ->
     let (m5a,m5b) = fap_inv m in
     let (m5aa,m5ab) = fap_inv m5a in
     if get_tag m5aa = FT_Name && get_tag m5ab = FT_DB && get_tag m5b = FT_DB then
       begin
         let i = get_no m5ab in
         let j = get_no m5b in
         da.(i) <- true;
         da.(j) <- true;
         fnocl1breln_axiom_real_3b ls a n da (get_no m5aa) [(i,j)]
       end
     else
       raise Not_found
and fnocl1breln_axiom_real_2b ls a n da =
  fnocl1breln_axiom_real_2c ls [] a n da
and fnocl1breln_axiom_real_2c ls rr a n da =
  match ls with
  | (m::lr) ->
     begin
       let da2 = Array.copy da in
       try
         fnocl1breln_axiom_real_2a (rr @ lr) m a n da
       with Not_found ->
         fnocl1breln_axiom_real_2c lr (m::rr) a n da2
     end
  | [] ->
     raise Not_found (** didn't find any r x y to start **)

let rec fnocl1breln_axiom_real_1 m a n =
  match get_tag m with
  | FT_All ->
     let a1 = get_no m in
     let m1 = get_l m in
     if a1 = a then
       fnocl1breln_axiom_real_1 m1 a (n+1)
     else
       raise Not_found
  | _ -> fnocl1breln_axiom_real_2 [] m a n (Array.make n false)

let fnocl1breln_axiom_real m =
  match get_tag m with
  | FT_All -> fnocl1breln_axiom_real_1 (get_l m) (get_no m) 1
  | _ -> raise Not_found
  
let fnocl1breln_axiom m =
  if !fbDYNAMIC_NOCL1BRELN then
    (try Some(fnocl1breln_axiom_real m) with Not_found -> None)
  else
    None

let declare_choiceop x a (m,mb) = Hashtbl.add choiceopnames x (a,m,mb)

let declare_fchoiceop x a m = Hashtbl.add choiceopnames_f x (a,m)

let minbrelnnames_f : (int,unit) Hashtbl.t = Hashtbl.create 10
let maxbrelnnames_f : (int,unit) Hashtbl.t = Hashtbl.create 10
let irrefbrelnnames_f : (int,(int * ftm)) Hashtbl.t = Hashtbl.create 10
let symbrelnnames_f : (int,(int * ftm)) Hashtbl.t = Hashtbl.create 10
let cov1brelnnames_f : (int,(int * int * ftm)) Hashtbl.t = Hashtbl.create 10
let nocl1brelnnames_f : (int,(int * (int * int) list * (int * int) list)) Hashtbl.t = Hashtbl.create 10

let declare_firrefbreln x a m = Hashtbl.add minbrelnnames_f x (); Hashtbl.add irrefbrelnnames_f x (a,m)
let declare_fsymbreln x a m = Hashtbl.add symbrelnnames_f x (a,m)
let declare_fcov1breln x a s m = Hashtbl.add maxbrelnnames_f x (); Hashtbl.add cov1brelnnames_f x (a,s,m)
let declare_fnocl1breln r a l extras = Hashtbl.add minbrelnnames_f r (); Hashtbl.add nocl1brelnnames_f r (a,l,extras)

let choiceop m =
  match m with
  | Choice(a) -> Some(a)
  | Name(x,_) ->
      begin
        let xn = name_no x in
	try
	  let (a,_,_) = Hashtbl.find choiceopnames xn in
	  Some(a)
	with
	| Not_found -> None
      end
  | _ -> None

let fchoiceop m =
  match get_tag m with
  | FT_Choice -> Some(get_no m)
  | FT_Name ->
      begin
	try
	  let (a,_) = Hashtbl.find choiceopnames_f (get_no m) in
	  Some(a)
	with
	| Not_found -> None
      end
  | _ -> None

let fsymbreln m =
  match get_tag m with
  | FT_Name ->
      begin
	try
	  let (a,_) = Hashtbl.find symbrelnnames_f (get_no m) in
	  Some(a)
	with
	| Not_found -> None
      end
  | _ -> None

let firrefbreln m =
  match get_tag m with
  | FT_Name ->
      begin
	try
	  let (a,_) = Hashtbl.find irrefbrelnnames_f (get_no m) in
	  Some(a)
	with
	| Not_found -> None
      end
  | _ -> None

let fcov1breln m =
  match get_tag m with
  | FT_Name ->
      begin
	try
	  let (a,s,_) = Hashtbl.find cov1brelnnames_f (get_no m) in
	  Some(a,s)
	with
	| Not_found -> None
      end
  | _ -> None

let fnocl1breln m =
  match get_tag m with
  | FT_Name ->
      begin
	try
	  let (a,l,extras) = Hashtbl.find nocl1brelnnames_f (get_no m) in
	  Some(a,l,extras)
	with
	| Not_found -> None
      end
  | _ -> None

let filtered = Vector.make 10 false;;

let part_of_conjecture : (ftm,unit) Hashtbl.t = Hashtbl.create 10

type namecategory =
    ChoiceOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary choice operator (in particular, tl[i] is this one) ***)
   | DescrOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary description operator (in particular, tl[i] is this one) ***)
   | IfThenElse of int * int * stp list (*** (i,n,sigmal) where length of sigmal is n, 0 <= i < n, Name has type o -> sigmal -> sigmal -> sigmal[i] ***)
   | ReflexiveBinary
   | IrreflexiveBinary
   | SymmetricBinary
   | ReflexiveSymmetricBinary
   | IrreflexiveSymmetricBinary

let constrainedName : (int,namecategory) Hashtbl.t = Hashtbl.create 10

let decomposable x =
   try
   let c = Hashtbl.find constrainedName x in (*** Some categorized names are decomposable and some are not ***)
   match c with
   | IfThenElse _ -> false (*** TO DO: Check that n-ary if-then-else need not be decomposable ***)
   (*** TO DO: Should *Binary cases be decomposable? ***)
   | _ -> true
   with Not_found -> true (*** A name is decomposable by default ***)

(*** only set this to true if the flag settings are sufficient to ensure that failure implies satisfiability ***)
let completep = ref false

let get_timeout_default x = match (!timeout) with Some y -> y | None -> x

let st_include_fun : (string -> unit) ref = ref (fun x -> raise (GenericError("Bug when including file " ^ x)))
let st_find_read_thf_fun : (string -> string -> unit) ref = ref (fun d x -> raise (GenericError("Bug when including file " ^ x)))

let declare_base_type a =
  if (!coq) then
    begin 
      let y = coqify_name a coq_names coq_used_names in
      coqsig_base := (y::!coqsig_base)
    end;
  let ano = basename_no a in
  Hashtbl.add name_base a ();
  name_base_list := (ano :: !name_base_list);
  if (get_bool_flag "CHOICE_AS_DEFAULT") then
    set_default_elt ano (trm_ftm name_def_f (ap(Choice (mk_base ano),Lam(mk_base ano,False))))

let st_to_stp m =
  begin
    try
      to_stp m
    with
    | DeclareInd ->
	begin (*** Declare the base type i the first time it's seen.  Use a different name if an 'i' has already been used. ***)
	  declare_base_type "$i";
	  to_stp m
	end
  end

let st_to_trm_given_stp m tp =
  begin
    try
      let (n,_) = to_trm name_trm [] m (Some tp) in n
    with
    | DeclareInd ->
	begin (*** Declare the base type i the first time it's seen.  Use a different name if an 'i' has already been used. ***)
	  declare_base_type "$i";
	  let (n,_) = to_trm name_trm [] m (Some tp) in n
	end
  end

let st_to_trm m =
  begin
    try
      to_trm name_trm [] m None
    with
    | DeclareInd ->
	begin (*** Declare the base type i the first time it's seen.  Use a different name if an 'i' has already been used. ***)
	  declare_base_type "$i";
	  to_trm name_trm [] m None
	end
  end



let declare_typed_constant (name:string) (role:string) (m:pretrm) (al:(string * string) list) =
  begin
    if (!verbosity > 4) then (Printf.printf "declare_typed_constant %s %s\n%s\n" name role (pretrm_str m); flush stdout);
    if (!verbosity > 20) then (Printf.printf "annotations:\n"; List.iter (fun (a,b) -> Printf.printf "%s: %s\n" a b) al; flush stdout);
    match m with
      POf(PName(x),m) ->
       let xn = name_no x in
	begin
	  match m with
	    PType -> (*** Actually unused. - April 20 2012 ***)
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Vector.get_default name_tp xn (-1) >= 0) then raise (Redeclaration x);
	      declare_base_type x
	  | PName "$type" -> (*** The case that's used. Added April 20 2012 ***)
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Vector.get_default name_tp xn (-1) >= 0) then raise (Redeclaration x);
	      declare_base_type x
	  | _ ->
	      let tp = st_to_stp m in
	      add_ontology_type x tp al;
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Vector.get_default name_tp xn (-1) >= 0) then raise (Redeclaration x);
	      if (!coq) then
		begin
		  let y = coqify_name x coq_names coq_used_names in
		  coqsig_const := (y,tp)::!coqsig_const
		end;
	      declare_name_type x tp;
              let xx = mk_name xn in
              Hashtbl.add name_trm_f xn ((xx,tp),ref false); (* LASH-TODO: what is the bool ref for? - Chad Jan 2022 *)
              name_trm_list := (xn,xx,tp)::!name_trm_list
	end
    | _ -> raise (GenericError ("Incorrect format for type declaration " ^ name))
  end

let rec init_probitem m =
  match m with
  | ProbDef(x,a,tm,al,w) ->
      begin
	try
	  if (get_bool_flag "ALL_DEFS_AS_EQNS") then
	    raise TreatAsAssumption
	  else
	    begin
	      if (!verbosity > 20) then Printf.printf "name_def %s %s\n" x (trm_str tm);
	      if true (* not (translucent_defn_p m) *) then (* LASH-TODO: reconsider Jan 2022 *)
	        begin
		  (* TODO: really set translucent definitions to true? *)
		  translucent_defns := true;
                  let xn = name_no x in
	          Hashtbl.add name_def_prenorm x tm;
(*	          (match !mkproofterm with (* June 2022: overall, pf construction works better with this commented out, in spite of the old comment on the next line *)
                   | Some _ ->  (* still needed for pf reconstruction *)
                      Hashtbl.add name_def x (norm name_def (logicnorm tm));
                   (*                      Hashtbl.add name_def x tm; (* questionable, but the previous version takes way too long on an example like NUM736^4.p *) *)
                   (*                      () *)
                   | _ -> ()); *)
                  let m = trm_ftm name_def_f tm in
	          Hashtbl.add name_def_f xn m
	        end
	  end
	with TreatAsAssumption ->
          let meq1 = Ap(Ap(Eq(a),Name(x,a)),tm) in
	  init_probitem (ProbAx(x,"hypothesis",meq1,al,w))
      end
  | ProbAx(name,role,tm1,al,w) ->
      begin
	let tmn = trm_ftm name_def_f tm1 in
	Hashtbl.add name_hyp_f name tmn;
	Hashtbl.add name_hyp_inv tmn name;
	if (!verbosity > 20) then Printf.printf "name_hyp %s %s\n" name (ftm_str tmn);
        initial_branch_prenorm := tm1::(!initial_branch_prenorm);
	initial_branch := tmn::(!initial_branch)
      end
  | ProbConj(name,tm1,al,w) ->
      begin
	conjecturenames := name::!conjecturenames;
        let ntm1 = normneg tm1 in
	let tmn = trm_ftm name_def_f tm1 in
	let ntmn = fneg tmn in
        initial_branch_prenorm := (ntm1::(!initial_branch_prenorm));
	if (!verbosity > 20) then Printf.printf "name_conj negated %s %s\n" name (ftm_str ntmn);
	initial_branch := (ntmn::(!initial_branch));
	conjecture := (tmn,ntmn)::!conjecture;
	Hashtbl.add part_of_conjecture ntmn ()
      end

let defpreweight m al = 2.0

let axpreweight m al =
  if ontology_prop_p m then 1.0 else 3.0

let conjpreweight m al = 0.0

(***
 THF official policy requires that all names are given a type before use,
 that definitions can be circular (in which case they must be treated as equations),
 and that definitions may appear *after* it's already been used in an assumption.
 In order to comply with this policy *and* do something reasonable in the 'usual' case,
 I do the following:

 1. I keep a hashtable (occurred_names) of typed names that have been used in an assumption.
 2. When I encounter a definition, if it's of the form (x = t), I first parse t.  If x has been used,
    then I include the equation as an axiom.  Otherwise, x is treated as a definition and expanded away.

 NOTE: If I wanted to be strict, I would exit if the definition is given without the name being given a type,
 but I will not require the type to be given.  I will print a warning if the verbosity is > 0.
 ***)
let declare_definition_real x (m:pretrm) al =
  if (Hashtbl.mem name_base x) then raise (Redeclaration x);
  let xn = name_no x in
  if (Hashtbl.mem name_def_f xn) then raise TreatAsAssumption; (*** treat it as an assumption per THF policy. - Mar 31, 2011 - Chad ***)
(*** raise (Redeclaration x); ***)
  let tp = Vector.get_default name_tp xn (-1) in
  if tp >= 0 then begin
     let tm1 = st_to_trm_given_stp m tp in
     try
       let (_,r) = Hashtbl.find name_trm_f xn in
       if (!r) then
	 raise TreatAsAssumption (*** It's already been used, treat 'definition' as an assumption. ***)
       else
	 raise Not_found
     with
     | Not_found ->
	begin
          (*	  add_ontology_term x tm; *)
	  let w = defpreweight tm1 al in
	  probsig := ProbDef(x,tp,tm1,al,w)::!probsig
	end
  end else
      begin (*** Giving a definition without giving it's type isn't allowed in THF anymore.  I'm still allowing it.  ***)
	if ((!verbosity > 0) && (not (!coqglobalfile)) && (not (!coqlocalfile))) then Printf.printf "WARNING: %s defined without giving type first.\n" x;
	let (tm1,tp) = st_to_trm m in
	declare_name_type x tp;
	let w = defpreweight tm1 al in
	probsig := ProbDef(x,tp,tm1,al,w)::!probsig
      end

let rec declare_thf_logic_formula (name:string) (role:string) (m:pretrm) (al:(string * string) list) =
  begin
    if !verbosity > 4 then (Printf.printf "declare_thf_logic_formula %s %s\n" name role; flush stdout);
    if (!verbosity > 20) then (Printf.printf "annotations:\n"; List.iter (fun (a,b) -> Printf.printf "%s: %s\n" a b) al; flush stdout);
    if ((role = "axiom") || (role = "hypothesis") || (role = "assumption") || (role = "lemma") || (role = "theorem") || (role = "corollary")) then
      begin
	if (Hashtbl.mem name_hyp name) then raise (Redeclaration name);
	let tm1 = st_to_trm_given_stp m mk_prop in
	let w = axpreweight tm1 al in
	probsig := ProbAx(name,role,tm1,al,w)::!probsig
      end
    else if (role = "conjecture") then
      begin
	let tm1 = st_to_trm_given_stp m mk_prop in
	let w = conjpreweight tm1 al in
	probsig := ProbConj(name,tm1,al,w)::!probsig
      end
    else
      raise (GenericError ("Unknown role " ^ role))
  end

let declare_definition (name:string) (role:string) (m:pretrm) (al:(string * string) list) =
  try
    begin
      if (get_bool_flag "ALL_DEFS_AS_EQNS") then raise TreatAsAssumption;
      if !verbosity > 4 then (Printf.printf "declare_definition %s %s\n" name role; flush stdout);
      if (!verbosity > 20) then (Printf.printf "annotations:\n"; List.iter (fun (a,b) -> Printf.printf "%s: %s\n" a b) al; flush stdout);
      match m with
	PDef(PName(x),m) -> (*** No longer THF syntax. ***)
	  declare_definition_real x m al
      | PAp(PAp(PEq,PName(x)),m) ->
	  declare_definition_real x m al
      | _ -> (*** Treat as an assumption, no matter how it looks. Odd, but OK. This may be too liberal; we haven't decided yet. ***)
	  raise TreatAsAssumption
(*** raise (GenericError ("Incorrect format for definition " ^ name)) ***)
    end
  with
  | TreatAsAssumption ->
      declare_thf_logic_formula name "hypothesis" m al

(*** Code for enumeration of types and terms - Dec 10, 2010 - Chad ***)
let enum_of_started_ : (int,unit) Hashtbl.t = Hashtbl.create 5
let enum_of_started a =
  Hashtbl.mem enum_of_started_ a
let enum_of_start a =
  Hashtbl.add enum_of_started_ a ()
let usableTypes_rtp : ((stp * int) list) Vector.t = Vector.make 5 []
let usableHeads_rtp : ((stp list * ftm * int) list) Vector.t = Vector.make 5 []

let new_usable_type_rtp ar a d =
  Vector.update usableTypes_rtp ar (fun ut -> (a,d) :: ut)

let usable_types_rtp ar = Vector.get_default usableTypes_rtp ar []

let new_usable_head_rtp ar sigmal m n =
  Vector.update usableHeads_rtp ar (fun uh -> (sigmal,m,n) :: uh)

let usable_heads_rtp ar = Vector.get_default usableHeads_rtp ar []

(*** search init ***)
let search_init () =
  (*** Add initial instantiations: true and false for o ***)
  let o = ty_f mk_prop in
  add_instantiation o mk_false;
  add_instantiation o (mk_neg mk_false)
  
(*** reset search ***)
let reset_search () =
  begin
    (*    clausesTable_clear (); *)
    clauses := [];
    clause_ruleinfo := Hashtbl.create 100;
    Searchoption.reset_pqueues ();
    Vector.clear patoms;
    Vector.clear natoms;
    Vector.clear pchoiceatoms;
    Vector.clear nchoiceatoms;
    Vector.clear peqns;
    Vector.clear neqns;
    Vector.clear univpreds;
    Hashtbl.clear instantiations;
    Ftm.processed_clear ();
    Hashtbl.clear enum_of_started_;
    Vector.clear usableTypes_rtp;
    Vector.clear usableHeads_rtp;
    Hashtbl.clear choiceopnames;
    Hashtbl.clear choiceopnames_f;
    Hashtbl.clear irrefbrelnnames_f;
    Hashtbl.clear symbrelnnames_f;
    Hashtbl.clear cov1brelnnames_f;
    Vector.clear filtered;
    search_init()
  end

let print_branch =
  List.iteri (fun i m -> Printf.printf "%d %s\n" (i+1) (ftm_str m))

(* select_list l [i1; ...; in] = [nth l in; ...; nth l i1] *)
let select_list (l:ftm list) : int list -> ftm list = List.rev_map (List.nth l)

let select_axioms_list : int list ref = ref [];;

let select_axioms () =
  (*** I should select the prenorm branch too, but that's only needed for proof reconstruction. ***)
  initial_branch := select_list !initial_branch !select_axioms_list;
  if (!verbosity > 4) then
    begin
      print_endline "Initial branch after selection:";
      print_branch !initial_branch
    end

let num_axioms () = List.length (!initial_branch)
