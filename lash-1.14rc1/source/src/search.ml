(* Lash *)
(* ported from Satallax file: *)
(* File: search.ml *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open Flags
open State
open Syntax
open Minisat
open Minisatinterface
open Refut
open Atom
open Log
open Searchoption
open Error

let nocl1brelnnames_partial : (int,(int * (int * int) list * (int * ftm) list * int list * (int * int) list * ftm list)) Hashtbl.t = Hashtbl.create 10

let enable_pattern_clauses = ref false;;
let dynamic_pattern_clauses = ref false;;
let apply_pattern_clauses_early = ref false;;

let filterp lit =
  if (!verbosity > 8) then Printf.printf "trying to filter %d\n" lit;
  if (minisat_search1 lit) then
    begin
      if (!verbosity > 8) then Printf.printf "Not filtering %d\n" lit;
      false
    end
  else
    begin
      if (!verbosity > 8) then Printf.printf "Filtering %d\n" lit;
      true
    end

let lit2nat i = if i < 0 then 2 * (-i) + 1 else 2 * i;;
let filteredp lit = Vector.get_default filtered (lit2nat lit) false;;

let filter lit =
  if (not (filteredp lit)) then
    if (filterp lit) then
      Vector.set filtered (lit2nat lit) true (*** The literal cannot be true. ***)

let filterneg lit = filter (- lit)

let pattern_clauses_transitivity_types : (stp,unit) Hashtbl.t = Hashtbl.create 10

let not_in_prop_model_delay_p : bool ref = ref false (*** Nov 2011 ***)
let not_in_prop_model_delay : int ref = ref 0        (*** Nov 2011 ***)




let get_literal_fn1 : (ftm -> int) ref = ref get_literal
let get_literal_fn2 : (ftm -> int) ref = ref get_literal

(*** Dec 2012: Make pattern clauses when the formula is assigned a literal. ***)
                                         (*
let get_literal_and_make_pattern_clause m =
  match m with
  | (Ap(Forall(_),_)) ->
      if assignedp m then
	get_literal m
      else
	let l = get_literal m in
	new_pattern_clauses l m;
	l
  | _ -> get_literal m
                                          *)
                                         
let nonforall_pattern_clauses_usable : bool ref = ref false

(*** Nov 2015: In addition to making the pattern clause when the minisat literal is created, apply it to the pattern clauses that already exist. ***)
                                                (*
let get_literal_and_make_and_apply_pattern_clause m =
  match m with
  | (Ap(Forall(_),_)) ->
      if assignedp m then
	get_literal m
      else
	let l = get_literal m in
	new_pattern_clauses l m;
	apply_pattern_clauses l m;
	l
  | _ ->
      if !nonforall_pattern_clauses_usable then
	let l = get_literal m in
	apply_pattern_clauses l m;
	l
      else
	get_literal m

let rec irrelevant_choice_p m =
  match m with
  | Ap(Choice(_),Lam(_,m1)) when (termNotFreeIn m1 0) -> true
  | Lam(_,m1) -> irrelevant_choice_p m1
  | Ap(m1,m2) -> irrelevant_choice_p m1 || irrelevant_choice_p m2
  | _ -> false

let rec reflexivity_used_p m =
  match m with
  | Ap(Ap(Eq(_),m1),m2) when m1 = m2 -> true
  | Lam(_,m1) -> reflexivity_used_p m1
  | Ap(m1,m2) -> (reflexivity_used_p m1) || (reflexivity_used_p m2)
  | _ -> false

let insane_instance_p m = (irrelevant_choice_p m) || (reflexivity_used_p m)
                                                 *)
                                                
let sym_eq_clauses_1 mlit msymlit a m1 m2 =
  new_search_clause [(-mlit);msymlit] (if (mkprooftermp ()) then (Some (Known(mlit,"symeq",[]))) else None)

let sym_eq_clauses mlit a m1 m2 =
  let msym = mk_norm_eq a m2 m1 in
  let msymlit = get_literal msym in
  sym_eq_clauses_1 mlit msymlit a m1 m2;
  sym_eq_clauses_1 msymlit mlit a m2 m1

let seen_instantiations : ((int * ftm),unit) Hashtbl.t = Hashtbl.create 10

let seen_inst_p a m =
  Hashtbl.mem seen_instantiations (a,m)

let see_inst a m =
  Hashtbl.add seen_instantiations (a,m) ()

let reset_search_1 () =
  reset_search();
  Hashtbl.clear seen_instantiations

(**
let rec extend_model fr interp p =
  match search_interp_extensions_val p unit_big_int (fr,interp) 1 with
  | [] -> (*** leave it unchanged ***)
      interp
  | (_,interp2)::_ -> (*** possibly updated interpretation interpreting more names (not changing interp of already interpreted names) ***)
      interp2

let extend_models p =
  if !verbosity > 5 then (Printf.printf "extend_models %s\n" (trm_str p); flush stdout);
  let u r = r := List.map (fun ((fr,interp),h) -> ((fr,extend_model fr interp p),h)) !r in
  u current_interp_2s_1;
  u current_interp_2s_2;
  u current_interp_2s_4;
  if !verbosity > 20 then
    begin
      Printf.printf "After trying to extend models of %s:\n" (trm_str p);
      Printf.printf "Interps over 1 elt frame (%d):\n" (List.length !current_interp_2s_1);
      List.iter (fun ((fr,inter),_) -> print_interp_trm_info p (fr,inter)) !current_interp_2s_1;
      Printf.printf "Interps over 2 elt frame (%d):\n" (List.length !current_interp_2s_2);
      List.iter (fun ((fr,inter),_) -> print_interp_trm_info p (fr,inter)) !current_interp_2s_2;
      Printf.printf "Interps over 4 elt frame (%d):\n" (List.length !current_interp_2s_4);
      List.iter (fun ((fr,inter),_) -> print_interp_trm_info p (fr,inter)) !current_interp_2s_4;
    end

let rec gen_models_a fr p n =
  List.map (fun z -> (z,Hashtbl.create 100)) (search_interp_extensions_val p unit_big_int (fr,empty_name_interp) n)

let gen_models p =
  if !verbosity > 5 then (Printf.printf "gen_models %s\n" (trm_str p); flush stdout);
  (*** first try to extend current interpretations ***)
  extend_models p;
  (*** then try to create more ***)
  let n = get_int_flag "MAX_INTERPS_PER_AXIOM" in
  let u fr r = r := gen_models_a fr p n @ !r in
  u fr1 current_interp_2s_1;
  u fr2 current_interp_2s_2;
  u fr4 current_interp_2s_4;
  if !verbosity > 20 then
    begin
      Printf.printf "After trying to generate models of %s:\n" (trm_str p);
      Printf.printf "Interps over 1 elt frame (%d):\n" (List.length !current_interp_2s_1);
      List.iter (fun ((fr,inter),h) -> print_interp_trm_info p (fr,inter)) !current_interp_2s_1;
      Printf.printf "Interps over 2 elt frame (%d):\n" (List.length !current_interp_2s_2);
      List.iter (fun ((fr,inter),h) -> print_interp_trm_info p (fr,inter)) !current_interp_2s_2;
      Printf.printf "Interps over 4 elt frame (%d):\n" (List.length !current_interp_2s_4);
      List.iter (fun ((fr,inter),h) -> print_interp_trm_info p (fr,inter)) !current_interp_2s_4;
    end
 **)

let rec stp_weight a =
  if is_ar a then
    (get_int_flag "ARTP_WEIGHT") + (stp_weight (ty_get_l a)) + (stp_weight (ty_get_r a))
  else if is_base a then
    get_int_flag "BASETP_WEIGHT"
  else
    get_int_flag "OTP_WEIGHT"

let rec tm_weight m =
  match get_tag m with
  | FT_None -> 0
  | FT_DB -> get_int_flag "DB_WEIGHT"
  | FT_Name -> get_int_flag "NAME_WEIGHT"
  | FT_Ap -> (get_int_flag "AP_WEIGHT") + (tm_weight (get_l m)) + (tm_weight (get_r m))
  | FT_Lam ->
    let fac = get_int_flag "LAM_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "LAM_WEIGHT") + (fac * (stp_weight (get_no m))) + (tm_weight (get_l m))
      else
	(get_int_flag "LAM_WEIGHT") + (tm_weight (get_l m))
    end
  | FT_False -> (get_int_flag "FALSE_WEIGHT")
  | FT_Imp -> (get_int_flag "IMP_WEIGHT")
  | FT_All ->
    let fac = get_int_flag "FORALL_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "FORALL_WEIGHT") + (fac * (stp_weight (get_no m)))
      else
	(get_int_flag "FORALL_WEIGHT")
    end
  | FT_Choice ->
     let fac = get_int_flag "CHOICE_TP_WEIGHT_FAC" in
     begin
       if (fac > 0) then
	 (get_int_flag "CHOICE_WEIGHT") + (fac * (stp_weight (get_no m)))
       else
	 (get_int_flag "CHOICE_WEIGHT")
     end
  | FT_Eq ->
    let fac = get_int_flag "EQ_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "EQ_WEIGHT") + (fac * (stp_weight (get_no m)))
      else
	(get_int_flag "EQ_WEIGHT")
    end

let instantiation_priority a m =
  !fiINSTANTIATION_DELAY + (stp_weight a) + (tm_weight m)

let process_instantiation a m =
  (*** Process it now -- making it passive ***)
  if (!verbosity > 5) then (Printf.printf "Instantiating with %s\n" (ftm_str m));
  add_instantiation a m;
  let iter_fun_pi (lit,p) = (*** Instantiate known universal predicates ***)
    if not (filteredp (-lit)) then
      let pm = mk_norm_ap p m in
      insertWithPriority !fiFORALL_DELAY (ProcessProp1 pm);
      let pmlit = !get_literal_fn2 pm in
      new_search_clause [lit;pmlit]
	(if (mkprooftermp ()) then (Some(InstRule(a,p,m))) else None)
  in
  List.iter iter_fun_pi (Vector.get_default univpreds a [])

let new_active_instantiation a m =
  if !fbEAGERLY_PROCESS_INSTANTIATIONS then (*** Process it now -- making it passive ***)
    process_instantiation a m
  else (*** Determine priority and put it on the queue (active instantiation) ***)
    let d = instantiation_priority a m in
    begin
      if (!verbosity > 20) then (Printf.printf "Delaying with priority %d active instantiation %s\n" d (ftm_str m));
      insertWithPriority d (NewInst(a,m))
    end

let possibly_new_instantiation (a:int) (m:ftm) =
  if (not (seen_inst_p a m)) then
(*    let um = get_bool_flag "USE_MODELS" in
    let dsei = get_int_flag "DELAY_SEMANTIC_EQUIV_INSTANTIATION" in
    if (um && dsei > 0 && not (current_interp_2s() = [])) then (*** if there are no current interps, then all instantiations would look equivalent, skip this case ***)
      begin
	let oldness = ref 0 in
	let unknownness = ref 0 in
	let vl = ref [] in
	List.iter
	  (fun ((fr,inter),h) ->
	    try
	      let v = string_of_big_int (eval_interp_2 (fr,default_to_zero inter) [] m) in
	      vl := v::!vl;
	      if Hashtbl.mem h v then
		incr oldness
	      else
		Hashtbl.add h v ()
	    with exc ->
	      vl := Printexc.to_string exc::!vl;
	      incr unknownness)
	  (current_interp_2s());
	let semdelay = dsei * !oldness in
	if semdelay > 0 then
          begin
            if (!verbosity > 5) then (Printf.printf "Delaying instantiation %d due to semantic equiv %s:" semdelay (ftm_str m); List.iter (fun v -> Printf.printf " %s" v) !vl; Printf.printf "\n");
            insertWithPriority semdelay (NewInst(ty_f a,m))
          end
        else
          begin
            if (!verbosity > 5) then (Printf.printf "Instantiation with new semantic equiv class %s:" (ftm_str m); List.iter (fun v -> Printf.printf " %s" v) !vl; Printf.printf "\n");
            see_inst a m;
            new_active_instantiation a m
          end
      end
    else *)
      begin
	if !verbosity > 5 then (Printf.printf "New instantiation: %s\n" (ftm_str m); Printf.printf "of type %s\n" (stp_str (ty_f_rev a)); flush stdout);
        see_inst a m;
        new_active_instantiation a m;
      end
  else if (!verbosity > 5) then
    Printf.printf "not really new inst %s\n" (ftm_str m)
  
let process_new_name a (m:ftm) d =
  let (sigmal,ar) = argtps_rtp (ty_f_rev a) in
  new_usable_head_rtp ar sigmal m d

let process_new_type ar a d =
  new_usable_type_rtp ar a d

let negimp_rule mlit m m1 m2 =
  let r = if (mkprooftermp ()) then (Some(NegPropRule(m))) else None in
  insertWithPriority !fiPOST_NOR_L_DELAY (ProcessProp1 m1);
  insertWithPriority !fiPOST_NOR_R_DELAY (ProcessProp1 (fneg m2));
  let m1lit = !get_literal_fn2 m1 in
  let nm2lit = !get_literal_fn2 (fneg m2) in
  new_search_clause [-mlit;m1lit] r;
  new_search_clause [-mlit;nm2lit] r

let imp_rule mlit m m1 m2 =
  let r = if (mkprooftermp ()) then (Some(PosPropRule(m))) else None in
  insertWithPriority !fiPOST_OR_L_DELAY (ProcessProp1 (fneg m1));
  insertWithPriority !fiPOST_OR_R_DELAY (ProcessProp1 m2);
  let nm1lit = !get_literal_fn2 (fneg m1) in
  let m2lit = !get_literal_fn2 m2 in
  new_search_clause [(-mlit);nm1lit;m2lit] r

(*
let rec replace_subterms f m =
  let n =
    match get_tag m with
    | FT_Ap ->
       let m1 = get_l m in
       let m2 = get_r m in
       mk_norm_ap (replace_subterms f m1) (replace_subterms f m2)
    | FT_Imp ->
       let m1 = get_l m in
       let m2 = get_r m in
       mk_norm_imp (replace_subterms f m1) (replace_subterms f m2)
    | FT_Lam ->
       let a = get_no m in
       let m1 = get_l m in
       mk_norm_lam a (replace_subterms f m1)
    | FT_All ->
       let a = get_no m in
       let m1 = get_l m in
       mk_all a (replace_subterms f m1)
    | FT_Eq ->
       let a = get_no m in
       let m1 = get_l m in
       let m2 = get_r m in
       mk_norm_eq a (replace_subterms f m1) (replace_subterms f m2)
    | _ -> m
  in
  match f n with
  | Some(n2) -> n2
  | None -> n
*)

let forall_rule nmlit a m1 w =
  if (!verbosity > 5) then begin print_string("Instantiating with " ^ (ftm_str w)); print_newline(); flush stdout end;
  let m1w = mk_norm_ap m1 w in
  insertWithPriority !fiFORALL_DELAY (ProcessProp1 m1w);
  let m1wlit = !get_literal_fn2 m1w in
  new_search_clause [nmlit;m1wlit]
    (if (mkprooftermp ()) then (Some(InstRule(a,m1,w))) else None)

let negforall_rule mlit a m1 =
  let (ws,w) = get_fresh_name (ty_f_rev a) in
  if (!verbosity > 4) then begin print_string("m1 = " ^ (ftm_str m1) ^ "\nUsing Fresh Witness " ^ (ftm_str w) ^ " of type " ^ (stp_str (ty_f_rev a)) ^ " in negforall_rule"); print_newline(); flush stdout end;
  process_new_name a w (get_int_flag "NEW_HEAD_ENUM_DELAY");
  let m1w = mk_norm_ap m1 w in
  if (!verbosity > 8) then begin print_string(" m1w = " ^ (ftm_str m1w)); print_newline(); flush stdout end;
  let nm1w = fneg m1w in
  insertWithPriority (get_int_flag "EXISTS_DELAY") (ProcessProp1 nm1w);
  let nm1wlit = !get_literal_fn2 nm1w in
  new_search_clause [-mlit;nm1wlit]
    (if (mkprooftermp ()) then (Some(FreshRule(a,m1,ws))) else None)

let decompose lit a largs rargs r =
  let delay = !fiPOST_DEC_DELAY in
  if !verbosity > 8 then Printf.printf "decompose %d %s\n" lit (stp_str a);
  let rec map2_ar sf ar la ra =
    match la, ra with
    | [], [] -> sf
    | (lh :: lt), (rh :: rt) ->
       if not (is_ar ar) then failwith "typing problem in decompose";
       let a1 = ty_get_l ar in
       let deq = mk_neg (mk_norm_eq (ty_f a1) lh rh) in
       if !verbosity > 8 then Printf.printf "decomposed eqn %s\n" (ftm_str deq);
       insertWithPriority delay (ProcessProp1 deq);
       map2_ar (!get_literal_fn2 deq :: sf) (ty_get_r ar) lt rt
  in
  let dlits = map2_ar [] a largs rargs in
  new_search_clause ((-lit)::dlits) r;;

let consider_confrontation a neqlit u v eqlit s t =
  let op = Confront(eqlit,neqlit,a,s,t,u,v) in
  let delay =
    if !fiCONFR_SAME2_DELAY <> !fiCONFR_SAME1_DELAY || !fiCONFR_SAME1_DELAY <> !fiCONFR_DIFF_DELAY then
      let sh = get_head s in
      let th = get_head t in
      let uh = get_head u in
      let vh = get_head v in
      if (((sh == uh) && (th == vh)) || ((sh == vh) && (th == uh))) then
        !fiCONFR_SAME2_DELAY
      else if ((sh == uh) || (th == vh) || (sh == vh) || (th == uh)) then
        !fiCONFR_SAME1_DELAY
      else
        !fiCONFR_DIFF_DELAY
    else !fiCONFR_DIFF_DELAY
  in
  insertWithPriority delay op

let consider_confrontation_list ty mlit m1 m2 l l_is_pos =
  if !fiPRIORITY_QUEUE_IMPL = 3 || (!fiCONFR_SAME2_DELAY = !fiCONFR_SAME1_DELAY && !fiCONFR_SAME1_DELAY = !fiCONFR_DIFF_DELAY) then
    insertWithPriority !fiCONFR_DIFF_DELAY (ConfrontList(ty, mlit, m1, m2, l, l_is_pos)) else
  let iter_fun_pos1 (otherlit,n1,n2) = consider_confrontation ty mlit m1 m2 otherlit n1 n2 in
  let iter_fun_neg1 (otherlit,n1,n2) = consider_confrontation ty otherlit n1 n2 mlit m1 m2 in
  if l_is_pos then List.iter iter_fun_pos1 l else List.iter iter_fun_neg1 l;;

let confront a eqlit s t neqlit u v =
  if (!verbosity > 9) then Printf.printf "Confront %d %d\n" eqlit neqlit;
  let r = if (mkprooftermp ()) then (Some (ConfrontationRule(eqlit,neqlit))) else None in
  let minuseqlit = (- eqlit) in
  let minusneqlit = (- neqlit) in
  let su = mk_norm_eq a s u in
  let tu = mk_norm_eq a t u in
  let sv = mk_norm_eq a s v in
  let tv = mk_norm_eq a t v in
  let msulit = (- (!get_literal_fn2 su)) in
  let mtulit = (- (!get_literal_fn2 tu)) in
  let msvlit = (- (!get_literal_fn2 sv)) in
  let mtvlit = (- (!get_literal_fn2 tv)) in
  insertWithPriority (!fiPOST_CONFRONT1_DELAY) (ProcessProp1 (mk_neg su));
  insertWithPriority (!fiPOST_CONFRONT2_DELAY) (ProcessProp1 (mk_neg tu));
  insertWithPriority (!fiPOST_CONFRONT3_DELAY) (ProcessProp1 (mk_neg sv));
  insertWithPriority (!fiPOST_CONFRONT4_DELAY) (ProcessProp1 (mk_neg tv));
  new_search_clause [minuseqlit;minusneqlit;msulit;msvlit] r;
  new_search_clause [minuseqlit;minusneqlit;msulit;mtvlit] r;
  new_search_clause [minuseqlit;minusneqlit;mtulit;msvlit] r;
  new_search_clause [minuseqlit;minusneqlit;mtulit;mtvlit] r

let confront_list ty mlit m1 m2 l l_is_pos =
  let iter_fun_pos2 (otherlit,n1,n2) = confront ty otherlit n1 n2 mlit m1 m2 in
  let iter_fun_neg2 (otherlit,n1,n2) = confront ty mlit m1 m2 otherlit n1 n2 in
  if l_is_pos then List.iter iter_fun_pos2 l else List.iter iter_fun_neg2 l;;

let choice_rule m args =
  match (fchoiceop m) with
  | Some(a) ->
      begin
	match args with
	| (pred::_) ->
	   let m1 = mk_norm_ap pred (mk_norm_ap m pred) in
	   let m2 = mk_all a (fneg (mk_norm_ap (uptrm pred 1 0) (mk_db 0))) in
	   insertWithPriority (get_int_flag "CHOICE_EMPTY_DELAY") (ProcessProp1 m2);
	   insertWithPriority (get_int_flag "CHOICE_IN_DELAY") (ProcessProp1 m1);
           if !verbosity > 5 then Printf.printf "choicerule (%d %d) %s %s\n" (!get_literal_fn2 m1) (!get_literal_fn2 m2) (ftm_str m) (ftm_str pred);
	   new_search_clause [!get_literal_fn2 m1;!get_literal_fn2 m2] (if (mkprooftermp ()) then (Some(ChoiceRule(m,pred))) else None)
	| _ -> raise (GenericError "Choice operator must be applied to at least one argument")
      end
  | None -> ()  

let rec subterms_as_instantiations cx m b =
  if get_maxv m = 0 && (!fbINITIAL_SUBTERMS_AS_INSTANTIATIONS_O || not (b = mk_prop)) then possibly_new_instantiation b m;
  match get_tag m with
  | FT_Lam ->
     subterms_as_instantiations (ty_get_l b::cx) (get_l m) (ty_get_r b)
  | FT_Ap ->
     let m1 = get_l m in
     let m2 = get_r m in
     let ab = subterms_as_instantiations_2 cx m1 in
     if get_maxv m1 = 0 then possibly_new_instantiation ab m1;
     let a = ty_get_l ab in
     subterms_as_instantiations cx m2 a;
  | FT_Imp ->
     let m1 = get_l m in
     let m2 = get_r m in
     subterms_as_instantiations cx m1 mk_prop;
     subterms_as_instantiations cx m2 mk_prop;
  | FT_Eq ->
     let m1 = get_l m in
     let m2 = get_r m in
     let a = get_no m in
     subterms_as_instantiations cx m1 a;
     subterms_as_instantiations cx m2 a;
  | FT_All ->
     subterms_as_instantiations (get_no m::cx) (get_l m) mk_prop;
  | _ -> ()
and subterms_as_instantiations_2 cx m =
  match get_tag m with
  | FT_Ap ->
     let m1 = get_l m in
     let m2 = get_r m in
     let ab = subterms_as_instantiations_2 cx m1 in
     if get_maxv m1 = 0 then possibly_new_instantiation ab m1;
     let a = ty_get_l ab in
     subterms_as_instantiations cx m2 a;
     ty_get_r ab
  | FT_DB -> List.nth cx (get_no m)
  | FT_Name -> Vector.get name_tp (get_no m)
  | FT_Lam -> raise (Failure "impossible beta redex")
  | FT_Choice -> let a = get_no m in mk_ar (mk_ar a mk_prop) a
  (** the following cases are also impossible **)
  | _ -> raise (Failure "impossible for a well typed term")

(*** Enumeration of types can be preserved across subgoals.  The types are global. ***)
let typesgenerated = ref 0

let typesofdepth : (int,stp) Hashtbl.t = Hashtbl.create 3

let generate_type d a =
  if (!verbosity > 9) then (Printf.printf "Generated type %s of depth %d\n" (stp_str a) d; flush stdout);
  Hashtbl.add typesofdepth d a

let nth_term a n =
  let rec nth_db_aux b i n cx =
    if !verbosity > 9 then (Printf.printf "nth_db_aux in %s %d %d\n" (stp_str b) i n; flush stdout);
    match cx with
    | a::cxr ->
       if n land 1 = 1 then
         let (sigmal,ar) = argtps_rtp a in
         if ar = b then
           (mk_db i,sigmal,n asr 1)
         else
           raise Not_found
       else
         nth_db_aux b (i+1) (n asr 1) cxr
    | _ -> raise Not_found
  in
  let rec nth_name_aux n hl =
    match hl with
    | (sigmal,h,_)::hr ->
       if n land 1 = 1 then
         (h,sigmal,n asr 1)
       else
         nth_name_aux (n asr 1) hr
    | _ -> raise Not_found
  in
  let rec nth_sort_aux n l =
    match l with
    | x::r ->
       let c = n land 1 in
       let n = n asr 1 in
       if c = 0 then
         (mk_base x,n)
       else
         nth_sort_aux n r
    | _ -> raise Not_found
  in
  let rec nth_type_aux n =
    let c = n land 1 in
    let n = n asr 1 in
    if c = 0 then
      nth_sort_aux n !name_base_list
    else
      let c = n land 1 in
      let n = n asr 1 in
      if c = 0 then
        (mk_prop,n)
      else
        let (a1,n) = nth_type_aux n in
        let (a2,n) = nth_type_aux n in
        (mk_ar a1 a2,n)
  in
  let rec nth_term_aux a n cx =
    if !verbosity > 9 then (Printf.printf "nth_term_aux in %s %d\n" (stp_str a) n; flush stdout);
    if is_ar a then
      let a1 = ty_get_l a in
      let a2 = ty_get_r a in
      let (m,n) = nth_term_aux a2 n (a1::cx) in
      (mk_norm_lam (ty_f a1) m,n)
    else if a = mk_prop then
      begin
        let c = n land 3 in
        let n = n asr 2 in
        if c = 0 then
          (mk_false,n)
        else if c = 1 then
          let (z,sigmal,n) = nth_db_aux mk_prop 0 n cx in
          nth_spine_aux z sigmal n cx
        else if c = 2 then
          let (z,sigmal,n) = nth_name_aux n (usable_heads_rtp a) in
          nth_spine_aux z sigmal n cx
        else
          let c = n land 3 in
          let n = n asr 2 in
          if c = 0 then
            let (m1,n) = nth_term_aux mk_prop n cx in
            let (m2,n) = nth_term_aux mk_prop n cx in
            (mk_norm_imp m1 m2,n)
          else if c = 1 then
            let (b1,n) = nth_type_aux n in
            let (m1,n) = nth_term_aux mk_prop n (b1::cx) in
            (mk_all (ty_f b1) m1,n)
          else if c = 2 then
            let (b1,n) = nth_type_aux n in
            let (m1,n) = nth_term_aux b1 n cx in
            let (m2,n) = nth_term_aux b1 n cx in
            (mk_norm_eq (ty_f b1) m1 m2,n)
          else
            if !fiCHOICE then
              let (b1,n) = nth_type_aux n in
              let (sigmal,rtp) = argtps_rtp b1 in
              if rtp = a then
                nth_spine_aux (mk_choice (ty_f b1)) ((mk_ar b1 mk_prop)::sigmal) n cx
              else
                raise Not_found
            else
              raise Not_found
      end
    else
      let b = ty_get_no a in
      let c = n land 1 in
      let n = n asr 1 in
      if c = 0 then
        let (z,sigmal,n) = nth_db_aux a 0 n cx in
        nth_spine_aux z sigmal n cx
      else
        let c = n land 1 in
        let n = n asr 1 in
        if c = 0 then
          let (z,sigmal,n) = nth_name_aux n (usable_heads_rtp a) in
          nth_spine_aux z sigmal n cx
        else
          if !fiCHOICE then
            let (b1,n) = nth_type_aux n in
            let (sigmal,rtp) = argtps_rtp b1 in
            if rtp = a then
              nth_spine_aux (mk_choice (ty_f b1)) ((mk_ar b1 mk_prop)::sigmal) n cx
            else
              raise Not_found
          else
            raise Not_found
  and nth_spine_aux h sigmal n cx =
    if !verbosity > 9 then (Printf.printf "nth_spine_aux in %s %d\n" (ftm_str h) n; flush stdout);
    match sigmal with
    | [] -> (h,n)
    | sigma::sigmar ->
       let (m,n) = nth_term_aux sigma n cx in
       nth_spine_aux (mk_norm_ap h m) sigmar n cx
  in
  let (m,n2) = nth_term_aux a n [] in
  if n2 = 0 then
    m
  else
    raise Not_found

let nth_term_linear a n =
  let rec nth_type n =
    let len = List.length !name_base_list + 2 in
    let m = n mod len in
    let n = n / len in
    if m = 0 then
      (mk_prop, n)
    else if m = len - 1 then
      let (a1,n) = nth_type n in
      let (a2,n) = nth_type n in
      (mk_ar a1 a2,n)
    else
      (mk_base (List.nth !name_base_list (m - 1)), n)
  in
  let rec nth_db b n cx =
    if !verbosity > 9 then (Printf.printf "nth_db_aux in %s %d\n" (stp_str b) n; flush stdout);
    let cxlen = List.length cx in
    if cxlen = 0 then raise Not_found;
    let i = n mod cxlen in
    let a = List.nth cx i in
    let (sigmal,ar) = argtps_rtp a in
    if ar = b then
      nth_spine (mk_db i) sigmal (n / cxlen) cx
    else
      raise Not_found
  and nth_db_nonlinear b i n cx ocx =
    if !verbosity > 9 then (Printf.printf "nth_db_aux in %s %d %d\n" (stp_str b) i n; flush stdout);
    match cx with
    | a::cxr ->
       if n land 1 = 1 then
         let (sigmal,ar) = argtps_rtp a in
         if ar = b then nth_spine (mk_db i) sigmal (n asr 1) ocx
         else raise Not_found
       else
         nth_db_nonlinear b (i+1) (n asr 1) cxr ocx
    | _ -> raise Not_found
  and nth_name n cx hl =
    let hllen = List.length hl in
    if hllen = 0 then raise Not_found;
    let (sigmal,h,_) = List.nth hl (n mod hllen) in
    nth_spine h sigmal (n / hllen) cx
  and nth_name_nonlinear n cx = function
    | (sigmal,h,_)::hr ->
       if n land 1 = 1 then
         nth_spine h sigmal (n asr 1) cx
       else
         nth_name_nonlinear (n asr 1) cx hr
    | _ -> raise Not_found
  and nth_prop n cx =
    let c = n land 3 in
    let n = n asr 2 in
    if c = 0 then
      (mk_false,n)
    else if c = 1 then
(*      nth_db_nonlinear mk_prop 0 n cx cx*)
      nth_db mk_prop n cx
    else if c = 2 then
      nth_name_nonlinear n cx (usable_heads_rtp a)
    else
      let c = n land 3 in
      let n = n asr 2 in
      if c = 0 then
        let (m1,n) = nth_prop n cx in
        let (m2,n) = nth_prop n cx in
        (mk_norm_imp m1 m2,n)
      else if c = 1 then
        let (b1,n) = nth_type n in
        let (m1,n) = nth_prop n (b1::cx) in
        (mk_all (ty_f b1) m1,n)
      else if c = 2 then
        let (b1,n) = nth_type n in
        let (m1,n) = nth_term_aux b1 n cx in
        let (m2,n) = nth_term_aux b1 n cx in
        (mk_norm_eq (ty_f b1) m1 m2,n)
      else
        if !fiCHOICE then
          let (b1,n) = nth_type n in
          let (sigmal,rtp) = argtps_rtp b1 in
          if rtp = a then
            nth_spine (mk_choice (ty_f b1)) ((mk_ar b1 mk_prop)::sigmal) n cx
          else
            raise Not_found
        else
          raise Not_found
  and nth_noprop a n cx =
    if n = 0 then raise Not_found; (* Termination *)
    let n = n - 1 in
    let b = ty_get_no a in
    let c = n land 1 in
    let n = n asr 1 in
    if c = 0 then
(*      nth_db_nonlinear a 0 n cx cx*)
      nth_db a n cx
    else
      let c = n land 1 in
      let n = n asr 1 in
      if c = 0 then
        nth_name_nonlinear n cx (usable_heads_rtp a)
      else
        if !fiCHOICE then
          let (b1,n) = nth_type n in
          let (sigmal,rtp) = argtps_rtp b1 in
          if rtp = a then
            nth_spine (mk_choice (ty_f b1)) ((mk_ar b1 mk_prop)::sigmal) n cx
          else
            raise Not_found
        else
          raise Not_found
  and nth_term_aux a n cx =
    if !verbosity > 9 then (Printf.printf "nth_term_aux in %s %d\n" (stp_str a) n; flush stdout);
    if is_ar a then
      let a1 = ty_get_l a in
      let a2 = ty_get_r a in
      let (m,n) = nth_term_aux a2 n (a1::cx) in
      (mk_norm_lam (ty_f a1) m,n)
    else if a = mk_prop then
      nth_prop n cx
    else
      nth_noprop a n cx
  and nth_spine h sigmal n cx =
    if !verbosity > 9 then (Printf.printf "nth_spine_aux in %s %d\n" (ftm_str h) n; flush stdout);
    match sigmal with
    | [] -> (h,n)
    | sigma::sigmar ->
       let (m,n) = nth_term_aux sigma n cx in
       nth_spine (mk_norm_ap h m) sigmar n cx
  in
  let (m,n2) = nth_term_aux a n [] in
  if n2 = 0 then
    m
  else
    raise Not_found;;

let nth_term = nth_term_linear;;

(*** Assume all types of depth < d are known.  Generate all those of depth d. ***)
let generate_types d =
  if (!verbosity > 9) then (Printf.printf "Generate types called with depth %d\n" d; flush stdout);
  if (d = (get_int_flag "ENUM_O")) then generate_type d mk_prop;
  if (d = (get_int_flag "ENUM_SORT")) then
    (List.iter (fun a -> generate_type d (mk_base a)) !name_base_list);
  let dm = d - 1 - !fiENUM_ARROW in
  if (dm >= 0) then
    begin
      for i = 0 to dm
      do
	List.iter
	  (fun ai ->
	    List.iter
	      (fun aj ->
		generate_type d (mk_ar ai aj))
	      (Hashtbl.find_all typesofdepth (dm - i)))
	  (Hashtbl.find_all typesofdepth i)
      done;
    end

(*
let list_rev_mapi f start_acc l =
  let rec rmapi_f i acc = function
    | [] -> acc
    | a::l -> rmap_f (i + 1) (f i a :: acc) l
  in
  rmapi_f 0 start_acc l;;
*)

let rec list_rev_map f acc = function
  | [] -> acc
  | a::l -> list_rev_map f (f a :: acc) l;;

let rec fold_lefti i f acc = function
  | [] -> acc
  | a::l -> fold_lefti (i + 1) f (f i acc a) l;;

let rec fold_downfrom f sf n = if n < 0 then sf else fold_downfrom f (f sf n) (n - 1);;

let neg0 = mk_norm_lam mk_prop (mk_neg (mk_db 0));;
let imp0 = mk_norm_lam mk_prop (mk_norm_lam mk_prop (mk_norm_imp (mk_db 1) (mk_db 0)));;
let eq0 ty = mk_norm_lam ty (mk_norm_lam ty (mk_norm_eq ty (mk_db 1) (mk_db 0)));;
let all0 ty = mk_norm_lam (mk_ar ty mk_prop) (mk_all ty (mk_norm_ap (mk_db 1) (mk_db 0)));;

let rec enum_depth sf d ctx a =
  if d < 0 then sf else
  if is_ar a then
    let a1 = ty_get_l a and a2 = ty_get_r a in
    list_rev_map (mk_norm_lam a1) sf (enum_depth [] d (a1 :: ctx) a2)
  else
    let proj_i i sf sigma =
      let (sigmal,b) = argtps_rtp sigma in
      if (a = b) then enum_depth_spine (d - 1) ctx sigmal sf (mk_db i) else sf
    in
    let sf = fold_lefti 0 proj_i sf ctx in
    let ffun_heads sf (sigmal,h,pimit) = enum_depth_spine (d - pimit) ctx sigmal sf h in
    let sf = List.fold_left ffun_heads sf (usable_heads_rtp a) in
    let fold_edi i sf sigma =
      let (sigmal,b) = argtps_rtp sigma in
      let sf =
        if (a <> b) then sf else
          enum_depth_spine (d - i - 1) ctx ((mk_ar sigma mk_prop)::sigmal) sf (mk_choice sigma) in
      if a <> mk_prop then sf else
        let sf = enum_depth_spine (d - i - 1) ctx [mk_ar sigma mk_prop] sf (all0 sigma) in
        enum_depth_spine (d - i - 1) ctx [sigma;sigma] sf (eq0 sigma)
    in
    let fold_edi2 sf i = List.fold_left (fold_edi i) sf (Hashtbl.find_all typesofdepth i) in
    let sf = fold_downfrom fold_edi2 sf (d - 1) in
    if a <> mk_prop then sf else
      let sf = enum_depth_spine (d - 1) ctx [mk_prop] sf neg0 in
      let sf = enum_depth_spine (d - 1) ctx [mk_prop;mk_prop] sf imp0 in
      enum_depth_spine (d - 1) ctx [] sf mk_false
and enum_depth_spine d ctx sigmal sf h =
  match sigmal with
  | (a::st) ->
     let atms = enum_depth [] d ctx a in
     List.fold_left (fun sf m -> enum_depth_spine d ctx st sf (mk_norm_ap h m)) sf atms
  | [] -> h :: sf



let leibeq_to_primeq m =
  let f m =
    match get_tag m with
    | FT_All ->
       let m2 = get_l m in
       begin
         match get_tag m2 with
         | FT_Imp ->
            let m2a = get_l m2 in
            begin
              match get_tag m2a with
              | FT_Ap ->
                 let m2b = get_r m2 in
                 begin
                   match get_tag m2b with
                   | FT_Ap ->
                      begin
                        let m2aa = get_l m2a in
                        let m2ba = get_l m2b in
                        match get_tag m2aa,get_tag m2ba with
                        | FT_DB,FT_DB ->
                           if get_no m2aa = 0 && get_no m2ba = 0 then
                             let m3 = get_r m2a in
                             let m4 = get_r m2b in
                             if get_fv0_0 m3 && get_fv0_0 m4 then
                               begin
                                 let a = ty_f_rev (get_no m) in
                                 match ty_pred_over a with
                                 | Some(a2) ->
                                    let meq = mk_norm_eq (ty_f a2) (uptrm m3 0 (-1)) (uptrm m4 0 (-1)) in
                                    if !verbosity > 4 then Printf.printf "replacing %s\nwith primitive equation %s\n" (ftm_str m) (ftm_str meq);
                                    Some(meq)
                                 | _ -> None (* shouldn't happen; ill typed *)
                               end
                             else
                               None
                           else
                             None
                        | FT_Ap,FT_Ap ->
                           let m3 = get_r m2a in
                           let m4 = get_r m2b in
                           if ftm_db_p 0 (get_l m2aa) && ftm_db_p 0 (get_l m2ba) && get_r m2aa = m4 && get_r m2ba = m3 && get_fv0_0 m3 && get_fv0_0 m4 then
                             begin
                               let a = ty_f_rev (get_no m) in
                               if is_ar a then
                                 let a3 = ty_get_r a in
                                 if is_ar a3 && ty_get_r a3 = mk_prop then
                                   let a2 = ty_get_l a in
                                   let meq = mk_norm_eq (ty_f a2) (uptrm m3 0 (-1)) (uptrm m4 0 (-1)) in
                                   (if !verbosity > 4 then Printf.printf "replacing %s\nwith primitive equation %s\n" (ftm_str m) (ftm_str meq));
                                   Some(meq)
                                 else
                                   None (* shouldn't happen; ill typed *)
                               else
                                 None (* shouldn't happen; ill typed *)
                             end
                           else
                             None
                        | _,_ -> None
                      end
                   | _ -> None
                 end
              | FT_All ->
                 let m2aa = get_l m2a in
                 begin
                   match get_tag m2aa with
                   | FT_Ap ->
                      let m2aaa = get_l m2aa in
                      begin
                        match get_tag m2aaa with
                        | FT_Ap ->
                           if ftm_db_p 1 (get_l m2aaa) && ftm_db_p 0 (get_r m2aaa) && ftm_db_p 0 (get_r m2aa) then
                             begin
                               let m2b = get_r m2 in
                               match get_tag m2b with
                               | FT_Ap ->
                                  let m2ba = get_l m2b in
                                  begin
                                    match get_tag m2ba with
                                    | FT_Ap ->
                                       let m3 = get_r m2ba in
                                       let m4 = get_r m2b in
                                       if ftm_db_p 0 (get_l m2ba) && get_fv0_0 m3 && get_fv0_0 m4 then
                                         let a2 = get_no m2a in
                                         let meq = mk_norm_eq a2 (uptrm m3 0 (-1)) (uptrm m4 0 (-1)) in
                                         (if !verbosity > 4 then Printf.printf "replacing %s\nwith primitive equation %s\n" (ftm_str m) (ftm_str meq));
                                         Some(meq)
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
            end
         | _ -> None
       end
    | _ -> None
  in
  let f2 t =
    match f t with
    | Some t2 -> t2
    | None -> t
  in
(*replace_subterms f m*)
  Ftm.unique_subterm_bottom_up_replace f2 m

exception ExistsToChoiceDone

let rec existstochoice1 m p =
  match get_tag m with
  | FT_All ->
     if p then
       mk_all (get_no m) (existstochoice1 (get_l m) p)
     else (*** This is where the action is: Replace (forall x, q[x]) with (q[Eps x:a => ~q[x]]) ***)
       let q = get_l m in
       let a = get_no m in
       Ftm.subst q 0 (mk_norm_ap (mk_choice a) (mk_norm_lam a (fneg q)))
  | FT_Eq ->
     begin
       let a = get_no m in
       let aa = ty_f_rev a in
       if is_ar aa then
         let a1 = ty_get_l aa in
         let a2 = ty_get_r aa in
         let m1s = uptrm (get_l m) 0 1 in
         let m2s = uptrm (get_r m) 0 1 in
	 existstochoice1
           (mk_all (ty_f a1) (mk_norm_eq (ty_f a2) (mk_norm_ap m1s (mk_db 0)) (mk_norm_ap m2s (mk_db 0))))
	   p
       else
         raise ExistsToChoiceDone
     end
  | FT_Imp ->
     begin
       let m1 = get_l m in
       let m2 = get_r m in
       try
	 mk_norm_imp (existstochoice1 m1 (not p)) m2
       with ExistsToChoiceDone
	    -> mk_norm_imp m1 (existstochoice1 m2 p)
     end
  | _ -> raise ExistsToChoiceDone
  
let rec existstochoice m =
  try
    existstochoice (existstochoice1 m true)
  with ExistsToChoiceDone -> m

let already_preprocessed = ref false

let process_mating plit nlit a pargs nargs =
  if (!verbosity > 9) then Printf.printf "Mating %d %d\na: %s\n" plit nlit (stp_str a);
  let pmd = !fiPOST_MATING_DELAY in
  let rec pso_map3 ret ty pa na =
    if is_ar ty then
      let a = ty_get_l ty in
      let b = ty_get_r ty in
      match pa, na with
      | pah :: pat, nah :: nat ->
         let deq = mk_neg (mk_norm_eq (ty_f a) pah nah) in
         insertWithPriority pmd (ProcessProp1 deq);
         pso_map3 ((!get_literal_fn2 deq) :: ret) b pat nat
      | _ -> assert false
    else
      match pa, na with
      | [],[] -> ret
      | _ -> assert false
  in
  let dlits = pso_map3 [] a pargs nargs in
  new_search_clause
    ((-plit)::(-nlit)::dlits)
    (if (mkprooftermp ()) then (Some (MatingRule(plit,nlit))) else None);;

let process_mating_list lit args a lst lst_is_pos =
  let iter_fun_pml_n (lit2,args2) = if args <> args2 then process_mating lit lit2 a args args2 in
  let iter_fun_pml_p (lit2,args2) = if args <> args2 then process_mating lit2 lit a args2 args in
  if lst_is_pos then List.iter iter_fun_pml_p lst else List.iter iter_fun_pml_n lst;;

let preprocess m =
  let m1 =
    if (get_bool_flag "LEIBEQ_TO_PRIMEQ") then leibeq_to_primeq m else m
  in
  let m2 =
    if (get_bool_flag "EXISTSTOCHOICE") then existstochoice m1 else m1
  in
  m2
                         
let preprocess1 m =
  if (!already_preprocessed) then
    m
  else
    try
      Hashtbl.find preprocess_ftm m
    with
    | Not_found ->
       let n = preprocess m in
       if not (n = m) then Hashtbl.add preprocess_ftm m n;
       n

let process_negation mlit m nm =
  begin
    match get_tag nm with
    | FT_False -> () (*** do nothing ***)
    | FT_Imp ->
       let m1 = get_l nm in
       let m2 = get_r nm in
       if m2 = mk_false then
         insertWithPriority 0 (ProcessProp1 m1) (** double negation case **)
       else
         negimp_rule mlit nm m1 m2
    | FT_All ->
       let a = get_no nm in
       let m1t = get_l nm in
       (* if ((!enable_pattern_clauses) && (get_bool_flag "PATTERN_CLAUSES_FORALL_AS_LIT")) then (apply_pattern_clauses mlit m); *)
       let m1 = mk_norm_lam a m1t in
       negforall_rule mlit a m1
    | FT_Eq ->
       let a = get_no nm in
       let m1 = get_l nm in
       let m2 = get_r nm in
       let r = if (mkprooftermp ()) then (Some(NegPropRule(nm))) else None in
       begin
	 if (m1 == m2) then new_search_clause [-mlit] r (*** negation of reflexivity ***)
         else if !fiSYM_EQ then sym_eq_clauses (-mlit) a m1 m2; (*** Equivalence of = with symmetric version. In earlier versions of Satallax (< 2.2) I sent m1=m2 and m2=m1 to the same literal. ***)
         let aa = ty_f_rev a in
         if is_ar aa then (*** FE ***)
           begin
             let a1 = ty_get_l aa in
             let a2 = ty_get_r aa in
            (***				  let m3 = neg (forall a1 (eq a2 (norm name_def (Ap (shift m1 0 1,DB (0,a1)))) (norm name_def (Ap (shift m2 0 1,DB (0,a1)))))) in  ***)
	     let m3 = mk_neg (mk_all (ty_f a1) (mk_norm_eq (ty_f a2) (mk_norm_ap m1 (mk_db 0)) (mk_norm_ap m2 (mk_db 0)))) in (*** No need to shift, since no dangling DB's [Thanks to Teucke!] ; Mar 15, normalize at the end to handle final eta (see FQ too) ***)
	     insertWithPriority (get_int_flag "POST_FEQ_DELAY") (ProcessProp1 m3);
	     if (get_bool_flag "INSTANTIATE_WITH_FUNC_DISEQN_SIDES") then
	       begin
	         possibly_new_instantiation a m1;
	         possibly_new_instantiation a m2
	       end;
	     let m3lit = !get_literal_fn2 m3 in
	     new_search_clause [-mlit;m3lit] r
           end
         else if aa = mk_prop then (*** BE ***)
           begin
	     let m1lit = !get_literal_fn2 m1 in
	     let m2lit = !get_literal_fn2 m2 in
	     insertWithPriority !fiPOST_NEQO_L_DELAY (ProcessProp1 m1);
	     insertWithPriority !fiPOST_NEQO_R_DELAY (ProcessProp1 m2);
	     insertWithPriority !fiPOST_NEQO_NL_DELAY (ProcessProp1 (fneg m1));
	     insertWithPriority !fiPOST_NEQO_NR_DELAY (ProcessProp1 (fneg m2));
	     new_search_clause [-mlit;m1lit;m2lit] r;
	     new_search_clause [-mlit;-m1lit;-m2lit] r
           end
         else if is_base aa then
           begin
             (*** decompose, confront, Choice accessible, special accessible ***)
	     if ((get_bool_flag "FILTER_NEGEQ") && (filterp mlit)) then
	       ()
	     else
	       begin
		 Vector.update neqns a (fun neqo -> (mlit,m1,m2) :: neqo);
                 (** (delayed) confrontation **)
                 consider_confrontation_list a mlit m1 m2 (Vector.get_default peqns a []) true;
		 possibly_new_instantiation a m1;
		 possibly_new_instantiation a m2;
		 let (lh,largs) = get_head_spine m1 in
		 let (rh,rargs) = get_head_spine m2 in
                 if lh == rh then
                   begin
                     match get_tag lh with
                     | FT_Choice ->
                        let la1 = ty_f_rev (get_no lh) in
		        decompose mlit (mk_ar (mk_ar la1 mk_prop) la1) largs rargs r
                     | FT_Name ->
                        let lhname = get_no lh in
                        if decomposable lhname then
                          begin
                            try
			      decompose mlit (Vector.get name_tp lhname) largs rargs r
                            with Not_found -> ()
                          end
		     | _ -> ()
		   end;
		 choice_rule lh largs;
		 choice_rule rh rargs;
	       end
           end
       end
    | _ ->
       let (h,args) = get_head_spine nm in
       match get_tag h with
       | FT_Choice ->
	  if (!fbFILTER_NEGATM && (filterp mlit)) then
	    ()
	  else
	    begin
	      let pmd = get_int_flag "PRE_CHOICE_MATING_DELAY_NEG" in
              let a = get_no h in
	      Vector.update nchoiceatoms a (fun ncao -> (mlit,args) :: ncao);
              let a1 = ty_f_rev a in
              let a2 = mk_ar (mk_ar a1 mk_prop) a1 in
              let l = Vector.get_default pchoiceatoms a [] in
              insertWithPriority pmd (MatingList(mlit,args,a2,l,true));
	      choice_rule h args;
	    end
       | FT_Name -> (** negative atom **)
	  if ((get_bool_flag "FILTER_NEGATM") && (filterp mlit)) then
	    ()
	  else
	    begin
              let x = get_no h in
	      if (decomposable x) then
		begin
		  let pmd = !fiPRE_MATING_DELAY_NEG in
                  Vector.update natoms x (fun nao -> (mlit,args) :: nao);
                  let a2 = Vector.get name_tp x in
                  let l = Vector.get_default patoms x [] in
                  insertWithPriority pmd (MatingList(mlit,args,a2,l,true));
		end;
	      choice_rule h args;
              begin
                match args with
                | [arg1;arg2] ->
                   begin
                     begin
                       match fcov1breln h with
                       | Some(a,s) ->
                          if !verbosity > 9 then Printf.printf "Doing cov1 rule\n";
                          let q = mk_norm_eq (ty_f a) arg1 arg2 in
                          let sr = mk_norm_ap (mk_norm_ap (mk_name s) arg1) arg2 in
                          insertWithPriority !fiCOV1BRELN_DELAY1 (ProcessProp1 q);
                          insertWithPriority !fiCOV1BRELN_DELAY2 (ProcessProp1 sr);
                          let qlit = !get_literal_fn2 q in
                          let srlit = !get_literal_fn2 sr in
                          new_search_clause [-mlit;srlit;qlit] None; (** forget about proofs for now **)
                       | _ -> ()
                     end;
                     begin
                       match fsymbreln h with
                       | Some(a) ->
                          if !verbosity > 9 then Printf.printf "Doing sym rule\n";
                          let hs = mk_norm_ap (mk_norm_ap h arg2) arg1 in
                          insertWithPriority !fiSYMBRELN_DELAY (ProcessProp1 hs);
                          let hslit = !get_literal_fn2 hs in
                          new_search_clause [-mlit;-hslit] None; (** forget about proofs for now **)
                       | _ -> ()
                     end
                   end
                | _ -> ()
	      end
	    end
       | _ ->
          Printf.printf "nm: %s\n" (ftm_str nm);
          raise (GenericError ("Unhandled case 1 (were logical constants normalized?) h:" ^ (ftm_str h)))
  end

let process_forall mlit m a m1t =
  begin
    (*		      if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m; if (!dynamic_pattern_clauses) then new_pattern_clauses (-mlit) m); *)
    if (!fbFILTER_UNIV && (filterp mlit)) then
      ()
    else
      let nmlit = (- mlit) in
      begin
        let m1 = mk_norm_lam a m1t in
	Vector.update univpreds a (fun upo -> (nmlit,m1) :: upo);
        (*                          if (get_bool_flag "HOUNIF1") then hounif1 (!verbosity) (to_meta m) [] [] [] (get_int_flag "HOUNIF1BOUND") true possibly_new_instantiation; (*** Mar 2012 ***) *)
	let insts = (get_instantiations a) in
        let aa = ty_f_rev a in
        if is_ar aa then
	  begin
            let a2 = ty_get_r aa in
	    let rta = rtp a2 in
	    begin
              if is_base rta then (** no default elt for types that return Prop **)
                let rtano = ty_get_no rta in
		if (not (default_elt_p rtano)) then
		  (insertWithPriority (get_int_flag "DEFAULTELT_DELAY") (DefaultElt rtano));
	    end;
            begin (** since there is a quantifier of arrow type, start a simple enumeration scheme for instantiations. This is needed for theoretical completeness but is utterly impractical. **)
              if not (enum_of_started a) then
                let d = get_int_flag "ENUM_START" in
                enum_of_start a;
                insertWithPriority d (EnumInst(ty_f_rev a,0));
            end;
	  end
        else if is_base aa then
	  begin
            let ano = ty_get_no aa in
	    match insts with
	    | [] ->
	       insertWithPriority (get_int_flag "DEFAULTELTINST_DELAY") (DefaultEltInst ano)
	    | _ -> ()
	  end;
        List.iter (forall_rule nmlit a m1) insts
      end
  end

let process_equality mlit m a m1 m2 =
  let r = if (mkprooftermp ()) then (Some(PosPropRule(m))) else None in
  begin
    if ((not (m1 == m2)) && !fiSYM_EQ) then sym_eq_clauses mlit a m1 m2; (*** Equivalence of = with symmetric version. In earlier versions of Satallax (< 2.2) I sent m1=m2 and m2=m1 to the same literal. ***)
    (*				  if ((get_bool_flag "PATTERN_CLAUSES_TRANSITIVITY_EQ") && (not (Hashtbl.mem pattern_clauses_transitivity_types a))) then
				  begin (*** April 6, 2011 - add a pattern clause for transitivity of equality the first time we see an equation at a type. ***)
				  let transa = forall a (forall a (forall a (imp (eq a (DB(2,a)) (DB(1,a))) (imp (eq a (DB(1,a)) (DB(0,a))) (eq a (DB(2,a)) (DB(0,a))))))) in
				  let transalit = !get_literal_fn2 transa in
				  let transa2 = forall a (forall a (forall a (imp (eq a (DB(2,a)) (DB(1,a))) (imp (eq a (DB(0,a)) (DB(1,a))) (eq a (DB(2,a)) (DB(0,a))))))) in
				  let transa2lit = !get_literal_fn2 transa2 in
				  let transa3 = forall a (forall a (forall a (imp (eq a (DB(1,a)) (DB(2,a))) (imp (eq a (DB(1,a)) (DB(0,a))) (eq a (DB(2,a)) (DB(0,a))))))) in
				  let transa3lit = !get_literal_fn2 transa3 in
				  Hashtbl.add pattern_clauses_transitivity_types a ();
				  pattern_clauses_forall_as_lit := false;
				  pattern_clauses_onlyallstrict := false;
				  new_search_clause [transalit] (if (mkprooftermp ()) then (Some (Known(transalit,coqknown("@eq_trans","eq_trans"),[a]))) else None);
				  new_search_clause [transa2lit] (if (mkprooftermp ()) then (Some (Known(transa2lit,coqknown("eq_trans2","eq_symtrans1"),[a]))) else None);
				  new_search_clause [transa3lit] (if (mkprooftermp ()) then (Some (Known(transa3lit,coqknown("eq_trans3","eq_symtrans2"),[a]))) else None);
				  new_pattern_clauses (- transalit) transa;
				  new_pattern_clauses (- transa2lit) transa2;
				  new_pattern_clauses (- transa3lit) transa3;
				  pattern_clauses_forall_as_lit := get_bool_flag "PATTERN_CLAUSES_FORALL_AS_LIT";
				  pattern_clauses_onlyallstrict := get_bool_flag "PATTERN_CLAUSES_ONLYALLSTRICT";
				  end;  *)
    let aa = ty_f_rev a in
    if is_ar aa then (*** FQ ***)
      let a1 = ty_get_l aa in
      let a2 = ty_get_r aa in
       (*			if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m); *)
       (***				  let m3 = forall a1 (eq a2 (norm name_def (Ap (shift m1 0 1,DB (0,a1)))) (norm name_def (Ap (shift m2 0 1,DB (0,a1))))) in ***)
      let m3 = mk_all (ty_f a1) (mk_norm_eq (ty_f a2) (mk_norm_ap m1 (mk_db 0)) (mk_norm_ap m2 (mk_db 0))) in (*** See FE above for why there's no shift on m1 and m2. Mar 15 2011: Normalize after everything, to make sure the case of a final eta is handled, e.g., forall x.s=x where s has no x free eta reduces. ***)
      insertWithPriority (get_int_flag "POST_NFEQ_DELAY") (ProcessProp1 m3);
      let m3lit = !get_literal_fn2 m3 in
      new_search_clause [-mlit;m3lit] r
    else if aa = mk_prop then (*** BQ ***)
       (*			if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m); *)
      let m1lit = !get_literal_fn2 m1 in
      let m2lit = !get_literal_fn2 m2 in
      insertWithPriority !fiPOST_EQO_L_DELAY (ProcessProp1 m1);
      insertWithPriority !fiPOST_EQO_R_DELAY (ProcessProp1 m2);
      insertWithPriority !fiPOST_EQO_NL_DELAY (ProcessProp1 (fneg m1));
      insertWithPriority !fiPOST_EQO_NR_DELAY (ProcessProp1 (fneg m2));
      new_search_clause [-mlit;m1lit;-m2lit] r;
      new_search_clause [-mlit;-m1lit;m2lit] r
    else
      if ((get_bool_flag "FILTER_POSEQ") && (filterp mlit)) then
	()
      else
	begin
           (*			    if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m); *)
	  Vector.update peqns a (fun peqo -> (mlit,m1,m2) :: peqo);
           (*** (delayed) confrontation ***)
          consider_confrontation_list a mlit m1 m2 (Vector.get_default neqns a []) false
	end;
  end
  
let process_unprocessed_prop mlit m =
  match get_tag m with
  | FT_Imp ->
     let m1 = get_l m in
     let m2 = get_r m in
     if m2 = mk_false then
       process_negation mlit m m1
     else
       begin
         (*		    if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m); *)
         imp_rule mlit m m1 m2
       end
  | FT_All -> process_forall mlit m (get_no m) (get_l m) (*** Instantiate ***)
  | FT_False ->
     let r = if (mkprooftermp ()) then (Some(PosPropRule(m))) else None in
     let flit = !get_literal_fn2 (mk_false) in
     new_search_clause [-flit] r
  | FT_Eq -> process_equality mlit m (get_no m) (get_l m) (get_r m)
  | _ ->
     begin
       let (h,args) = get_head_spine m in
       match get_tag h with
       | FT_Choice ->
	  let pmd = get_int_flag "PRE_CHOICE_MATING_DELAY_POS" in
	  if ((get_bool_flag "FILTER_POSATM") && (filterp mlit)) then
	    ()
	  else
	    begin
              (*			      if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m); *)
              let a = get_no h in
              Vector.update pchoiceatoms a (fun pcao -> (mlit,args) :: pcao);
              let a1 = ty_f_rev a in
              let a2 = mk_ar (mk_ar a1 mk_prop) a1 in
              let l = Vector.get_default nchoiceatoms a [] in
              insertWithPriority pmd (MatingList(mlit,args,a2,l,false));
	      choice_rule h args;
	    end
       | FT_Name -> (** positive atom **)
	  if (!fbFILTER_POSATM && (filterp mlit)) then
	    ()
	  else
	    begin
              (*			      if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m); *)
              let x = get_no h in
	      if (decomposable x) then
		begin
		  let pmd = !fiPRE_MATING_DELAY_POS in
                  Vector.update patoms x (fun pao -> (mlit,args) :: pao);
                  let a2 = Vector.get name_tp x in
                  let l = Vector.get_default natoms x [] in
                  insertWithPriority pmd (MatingList(mlit,args,a2,l,false));
		end;
	      choice_rule h args; (*** This was missing and caused some incompleteness (eg, CHOICE6 in mode59c). - Chad, Jan 25, 2011 ***)
              begin
                match args with
                | [arg1;arg2] ->
                   begin
                     match firrefbreln h with
                     | Some(a) ->
                        if !verbosity > 9 then Printf.printf "Doing irreflexivity rule\n";
                        let mr = mk_norm_eq (ty_f a) arg1 arg2 in
                        let deq = mk_neg mr in
                        insertWithPriority !fiIRREFBRELN_DELAY (ProcessProp1 deq);
                        let deqlit = !get_literal_fn2 deq in
                        new_search_clause [-mlit;deqlit] None; (** forget about proofs for now **)
                     | _ -> ()
                   end;
                   begin
                     match fsymbreln h with
                     | Some(a) ->
                        if !verbosity > 9 then Printf.printf "Doing sym rule\n";
                        let hs = mk_norm_ap (mk_norm_ap h arg2) arg1 in
                        insertWithPriority !fiSYMBRELN_DELAY (ProcessProp1 hs);
                        let hslit = !get_literal_fn2 hs in
                        new_search_clause [-mlit;hslit] None; (** forget about proofs for now **)
                     | _ -> ()
                   end;
                   begin
                     match fnocl1breln h with
                     | Some(a,l,extras) ->
                        if !verbosity > 9 then (Printf.printf "Doing nocl1 %d rule\n" (get_no h); flush stdout);
                        let pl = Hashtbl.find_all nocl1brelnnames_partial h in
                        if !verbosity > 9 then (Printf.printf "Doing nocl1 %d rule %d partials so far\n" (get_no h) (List.length pl); flush stdout);
                        List.iter
                          (fun (a,l,al,cl,extras,cnt) ->
                            begin
                              let lr = ref l in
                              let ll = ref [] in
                              try
                                while true do
                                  match !lr with
                                  | (i,j)::r when i = j -> raise (Failure "to do")
                                  | (i,j)::r ->
                                     let clr = ref (-mlit::cl) in
                                     let cntr = ref cnt in
                                     List.iter
                                       (fun (k,arg) ->
                                         if k = i then
                                           let q = mk_norm_eq (ty_f a) arg1 arg in
                                           let qlit = !get_literal_fn2 q in
                                           let nq = mk_neg q in
                                           cntr := nq::!cntr;
                                           clr := -qlit::!clr
                                         else if k = j then
                                           let q = mk_norm_eq (ty_f a) arg2 arg in
                                           let qlit = !get_literal_fn2 q in
                                           let nq = mk_neg q in
                                           cntr := nq::!cntr;
                                           clr := -qlit::!clr)
                                       al;
                                     let al = (i,arg1)::(j,arg2)::al in
                                     if !ll = [] && r = [] then
                                       begin
                                         try
                                           List.iter
                                             (fun (i,j) ->
                                               let q = mk_norm_ap (mk_norm_ap h (List.assoc i al)) (List.assoc j al) in
                                               let qlit = !get_literal_fn2 q in
                                               insertWithPriority !fiNOCL1BRELN_DELAY (ProcessProp1 (mk_neg q));
                                               let nq = mk_neg q in
                                               clr := -qlit::!clr)
                                             extras;
                                           List.iter
                                             (fun n ->
                                               insertWithPriority !fiNOCL1BRELN_DELAY (ProcessProp1 n))
                                             !cntr;
                                           new_search_clause !clr None (** forget about proofs for now **)
                                         with Not_found ->
                                           Printf.printf "problem in nocl1:\nal:\n";
                                           List.iter (fun (i,n) -> Printf.printf "%d := " i; Ftm.print n; Printf.printf "\n") al;
                                           flush stdout;
                                           raise Not_found
                                       end
                                     else
                                       Hashtbl.add nocl1brelnnames_partial h (a,!ll @ r,al,!clr,extras,!cntr);
                                     lr := r;
                                     ll := (i,j)::!ll
                                  | [] -> raise Exit
                                done
                              with Exit -> ()
                            end)
                          pl;
                        begin
                          let lr = ref l in
                          let ll = ref [] in
                          try
                            while true do
                              match !lr with
                              | (i,j)::r ->
                                 if i = j then
                                   raise (Failure "to do")
                                 else
                                   begin
                                     Hashtbl.add nocl1brelnnames_partial h (a,!ll @ r,[(i,arg1);(j,arg2)],[-mlit],extras,[]);
                                   end;
                                 lr := r;
                                 ll := (i,j)::!ll
                              | [] -> raise Exit
                            done
                          with Exit ->
                            ()
                        end;
                     | _ -> ()
                   end;
                | _ -> ()
	      end
	    end
       | _ -> raise (GenericError ("Unhandled case 2 (were logical constants normalized?) h:" ^ (ftm_str h)))
     end
    
let process_prop p op m =
  if (not (Ftm.processed_mem m)) then
    begin
      let mlit = !get_literal_fn2 m in
      if ((!not_in_prop_model_delay_p) && (!minisatsearchcounter = 0) && ((minisat_modelValue mlit) > 0)) then (*** Chad: Nov 2011 - delay if not true in the current prop approx; Chad: Dec 2012 - added condition that minisatsearchcounter = 0 so that modelValue is only called if the last interaction with minisat actually called search. Otherwise we may get segmentation faults. The effect is that if MINISAT_SEARCH_PERIOD > 1 and NOT_IN_PROP_MODEL_DELAY > 0, then we only check if the prop is in the model when we happen to have called minisat to search. ***)
	begin
	  if (!verbosity > 8) then Printf.printf "using prop model to delay working on %d %s\n" mlit (ftm_str m);
	  insertWithPriority (!not_in_prop_model_delay) op
	end
      else
	begin
	  Ftm.processed_add m;
	  if (!verbosity > 8) then Printf.printf "working on %d %s\n" mlit (ftm_str m);
	  process_unprocessed_prop mlit m
	end
    end (*** no else ***)

let rec process_search_option p op =
  match op with
  | ProcessProp1(m) -> (* not treating translucent in Lash (yet?) *)
     process_prop p op m
  | ProcessProp2(m) ->
     process_prop p op m
  | Mating(plit,nlit,a,pargs,nargs) ->
     process_mating plit nlit a pargs nargs
  | MatingList(lit,args,a,l,l_is_pos) -> process_mating_list lit args a l l_is_pos
  | Confront(eqlit,neqlit,a,s,t,u,v) -> confront a eqlit s t neqlit u v
  | ConfrontList(lit,ty,t1,t2,l,l_is_pos) -> confront_list lit ty t1 t2 l l_is_pos
  | DefaultElt(ano) -> ignore (default_elt ano)
  | DefaultEltInst(ano) -> (*** If there are no instantiations of the sort, use the default elt. ***)
      let a = ty_f (mk_base ano) in
      let insts = (get_instantiations a) in
      begin
	match insts with
	| [] -> 
	    let m = default_elt ano in
	    possibly_new_instantiation a m
	| _ -> ()
      end
  | NewInst(a,m) ->
     process_instantiation a m; (*** Must process it now and make it passive ***)
  | EnumInst(a,ns) -> (* generate the nth term and add it as an instantiation *)
     for n = ns to ns + 0 do
       try
         let m = nth_term a (!fiENUM_MASK lxor n) in
         insertWithPriority 500 (NewInst(ty_f a,m));
       with Not_found -> ()
     done;
     insertWithPriority 1000 (EnumInst(a,ns+1)) (* with low priority generate the next one *)
(*   let rec find_return_next n =
       if n = 100 then n
       else match nth_term a (!fiENUM_MASK lxor (ns + n)) with
            | m -> insertWithPriority 500 (NewInst(ty_f a,m)); (n + 1)
            | exception Not_found -> find_return_next (n + 1)
     in
     let next = find_return_next 0 in
     insertWithPriority 1000 (EnumInst(a,ns+next))*)
  | Filter(d) ->
      try
	let d1 = peekAtNext() in (*** peek to make sure there is some other option, use this to delay the next Filter ***)
	(*** Put Filter back on priority queue, with higher delay ( = lower priority) ***)
	let d2 = d1 + (get_int_flag "FILTER_INCR") in
	insertWithPriority d2 (Filter d2);
	if (get_bool_flag "FILTER_UNIV_USABLE") then
          Vector.iter (fun _ l -> List.iter (fun (n,_) -> filterneg n) l) univpreds;
	if (get_bool_flag "FILTER_POSATM_USABLE") then
	  begin
            Vector.iter (fun _ l -> List.iter (fun (n,_) -> filterneg n) l) patoms;
            Vector.iter (fun _ l -> List.iter (fun (n,_) -> filterneg n) l) pchoiceatoms
	  end;
	if (get_bool_flag "FILTER_NEGATM_USABLE") then
	  begin
            Vector.iter (fun _ l -> List.iter (fun (n,_) -> filterneg n) l) natoms;
            Vector.iter (fun _ l -> List.iter (fun (n,_) -> filterneg n) l) nchoiceatoms
	  end;
	if (get_bool_flag "FILTER_POSEQ_USABLE") then
          Vector.iter (fun _ l -> List.iter (fun (n,_,_) -> filterneg n) l) peqns;
	if (get_bool_flag "FILTER_NEGEQ_USABLE") then
          Vector.iter (fun _ l -> List.iter (fun (n,_,_) -> filterneg n) l) neqns;
      with
      | Not_found -> () (*** If this is the only option, quit ***)

let rec search_main () =
  match getNext () with
  | (p, op) ->
     if (!verbosity > 5) then Printf.printf "Option (Priority %d): %s\n" p (searchoption_str op);
     process_search_option p op;
     search_main ()
  (* no more options available *)
  | exception Not_found -> (* print_model_pfterm (); *) minisat_result ()

let pos_heads : (ftm,unit) Hashtbl.t = Hashtbl.create 10
let neg_heads : (ftm,unit) Hashtbl.t = Hashtbl.create 10
let eqn_heads : (ftm,unit) Hashtbl.t = Hashtbl.create 10
let diseqn_heads : (ftm,unit) Hashtbl.t = Hashtbl.create 10

let rec set_relevance_info_tm m =
  match get_tag m with
  | FT_Lam -> set_relevance_info_tm (get_l m)
  | _ ->
     let (h,s) = get_head_spine m in
     match get_tag h with
     | FT_Name ->
        Hashtbl.add diseqn_heads h ();
        ignore (List.map set_relevance_info_tm s)
     | _ -> ()

let rec set_relevance_info m pos =
  match get_tag m with
  | FT_Lam -> set_relevance_info (get_l m) pos
  | FT_All -> set_relevance_info (get_l m) pos
  | FT_Imp -> set_relevance_info (get_l m) (not pos); set_relevance_info (get_r m) pos
  | FT_Eq ->
     begin
       let srtm m =
         let (h,s) = get_head_spine m in
         if get_tag h = FT_Name then
	   if pos then
	     Hashtbl.add eqn_heads h ()
	   else
	     (Hashtbl.add diseqn_heads h ();
	      ignore (List.map set_relevance_info_tm s))
       in
       srtm (get_l m);
       srtm (get_r m);
     end
  | _ ->
     let (h,s) = get_head_spine m in
     if get_tag h = FT_Name then
       begin
         ignore (List.map set_relevance_info_tm s);
	 if pos then
	   Hashtbl.add pos_heads h ()
	 else
	   Hashtbl.add neg_heads h ()
       end
     else
       ()

let rec relevance_delay m pos d =
  if (d <= 0) then
    0
  else
    match get_tag m with
    | FT_Lam -> relevance_delay (get_l m) pos d
    | FT_All -> relevance_delay (get_l m) pos d
    | FT_Imp -> relevance_delay (get_l m) (not pos) (relevance_delay (get_r m) pos d)
    | FT_Eq ->
       begin
         let m1 = get_l m in
         let m2 = get_r m in
	 let h1 = get_head m1 in
	 let d2 =
	   if ((pos && (Hashtbl.mem diseqn_heads h1)) || ((not pos) && (Hashtbl.mem eqn_heads h1))) then
	     d - 1
	   else
	     d
	 in
         let h2 = get_head m2 in
	 if ((pos && (Hashtbl.mem diseqn_heads h2)) || ((not pos) && (Hashtbl.mem eqn_heads h2))) then
	   d2 - 1
	 else
	   d2
       end
    | _ ->
	let h = get_head m in
	if ((pos && (Hashtbl.mem neg_heads h)) || ((not pos) && (Hashtbl.mem pos_heads h))) then
	  d - 1
	else
	  d

let process_and_insert insertfun m =
  let mn = preprocess1 m in
  match fchoiceop_axiom mn with
  | Some(x,a) ->
     if !verbosity > 5 then Printf.printf "choiceop %d at %s\n" x (stp_str a);
     declare_fchoiceop x (ty_f a) mn
  | None ->
     begin
       let skp = ref false in
       let symbreln () =
         match fsymbreln_axiom mn with
         | Some(r,a) ->
            if !verbosity > 5 then Printf.printf "symmetric binary relation %d at %s\n" r (stp_str a);
            declare_fsymbreln r (ty_f a) mn;
            skp := true
         | None -> ()
       in
       let irrefbreln () =
         match firrefbreln_axiom mn with
         | Some(r,a) when not (Hashtbl.mem maxbrelnnames_f r) ->
            if !verbosity > 5 then Printf.printf "irreflexive binary relation %d at %s\n" r (stp_str a);
            declare_firrefbreln r (ty_f a) mn;
            skp := true
         | None -> ()
       in
       let cov1brelns () =
         match fcov1breln_axiom mn with
         | Some(r,a,s) when not (Hashtbl.mem minbrelnnames_f r) ->
            if !verbosity > 5 then Printf.printf "binary relation %d at %s related to %d\n" r (stp_str a) s;
            declare_fcov1breln r (ty_f a) s mn;
            skp := true
         | None -> ()
       in
       let nocl1breln () =
         match fnocl1breln_axiom mn with
         | Some(r,a,l,extras) when not (Hashtbl.mem maxbrelnnames_f r) ->
            if !verbosity > 5 then (Printf.printf "binary relation %d [%s] nocl1 rule :-" r (stp_str a); List.iter (fun (i,j) -> Printf.printf " %d(%d,%d)" r i j) l; Printf.printf ";"; List.iter (fun (i,j) -> Printf.printf " %d(%d,%d)" r i j) extras; Printf.printf "\n");
            declare_fnocl1breln r (ty_f a) l extras;
            skp := true
         | _ -> ()
       in
       symbreln();
       irrefbreln ();
       cov1brelns ();
       nocl1breln();
       if not !skp then
         begin
           insertfun mn;
           let mlit = !get_literal_fn1 mn in
           Hashtbl.add assumption_lit mlit (mn,m);
           new_assumption_lit mlit;
           if !fbINITIAL_SUBTERMS_AS_INSTANTIATIONS then
	     begin
	       if (!verbosity > 4) then Printf.printf "---- Initial Subterms as Instantiations BEGIN ----\n";
	       if (!verbosity > 4) then Printf.printf "---- m = %s ----\n" (ftm_str m);
	       if (!verbosity > 4) then Printf.printf "---- mn = %s ----\n" (ftm_str mn);
	       (try ignore (subterms_as_instantiations [] mn mk_prop) with Not_found -> ());
	       if (!verbosity > 4) then Printf.printf "---- Initial Subterms as Instantiations END ----\n"
	     end
         end
     end

let insert_conjecture mn =
  (*  if get_bool_flag "USE_MODELS" then gen_models mn; *)
  insertWithPriority 0 (ProcessProp1 mn);
  if (get_int_flag "RELEVANCE_DELAY" > 0) then
    set_relevance_info mn false

let insert_axiom mn =
  (*  if get_bool_flag "USE_MODELS" then gen_models mn; *)
  let ad = get_int_flag "AXIOM_DELAY"
  and rd = relevance_delay mn true (get_int_flag "RELEVANCE_DELAY") in
  insertWithPriority (ad + rd) (ProcessProp1 mn)

let insert_filter_command d = insertWithPriority d (Filter d)

let put_ax_on_queue ax =
  let axlit = !get_literal_fn1 ax in
  Hashtbl.add assumption_lit axlit (ax,ax);
  new_assumption_lit axlit;
  insertWithPriority (get_int_flag "AXIOM_DELAY") (ProcessProp1 ax);
  if (!verbosity > 1) then Printf.printf "Putting axiom on queue %s\n" (ftm_str ax)

let should_filter () =
     get_bool_flag "FILTER_UNIV_USABLE"
  || get_bool_flag "FILTER_POSATM_USABLE"
  || get_bool_flag "FILTER_NEGATM_USABLE"
  || get_bool_flag "FILTER_POSEQ_USABLE"
  || get_bool_flag "FILTER_NEGEQ_USABLE"

let search_1 b1 b2 =
  minisatsearchdelay := !fiMINISAT_SEARCH_DELAY;
  minisatsearchperiod := !fiMINISAT_SEARCH_PERIOD;
  minisatsearchperiodfactor := !fiMINISAT_SEARCH_PERIOD_FACTOR;
  let _ = minisat_init (!verbosity) in
  if (!verbosity > 3) then print_endline "Initialized minisat";

  (*** Process "conjecture" part first - March 18 2011 ***)
  List.iter (process_and_insert insert_conjecture) b1;
  (*** Process "axiom" part second - March 18 2011 ***)
  List.iter (process_and_insert insert_axiom) b2;

  if should_filter () then insert_filter_command (get_int_flag "FILTER_START");

  search_main ()

let adapt_timeout s =
  if (s >= 0.2) then (set_timer (s *. 0.5); mult_timeout 0.5)
  else (set_timer s; timeout := Some 0.0)

let handle_binop_ex e r f sgn =
  let go () =
    reset_search_1 ();
    incr sgn;
    Lazy.force f in

  match e with
    | Unsatisfiable(Some(r1)) ->
      begin
        try go ()
        with Unsatisfiable(Some(r2)) -> raise (Unsatisfiable (Some (r r1 r2)))
      end
     | Unsatisfiable(None) -> go ()
     | Timeout ->
        if (!nontheorem) then
        begin
          let s = get_timeout_default 0.0 in
          if s < 0.0 then raise Timeout;
          adapt_timeout s;
          go ()
        end
        else raise Timeout
     | e -> raise e

let rec split_global_disjunctions b1 b2 b bs sgn cnj =
  if !sgn >= !fiSPLIT_GLOBAL_DISJUNCTIONS_LIMIT then
    begin
      if (!verbosity > 5) then Printf.printf "Searching on Subgoal %d\n" (!sgn);
      if cnj then
	search_1 (b1 @ b) b2 (* never got to processing b2 (axiom part), so bs is empty and b1 and b are conj parts *)
      else
	search_1 bs (b1 @ b) (* finished processing conj part (saved in bs), b2 must be empty and b1 and b are axiom parts *) (*** reversed conjecture and axiom parts to compute axiom parts ***)
    end
  else
    match b1 with
      (m::pr) ->
       begin
         match get_tag m with
         | FT_Imp ->
            let m1 = get_l m in
            let m2 = get_r m in
            if m2 = mk_false then
              begin
                match get_tag m1 with
                | FT_Eq ->
                   if get_l m1 = get_r m1 then
	             if (mkprooftermp ()) then
	               raise (Unsatisfiable (Some (fun () -> NegReflR (m,ftm_trm name_tp [] m1))))
	             else
	               raise (Unsatisfiable None)
                   else
                     begin
                       let aa = ty_f_rev (get_no m1) in
                       if is_ar aa then
                         let a1 = ty_get_l aa in
                         let a2 = ty_get_r aa in
		         begin (** no need to shift since no dangling de Bruijns *)
                           let m2 = get_r m1 in
                           let m1 = get_l m1 in
                           let mnew = mk_neg (mk_all (ty_f a1) (mk_norm_eq (ty_f a2) (mk_norm_ap m1 (mk_db 0)) (mk_norm_ap m2 (mk_db 0)))) in
		           try
		             split_global_disjunctions
                               (mnew::pr)
		               b2 b bs sgn cnj
		           with
		           | Unsatisfiable(Some(r1)) ->
		              raise (Unsatisfiable (Some (fun () -> NegEqFR(a1,a2,m,mnew,ftm_trm name_tp [] m1,ftm_trm name_tp [] m2,r1 ()))))
		         end
                       else if aa = mk_prop && !fbSPLIT_GLOBAL_DISJUNCTIONS_EQO then
		         begin
                           let m2 = get_r m1 in
                           let m1 = get_l m1 in
		           try
		             split_global_disjunctions (m1::(fneg m2)::pr) b2 b bs sgn cnj
		           with
		           | Unsatisfiable(Some(r1)) ->
		              begin
		                try
			          reset_search_1 (); incr sgn;
			          split_global_disjunctions ((fneg m1)::m2::pr) b2 b bs sgn cnj
		                with
		                | Unsatisfiable(Some(r2)) ->
			           raise (Unsatisfiable (Some (fun () -> NegEqOR(m,m1,m2,ftm_trm name_tp [] m1,ftm_trm name_tp [] m2,r1 (),r2 ()))))
		              end
		           | Unsatisfiable(None) ->
		              reset_search_1 (); incr sgn;
		              split_global_disjunctions ((fneg m1)::m2::pr) b2 b bs sgn cnj
		           | Timeout ->
		              if (!nontheorem) then
		                begin
			          let s = get_timeout_default 0.0 in
			          if (s >= 0.2) then
			            begin
			              set_timer (s *. 0.5);
			              mult_timeout 0.5;
			              reset_search_1 (); incr sgn;
			              split_global_disjunctions ((fneg m1)::m2::pr) b2 b bs sgn cnj
			            end
			          else if (s >= 0.0) then
			            begin
			              set_timer s;
			              timeout := Some 0.0;
			              reset_search_1 (); incr sgn;
			              split_global_disjunctions ((fneg m1)::m2::pr) b2 b bs sgn cnj
			            end
			          else raise Timeout
		                end
		              else
		                raise Timeout
		         end
                       else
                         split_global_disjunctions pr b2 (m::b) bs sgn cnj
                     end
                | FT_All ->
                   let a = get_no m1 in
                   let m1b = get_l m1 in
	           let (ws,w) = get_fresh_name (ty_f_rev a) in
	           if (!verbosity > 5) then begin print_string("Using Fresh Witness " ^ (ftm_str w) ^ " of type " ^ (stp_str (ty_f_rev a))); print_newline(); flush stdout end;
	           process_new_name a w (get_int_flag "NEW_HEAD_ENUM_DELAY");
	           let m1w = Ftm.subst m1b 0 w in
	           if (!verbosity > 8) then (print_string(" m1w = " ^ (ftm_str m1w)); print_newline());
	           let nm1w = fneg m1w in
	           if (!verbosity > 8) then (print_string(" nm1w = " ^ (ftm_str nm1w)); print_newline());
	           begin
		     try
		       split_global_disjunctions (nm1w::pr) b2 b bs sgn cnj
		     with
		     | Unsatisfiable(Some(r1)) ->
		        raise (Unsatisfiable(Some(fun () -> let a2 = ty_f_rev a in NegAllR(a2,m,nm1w,Lam(a2,ftm_trm name_tp [a2] m1b),ws,r1 ()))))
	           end
                | FT_False ->
                   split_global_disjunctions pr b2 b bs sgn cnj (*** drop ~False ***)
                | FT_Imp ->
                   let m2 = get_r m1 in
                   let m1 = get_l m1 in
	           begin
	             try
	               split_global_disjunctions (m1::(fneg m2)::pr) b2 b bs sgn cnj
	             with
	             | Unsatisfiable(Some(r1)) ->
		        raise (Unsatisfiable (Some (fun () -> NegImpR(m,m1,fneg m2,ftm_trm name_tp [] m1,ftm_trm name_tp [] m2,r1 ()))))
	           end
                | _ -> split_global_disjunctions pr b2 (m::b) bs sgn cnj
              end
            else if !fbSPLIT_GLOBAL_DISJUNCTIONS_IMP then
              begin
	        try
		  split_global_disjunctions (m2::pr) b2 b bs sgn cnj
                with
	        | Unsatisfiable(Some(r1)) ->
		   begin
		     try
		       reset_search_1 (); incr sgn;
		       split_global_disjunctions ((fneg m1)::pr) b2 b bs sgn cnj
                     with
		     | Unsatisfiable(Some(r2)) ->
		        raise (Unsatisfiable (Some (fun () -> ImpR(m,fneg m1,m2,ftm_trm name_tp [] m1,ftm_trm name_tp [] m2,r2 (),r1 ()))))
		   end
	        | Unsatisfiable(None) ->
		   reset_search_1 (); incr sgn;
		   split_global_disjunctions ((fneg m1)::pr) b2 b bs sgn cnj
	        | Timeout ->
		   if (!nontheorem) then
		     begin
		       let s = get_timeout_default 0.0 in
		       if (s >= 0.2) then
		         begin
			   set_timer (s *. 0.5);
			   mult_timeout 0.5;
			   reset_search_1 (); incr sgn;
			   split_global_disjunctions ((fneg m1)::pr) b2 b bs sgn cnj
		         end
		       else if (s >= 0.0) then
		         begin
			   set_timer s;
			   timeout := Some 0.0;
			   reset_search_1 (); incr sgn;
			   split_global_disjunctions ((fneg m1)::pr) b2 b bs sgn cnj
		         end
		       else raise Timeout
		     end
		   else
		     raise Timeout
              end
            else
              split_global_disjunctions pr b2 (m::b) bs sgn cnj
         | FT_Eq ->
            if !fbSPLIT_GLOBAL_DISJUNCTIONS_EQO && ty_f_rev (get_no m) = mk_prop then
              begin
                let m1 = get_l m in
                let m2 = get_r m in
	        try
		  split_global_disjunctions (m1::m2::pr) b2 b bs sgn cnj
	        with
	        | Unsatisfiable(Some(r1)) ->
		   begin
		     try
		       reset_search_1 (); incr sgn;
		       split_global_disjunctions ((fneg m1)::(fneg m2)::pr) b2 b bs sgn cnj
		     with
		     | Unsatisfiable(Some(r2)) ->
		        raise (Unsatisfiable (Some (fun () -> EqOR(m,m1,m2,ftm_trm name_tp [] m1,ftm_trm name_tp [] m2,r1 (),r2 ()))))
                   end
                | Unsatisfiable(None) ->
		   reset_search_1 (); incr sgn;
		   split_global_disjunctions ((fneg m1)::(fneg m2)::pr) b2 b bs sgn cnj
              end
            else
              split_global_disjunctions pr b2 (m::b) bs sgn cnj
         | _ -> split_global_disjunctions pr b2 (m::b) bs sgn cnj
       end
    | [] ->
       begin
	 match b2 with
	   (_::_) -> split_global_disjunctions b2 [] [] b sgn false
	 | [] ->
	    begin
	      if (!verbosity > 5) then Printf.printf "Searching on Subgoal %d\n" (!sgn);
	      if cnj then
		search_1 b bs
	      else
		search_1 bs b (*** reversed conjecture and axiom parts to compute axiom parts ***)
	    end
       end
      
(*** Following Andreas Teucke's suggestion: Preprocess before split - Mar 18 2011 ***)
let preprocess_before_split b1 b2 =
  let pbr1 = List.map preprocess1 b1 in
  let pbr2 = List.map preprocess1 b2 in
  already_preprocessed := true;
  (pbr1, pbr2)

let search_split_global_disjs b1 b2 =
  let (b1', b2') = match get_bool_flag "PREPROCESS_BEFORE_SPLIT" with
      true  -> preprocess_before_split b1 b2
    | false -> (b1, b2) in
  split_global_disjunctions b1' b2' [] [] (ref 1) true

let split_conjecture_axioms ms =
  if get_bool_flag "TREAT_CONJECTURE_AS_SPECIAL"
  then List.partition (fun m -> Hashtbl.mem part_of_conjecture m) (List.rev ms) (* reversal is essential, otherwise speed can be halved! (apparently) *)
  else ([], ms)

let search () =

  let d_const = get_int_flag "IMITATE_DELAY" in
  let d_def = get_int_flag "IMITATE_DEFN_DELAY" in
  let i_def = get_bool_flag "IMITATE_DEFNS" in
  List.iter
    (fun (x,m,sigma) ->
      let (sigmal,rtp) = argtps_rtp sigma in
      if (Hashtbl.mem name_def_f x) then
	begin
	  if i_def then
	    new_usable_head_rtp rtp sigmal m d_def
	end
      else
	new_usable_head_rtp rtp sigmal m d_const)
    !name_trm_list;
  
  (*  setup_pattern_clauses (); *)
  (* setup_basetypes (); *)
  (*  setup_prop_model_delay (); *)

  search_init ();

  begin (*** Chad: Nov 2011 ***)
    not_in_prop_model_delay := get_int_flag "NOT_IN_PROP_MODEL_DELAY";
    not_in_prop_model_delay_p := (!not_in_prop_model_delay > 0)
  end;

  (*** split branch into conjecture part (b1) and axiom part (b2) ***)
  let (b1, b2) = split_conjecture_axioms !initial_branch in
  if get_bool_flag "SPLIT_GLOBAL_DISJUNCTIONS"
  then search_split_global_disjs b1 b2
  else search_1 b1 b2

