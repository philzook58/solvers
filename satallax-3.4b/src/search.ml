(* File: search.ml *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open Flags
open State
open Syntax
open Match
open Minisat
open Minisatinterface
open Refut
open Atom
open Log
open Searchoption
open Error
open Big_int
open Models
open Patternclause

let enable_pattern_clauses = ref false;;
let dynamic_pattern_clauses = ref false;;
let apply_pattern_clauses_early = ref false;;

let filterp lit =
  begin
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
  end

let filteredp lit = Hashtbl.mem filtered lit

let filter lit =
  if (not (filteredp lit)) then
    if (filterp lit) then
      Hashtbl.add filtered lit () (*** The literal cannot be true. ***)

let filterneg lit = filter (- lit)

let pattern_clauses_transitivity_types : (stp,unit) Hashtbl.t = Hashtbl.create 10

let not_in_prop_model_delay_p : bool ref = ref false (*** Nov 2011 ***)
let not_in_prop_model_delay : int ref = ref 0        (*** Nov 2011 ***)




let get_literal_fn1 : (trm -> int) ref = ref get_literal
let get_literal_fn2 : (trm -> int) ref = ref get_literal

(*** Dec 2012: Make pattern clauses when the formula is assigned a literal. ***)
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

let nonforall_pattern_clauses_usable : bool ref = ref false

(*** Nov 2015: In addition to making the pattern clause when the minisat literal is created, apply it to the pattern clauses that already exist. ***)
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

let sym_eq_clauses_1 mlit msymlit a m1 m2 =
  let symab = Lam(a,forall a (imp (eq a (DB(1,a)) (DB(0,a))) (eq a (DB(0,a)) (DB(1,a))))) in
  let syma = Ap(Forall(a),symab) in
  let symalit = get_literal syma in
  let syma2b = Lam(a,imp (eq a (shift m1 0 1) (DB(0,a))) (eq a (DB(0,a)) (shift m1 0 1))) in
  let syma2 = Ap(Forall(a),syma2b) in
  let syma2lit = get_literal syma2 in
  let syma3 = imp (eq a m1 m2) (eq a m2 m1) in
  let syma3lit = get_literal syma3 in
  new_search_clause [symalit] (if (mkprooftermp ()) then (Some (Known(symalit,coqknown("@eq_sym","eq_sym"),[a]))) else None);
  new_search_clause [(-symalit);syma2lit] (if (mkprooftermp ()) then (Some (InstRule(a,symab,m1))) else None);
  new_search_clause [(-syma2lit);syma3lit] (if (mkprooftermp ()) then (Some (InstRule(a,syma2b,m2))) else None);
  new_search_clause [(-syma3lit);(-mlit);msymlit] (if (mkprooftermp ()) then (Some (PosPropRule(syma3))) else None)

let sym_eq_clauses mlit a m1 m2 =
  let msym = eq a m2 m1 in
  let msymlit = get_literal msym in
  sym_eq_clauses_1 mlit msymlit a m1 m2;
  sym_eq_clauses_1 msymlit mlit a m2 m1

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

let seen_instantiations : ((stp * trm),unit) Hashtbl.t = Hashtbl.create 10

let seen_inst_p a m =
  Hashtbl.mem seen_instantiations (a,m)

let see_inst a m =
  Hashtbl.add seen_instantiations (a,m) ()

let reset_search_1 () =
  reset_search();
  Hashtbl.clear seen_instantiations

let rec stp_weight a =
  match a with
  | Ar(a1,a2) -> !fiARTP_WEIGHT + (stp_weight a1) + (stp_weight a2)
  | Base(_) -> !fiBASETP_WEIGHT
  | Prop -> !fiOTP_WEIGHT

let rec tm_weight m =
  match m with
  | Name(_,a) ->
    let fac = get_int_flag "NAME_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "NAME_WEIGHT") + (fac * (stp_weight a))
      else
	get_int_flag "NAME_WEIGHT"
    end
  | False -> get_int_flag "FALSE_WEIGHT"
  | Imp -> (get_int_flag "IMP_WEIGHT")
  | Forall(a) ->
    let fac = get_int_flag "FORALL_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "FORALL_WEIGHT") + (fac * (stp_weight a))
      else
	(get_int_flag "FORALL_WEIGHT")
    end
  | Eq(a) ->
    let fac = get_int_flag "EQ_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "EQ_WEIGHT") + (fac * (stp_weight a))
      else
	(get_int_flag "EQ_WEIGHT")
    end
  | Choice(a) ->
    let fac = get_int_flag "CHOICE_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "CHOICE_WEIGHT") + (fac * (stp_weight a))
      else
	(get_int_flag "CHOICE_WEIGHT")
    end
  | DB(i,a) ->
    let fac = get_int_flag "DB_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "DB_WEIGHT") + (fac * (stp_weight a))
      else
	(get_int_flag "DB_WEIGHT")
    end
  | Lam(a,m) ->
    let fac = get_int_flag "LAM_TP_WEIGHT_FAC" in
    begin
      if (fac > 0) then
	(get_int_flag "LAM_WEIGHT") + (fac * (stp_weight a))
      else
	(get_int_flag "LAM_WEIGHT")
    end
  | Ap(m1,m2) ->
    (get_int_flag "AP_WEIGHT") + (tm_weight m1) + (tm_weight m2)
  | _ -> 0

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

let instantiation_priority a m =
  (get_int_flag "INSTANTIATION_DELAY") + (stp_weight a) + (tm_weight m)

let process_instantiation a m =
  begin (*** Process it now -- making it passive ***)
    add_instantiation a m;
    List.iter
      (fun (lit,p) -> (*** Instantiate known universal predicates ***)
	if not (filteredp (-lit)) then
	  let pm = (norm name_def (ap(p,m))) in
	  insertWithPriority (get_int_flag "FORALL_DELAY") (ProcessProp1 pm);
	  let pmlit = !get_literal_fn2 pm in
	  new_search_clause [lit;pmlit]
	    (if (mkprooftermp ()) then (Some(InstRule(a,p,m))) else None)
	    )
      (Hashtbl.find_all univpreds a)
  end

let new_active_instantiation a m =
  if (insane_instance_p m) then (*** Always leave insane instantiations active with a very high priority when we first see them. ***)
    begin
      if (!verbosity > 40) then (Printf.printf "Delaying insane instantiation %s\n" (trm_str m));
      insertWithPriority 5000 (NewInst(a,m)) (*** Delay it for a very long time, leaving it active ***)
    end
  else if (get_bool_flag "EAGERLY_PROCESS_INSTANTIATIONS") then (*** Process it now -- making it passive ***)
    process_instantiation a m
  else (*** Determine priority and put it on the queue (active instantiation) ***)
    let d = instantiation_priority a m in
    begin
      if (!verbosity > 20) then (Printf.printf "Delaying with priority %d active instantiation %s\n" d (trm_str m));
      insertWithPriority d (NewInst(a,m))
    end

let possibly_new_instantiation a m =
  if (not (seen_inst_p a m)) then
    let um = get_bool_flag "USE_MODELS" in
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
            if (!verbosity > 5) then (Printf.printf "Delaying instantiation %d due to semantic equiv %s:" semdelay (trm_str m); List.iter (fun v -> Printf.printf " %s" v) !vl; Printf.printf "\n");
            insertWithPriority semdelay (NewInst(a,m))
          end
        else
          begin
            if (!verbosity > 5) then (Printf.printf "Instantiation with new semantic equiv class %s:" (trm_str m); List.iter (fun v -> Printf.printf " %s" v) !vl; Printf.printf "\n");
            see_inst a m;
            new_active_instantiation a m
          end
      end
    else
      begin
	if !verbosity > 5 then (Printf.printf "New instantiation: %s\n" (trm_str m); Printf.printf "\n"; flush stdout);
        see_inst a m;
        new_active_instantiation a m
      end
  else if (!verbosity > 5) then
    begin
      Printf.printf "not really new inst %s\n" (trm_str m)
    end

let process_new_name a m d =
  let (sigmal,ar) = argtps_rtp a in
  new_usable_head_rtp ar sigmal m d;
  iter_term_continuations_rtp ar sigmal m d

let process_new_type ar a d =
  new_usable_type_rtp ar a d;
  iter_type_continuations_rtp ar a d

let negimp_rule mlit m m1 m2 =
  let r = if (mkprooftermp ()) then (Some(NegPropRule(m))) else None in
  insertWithPriority (get_int_flag "POST_NOR_L_DELAY") (ProcessProp1 m1);
  insertWithPriority (get_int_flag "POST_NOR_R_DELAY") (ProcessProp1 (normneg m2));
  let m1lit = !get_literal_fn2 m1 in
  let nm2lit = !get_literal_fn2 (normneg m2) in
  new_search_clause [-mlit;m1lit] r;
  new_search_clause [-mlit;nm2lit] r

let imp_rule mlit m m1 m2 =
  let r = if (mkprooftermp ()) then (Some(PosPropRule(m))) else None in
  insertWithPriority (get_int_flag "POST_OR_L_DELAY") (ProcessProp1 (normneg m1));
  insertWithPriority (get_int_flag "POST_OR_R_DELAY") (ProcessProp1 m2);
  let nm1lit = !get_literal_fn2 (normneg m1) in
  let m2lit = !get_literal_fn2 m2 in
  new_search_clause [(-mlit);nm1lit;m2lit] r

let forall_rule nmlit a m1 w =
  let m1w = (norm name_def (ap(m1,w))) in
  insertWithPriority (get_int_flag "FORALL_DELAY") (ProcessProp1 m1w);
  let m1wlit = !get_literal_fn2 m1w in
  new_search_clause [nmlit;m1wlit]
    (if (mkprooftermp ()) then (Some(InstRule(a,m1,w))) else None);
  m1w

let negforall_rule mlit a m1 =
  let (ws,w) = get_fresh_name a in
  if (!verbosity > 4) then begin print_string("Using Fresh Witness " ^ (trm_str w)); print_newline(); flush stdout end;
  process_new_name a w (get_int_flag "NEW_HEAD_ENUM_DELAY");
  let m1w = (norm name_def (ap(m1,w))) in
  if (!verbosity > 8) then begin print_string(" m1w = " ^ (trm_str m1w)); print_newline(); flush stdout end;
  let nm1w = normneg m1w in
  if get_bool_flag "USE_MODELS" then extend_models nm1w;
  insertWithPriority (get_int_flag "EXISTS_DELAY") (ProcessProp1 nm1w);
  let nm1wlit = !get_literal_fn2 nm1w in
  new_search_clause [-mlit;nm1wlit]
    (if (mkprooftermp ()) then (Some(FreshRule(a,m1,ws))) else None);
  nm1w

let decompose lit largs rargs r =
  let delay = get_int_flag "POST_DEC_DELAY" in
  let dlits = List.map2
      (fun la ra ->
	let deq = normneg (ueq la ra) in
	insertWithPriority delay (ProcessProp1 deq);
	!get_literal_fn2 deq
      )
      largs rargs
  in
  new_search_clause ((-lit)::dlits) r

let consider_confrontation a neqlit u v eqlit s t =
  let op = Confront(eqlit,neqlit,a,s,t,u,v) in
  let (sh,_) = head_spine s in
  let (th,_) = head_spine t in
  let (uh,_) = head_spine u in
  let (vh,_) = head_spine v in
  let delay =
    if (((sh = uh) && (th = vh)) || ((sh = vh) && (th = uh))) then
      !fiCONFR_SAME2_DELAY
    else if ((sh = uh) || (th = vh) || (sh = vh) || (th = uh)) then
      !fiCONFR_SAME1_DELAY
    else
      !fiCONFR_DIFF_DELAY
  in
  insertWithPriority delay op

let confront a eqlit s t neqlit u v =
  if (!verbosity > 9) then Printf.printf "Confront %d %d\n" eqlit neqlit;
  let r = if (mkprooftermp ()) then (Some (ConfrontationRule(eqlit,neqlit))) else None in
  let minuseqlit = (- eqlit) in
  let minusneqlit = (- neqlit) in
  let su = (eq a s u) in
  let tu = (eq a t u) in
  let sv = (eq a s v) in
  let tv = (eq a t v) in
  let msulit = (- (!get_literal_fn2 su)) in
  let mtulit = (- (!get_literal_fn2 tu)) in
  let msvlit = (- (!get_literal_fn2 sv)) in
  let mtvlit = (- (!get_literal_fn2 tv)) in
  let nsu = neg su in
  let nsv = neg tu in
  let ntu = neg sv in
  let ntv = neg tv in
  insertWithPriority (!fiPOST_CONFRONT1_DELAY) (ProcessProp1 nsu);
  insertWithPriority (!fiPOST_CONFRONT2_DELAY) (ProcessProp1 ntu);
  insertWithPriority (!fiPOST_CONFRONT3_DELAY) (ProcessProp1 nsv);
  insertWithPriority (!fiPOST_CONFRONT4_DELAY) (ProcessProp1 ntv);
  new_search_clause [minuseqlit;minusneqlit;msulit;msvlit] r;
  new_search_clause [minuseqlit;minusneqlit;msulit;mtvlit] r;
  new_search_clause [minuseqlit;minusneqlit;mtulit;msvlit] r;
  new_search_clause [minuseqlit;minusneqlit;mtulit;mtvlit] r;
  [nsu;nsv;ntu;ntv]

let mate plit nlit pargs nargs =
  let pmd = get_int_flag "POST_MATING_DELAY" in
  let deqs = ref [] in
  let dlits = List.map2
      (fun pa na ->
	let deq = normneg (ueq pa na) in
	deqs := deq::!deqs;
	insertWithPriority pmd (ProcessProp1 deq);
	!get_literal_fn2 deq
	  )
      pargs nargs
  in
  new_search_clause
    ((-plit)::(-nlit)::dlits)
    (if (mkprooftermp ()) then (Some (MatingRule(plit,nlit))) else None);
  !deqs

let choice_rule h args =
  match (choiceop h) with
  | Some(a) ->
      begin
	match args with
	| (pred::_) ->
	    let m1 = norm name_def (ap(pred,ap(h,pred))) in
	    let m2 = norm name_def (forall a (normneg (ap(shift pred 1 0,DB(0,a))))) in
	    insertWithPriority (get_int_flag "CHOICE_EMPTY_DELAY") (ProcessProp1 m2);
	    insertWithPriority (get_int_flag "CHOICE_IN_DELAY") (ProcessProp1 m1);
	    new_search_clause [!get_literal_fn2 m1;!get_literal_fn2 m2] (if (mkprooftermp ()) then (Some(ChoiceRule(h,pred))) else None)
	| _ -> raise (GenericError "Choice operator must be applied to at least one argument")
      end
  | None -> ()  

let rec enum_projections pd d gamma gammal i a c =
  match gammal with
  | (sigma::gammar) ->
      begin
	let (sigmal,b) = argtps_rtp sigma in
	begin
	  if (a = b) then
	    begin
	      insertWithPriority pd (EnumAp(d,gamma,sigmal,DB(i,sigma),c))
	    end;
	end;
	enum_projections pd d gamma gammar (i + 1) a c
      end
  | [] -> ()

let rec subterms_as_instantiations m n =
  match m with
  | Ap(m1,m2) ->
      let (ab,h1) = subterms_as_instantiations m1 n in
      begin
	match ab with
	| Ar(a,b) -> 
	    begin
	      let h2 = subterms_as_instantiations_n m2 a n in
	      if (((Hashtbl.length h1) = 0) && ((Hashtbl.length h2) = 0)) then
		possibly_new_instantiation b m;
	      Hashtbl.iter (fun i _ -> if (not (Hashtbl.mem h1 i)) then Hashtbl.add h1 i ()) h2;
	      (b,h1)
	    end
	| _ -> raise (GenericError ((trm_str m) ^ " is ill-typed (in subterms_as_instantiations)"))
      end
  | Name(x,a) ->
      possibly_new_instantiation a m;
      (a,Hashtbl.create 10)
  | DB(i,a) ->
      let h = Hashtbl.create 10 in
      Hashtbl.add h (n - i) ();
      (a,h)
  | Lam(_,_) -> raise (GenericError ((trm_str m) ^ " expected to have base type in subterms_as_instantiations"))
(*** Don't use logical constants as instantiations ***)
  | _ -> (tpof m,Hashtbl.create 10)
and subterms_as_instantiations_n m a n =
  match (m,a) with
  | (Lam(b,m1),Ar(a1,a2)) -> (*** when (b = a1) ->, assume this holds ***)
      begin
	let h1 = subterms_as_instantiations_n m1 a2 (n + 1) in
	Hashtbl.remove h1 (n + 1);
	if ((Hashtbl.length h1) = 0) then
	  possibly_new_instantiation a m;
	h1
      end
  | _ -> let (b,h) = subterms_as_instantiations m n in h

(***
 Convert some HO versions of equality to primitive equality:
 !p.p s -> p t becomes s = t
 !r.(!x.rxx) -> rst becomes s = t
 ***)
let is_an_eqn m =
  match m with
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap (Ap (Imp, Ap (DB (0, Ar (_, Prop)), s)),
		 Ap (DB (0, Ar (_, Prop)), t))))
      when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    -> (a,shift s 0 (- 1),shift t 0 (- 1))
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap
	       (Ap (Imp,
		    Ap (Ap (Imp, Ap (DB (0, Ar (_, Prop)), s)),
			False)),
		Ap (Ap (Imp, Ap (DB (0, Ar (_, Prop)), t)),
		    False))))
    when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    -> (a,shift s 0 (- 1),shift t 0 (- 1))
  | Ap (Forall (Ar (a, Ar (_, Prop))),
	Lam (Ar (_, Ar (_, Prop)),
	     Ap
	       (Ap (Imp,
		    Ap (Forall (_),
			Lam (_,
			     Ap (Ap (DB (1, Ar (_, Ar (_, Prop))), DB (0, _)),
				 DB (0, _))))),
		Ap (Ap (DB (0, Ar (_, Ar (_, Prop))), s),
		    t))))
    when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    -> (a,shift s 0 (- 1),shift t 0 (- 1))
  | Ap (Forall (Ar (a, Ar (_, Prop))),
	Lam (Ar (_, Ar (_, Prop)),
	     Ap
	       (Ap (Imp,
		    Ap
		      (Ap (Imp,
			   Ap
			     (Ap (DB (0, Ar (_, Ar (_, Prop))),
				  s),
			      t)),
		       False)),
		Ap
		  (Ap (Imp,
		       Ap (Forall (_),
			   Lam (_,
				Ap
				  (Ap (DB (1, Ar (_, Ar (_, Prop))), DB (0, _)),
				   DB (0, _))))),
		   False))))
    when ((termNotFreeIn s 0) && (termNotFreeIn t 0))
    -> (a,shift s 0 (- 1),shift t 0 (- 1))
  | _ -> raise Not_found (*** It's not an equation. ***)

let rec leibeq_to_primeq m =
  try
    let (a,s,t) = is_an_eqn m in eq a (leibeq_to_primeq s) (leibeq_to_primeq t) (*** added the recursive calls here so it hopefully behaves like Andreas Teucke's version in proofterm.  - Chad, Feb 15, 2011 ***)
  with
  | Not_found ->
      begin
	match m with
	| Ap(m1,m2) -> Ap(leibeq_to_primeq m1,leibeq_to_primeq m2)
	| Lam(a1,m1) -> Lam(a1,leibeq_to_primeq m1)
	| _ -> m
      end

(*** Enumeration of types can be preserved across subgoals.  The types are global. ***)
let typesgenerated = ref 0  

let typesofdepth : (int,stp) Hashtbl.t = Hashtbl.create 3

let generate_type d a =
  if (!verbosity > 9) then (Printf.printf "Generated type %s of depth %d\n" (stp_str a) d; flush stdout);
  Hashtbl.add typesofdepth d a

(*** Assume all types of depth < d are known.  Generate all those of depth d. ***)
let generate_types d =
  if (!verbosity > 9) then (Printf.printf "Generate types called with depth %d\n" d; flush stdout);
  if (d = (get_int_flag "ENUM_O")) then generate_type d Prop;
  if (d = (get_int_flag "ENUM_SORT")) then
    (List.iter (fun a -> generate_type d (Base(a))) !name_base_list);
  let dm = d - 1 - (get_int_flag "ENUM_ARROW") in
  if (dm >= 0) then
    begin
      for i = 0 to dm
      do
	List.iter
	  (fun ai ->
	    List.iter
	      (fun aj ->
		generate_type d (Ar(ai,aj)))
	      (Hashtbl.find_all typesofdepth (dm - i)))
	  (Hashtbl.find_all typesofdepth i)
      done
    end

let rec enum_depth d ctx a =
  if (!verbosity > 9) then Printf.printf "enum_depth %d for type %s\n" d (stp_str a);
  match a with
  | Ar(a1,a2) -> List.map (fun m -> Lam(a1,m)) (enum_depth d (a1::ctx) a2)
  | _ ->
      if (d > 0) then
	begin
	  let r = ref [] in
	  ignore (enum_depth_proj (d - 1) ctx ctx a 0 r);  (*** - 1 here ensures termination ***)
	  enum_depth_imit (d - 1) ctx a r; (*** - 1 here ensures termination ***)
	  (!r)
	end
      else []
and enum_depth_proj d ctx origctx a i r =
  if (!verbosity > 9) then Printf.printf "enum_depth_proj %d for type %s i = %d\n" d (stp_str a) i;
  match ctx with
  | (sigma::ctx') ->
      begin
	let (sigmal,b) = argtps_rtp sigma in
	begin
	  if (a = b) then
	    begin
	      enum_depth_spine (d - (get_int_flag "PROJECT_DELAY")) origctx sigmal (DB(i,sigma)) r
	    end
	end;
	enum_depth_proj d ctx' origctx a (i + 1) r
      end
  | _ -> []
and enum_depth_imit d ctx a r =
  if (!verbosity > 9) then Printf.printf "enum_depth_imit %d for type %s\n" d (stp_str a);
  (*** Imitations ***)
  (List.iter
     (fun (sigmal,h,pimit) ->
       enum_depth_spine (d - pimit) ctx sigmal h r
     )
     (usable_heads_rtp a));
  let pneg = get_int_flag "ENUM_NEG" in
  let pimp = get_int_flag "ENUM_IMP" in
  let pfalse = get_int_flag "ENUM_FALSE" in
  let pforall = get_int_flag "ENUM_FORALL" in
  let peq = get_int_flag "ENUM_EQ" in
  let pchoice = get_int_flag "ENUM_CHOICE" in
  (*** Polymorphic Logical Constants ***)
  for i = 0 to (d - 1)
  do
    List.iter
      (fun sigma ->
	let (sigmal,b) = argtps_rtp sigma in
	if (a = b) then
	  enum_depth_spine (d - (i + pchoice)) ctx ((Ar(sigma,Prop))::sigmal) (Choice(sigma)) r;
	if (a = Prop) then
	    begin
	      enum_depth_spine (d - (i + pforall)) ctx [Ar(sigma,Prop)] (Forall(sigma)) r;
	      enum_depth_spine (d - (i + peq)) ctx [sigma;sigma] (Eq(sigma)) r;
	    end;
	)
      (Hashtbl.find_all typesofdepth i)
  done;
  if (a = Prop) then
    begin
      (*** Neg, Imp, False ***)
      enum_depth_spine (d - pneg) ctx [Prop] (Lam(Prop,Ap(Ap(Imp,DB(0,Prop)),False))) r;
      enum_depth_spine (d - pimp) ctx [Prop;Prop] (Imp) r;
      enum_depth_spine (d - pfalse) ctx [] (False) r;
    end
and enum_depth_spine d ctx sigmal h r =
  if (!verbosity > 9) then Printf.printf "enum_depth_spine %d %s\n" d (trm_str h);
  match sigmal with
  | (a::sigmal') ->
      List.iter
	(fun m -> enum_depth_spine d ctx sigmal' (Ap(h,m)) r)
	(enum_depth d ctx a)
  | [] ->
      if (d >= 0) then
	let m = norm name_def h in
	if (!verbosity > 9) then Printf.printf "enum_depth_spine finished with %s\n" (trm_str m);
	r := (m::!r)

(*** Finiteness Assumptions - Apr 2012 ***)
let stp_finite_elts : (stp,trm list) Hashtbl.t = Hashtbl.create 9
let stp_finite_sings : (stp,trm list) Hashtbl.t = Hashtbl.create 9
let stp_finite_axs : (stp,trm list) Hashtbl.t = Hashtbl.create 9

let rec finite_base_type_r a n el sl cov =
  if (n > 0) then
    let (ename,e) = get_fresh_name a in
    let ep = Ap(Ap(Eq(a),DB(0,a)),e) in
    if (!verbosity > 1) then Printf.printf "New Generating elt %s of finite type %s satisfying\n%s\n" ename (stp_str a) (trm_str ep);
    finite_base_type_r a (n - 1) (e::el) ((Lam(a,ep))::sl) (disj ep cov)
  else
    (el,sl,cov)

let finite_base_type x n =
  let a = Base x in
  let (ename,e) = get_fresh_name a in
  let ep = Ap(Ap(Eq(a),DB(0,a)),e) in
  if (!verbosity > 1) then Printf.printf "New Generating elt %s of finite type %s satisfying\n%s\n" ename x (trm_str ep);
  let (el,sl,cov) = finite_base_type_r a (n - 1) [e] [Lam(a,ep)] ep in
  if (!verbosity > 1) then Printf.printf "Coverage Property of finite type %s\n%s\n" x (trm_str cov);
  Hashtbl.add stp_finite_elts a el;
  Hashtbl.add stp_finite_sings a sl;
  Hashtbl.add stp_finite_axs a [forall a cov]

let rec finite_func_type_1 a domelts codsings fsing =
  match domelts with
  | (domelt::domelts) -> finite_func_type_2 a domelt domelts codsings codsings fsing
  | [] ->
    begin
      let felts = Hashtbl.find stp_finite_elts a in
      let fsings = Hashtbl.find stp_finite_sings a in
      let faxs = Hashtbl.find stp_finite_axs a in
      let (ename,e) = get_fresh_name a in
      if (!verbosity > 1) then Printf.printf "New Generating elt %s of finite type %s satisfying\n%s\n" ename (stp_str a) (trm_str fsing);
      Hashtbl.add stp_finite_elts a (e::felts);
      Hashtbl.add stp_finite_sings a (Lam(a,fsing)::fsings);
      Hashtbl.add stp_finite_axs a ((onlybetanorm (Ap(Lam(a,fsing),e)))::faxs)
    end
and finite_func_type_2 a e domelts codsings codsings2 fsing =
  match codsings with
  | (codsing::codsings) -> finite_func_type_1 a domelts codsings2 (conj fsing (onlybetanorm (Ap(codsing,Ap(DB(0,a),e))))); finite_func_type_2 a e domelts codsings codsings2 fsing
  | [] -> ()

let rec finite_func_type_0 a e domelts codsings codsings2 =
  match codsings with
  | (codsing::codsings) -> finite_func_type_1 a domelts codsings2 (onlybetanorm (Ap(codsing,Ap(DB(0,a),e)))); finite_func_type_0 a e domelts codsings codsings2
  | [] -> ()

let finite_func_type a domelts codsings =
  match domelts with
  | (domelt::domelts) -> finite_func_type_0 a domelt domelts codsings codsings
  | [] -> raise (GenericError "Empty Domain Bug")

let rec stp_finite a : unit =
  if ((not (Hashtbl.mem stp_finite_elts a)) || (List.length (Hashtbl.find stp_finite_elts a) = 0)) then
    begin
      if (!verbosity > 1) then Printf.printf "Generating elts of finite type %s\n" (stp_str a);
      match a with
      | Ar(a1,a2) ->
        begin
          stp_finite a1;
          stp_finite a2;
          if (!verbosity > 1) then Printf.printf "Generating funcs %s 1\n" (stp_str a);
          let domelts = Hashtbl.find stp_finite_elts a1 in
          if (!verbosity > 1) then Printf.printf "Generating funcs %s 2 %d\n" (stp_str a) (List.length domelts);
          let codsings = Hashtbl.find stp_finite_sings a2 in
          if (!verbosity > 1) then Printf.printf "Generating funcs %s 3 %d\n" (stp_str a) (List.length codsings);
          try
            Hashtbl.add stp_finite_elts a [];
            Hashtbl.add stp_finite_sings a [];
            Hashtbl.add stp_finite_axs a [];
            finite_func_type a domelts codsings
          with Timeout -> (*** Destroy partially enumerated type ***)
            begin
              Hashtbl.add stp_finite_elts a [];
              Hashtbl.add stp_finite_sings a [];
              Hashtbl.add stp_finite_axs a [];
              raise Timeout
            end
          end
      | Prop ->
         begin
           Hashtbl.add stp_finite_elts Prop [False;Ap(Ap(Imp,False),False)];
           Hashtbl.add stp_finite_sings Prop [Lam(Prop,Ap(Ap(Imp,DB(0,Prop)),False));Lam(Prop,DB(0,Prop))];
         end
      | _ -> ()
    end;;

exception ExistsToChoiceDone

let rec existstochoice1 m p =
  match m with
  | Ap(Forall(a),m1) ->
      let q = gen_lam_body a m1 in
      begin
	if p then
	  Ap(Forall(a),Lam(a,existstochoice1 q p))
	else (*** This is where the action is: Replace (forall x, q[x]) with (q[Eps x:a => ~q[x]]) ***)
	  subst q 0 (Ap(Choice(a),Lam(a,normneg q)))
      end
  | Ap(Ap(Eq(Ar(a1,a2)),m1),m2) ->
      let m1s = shift m1 0 1 in
      let m2s = shift m2 0 1 in
      begin
	existstochoice1
	  (norm name_def (forall a1 (eq a2 (ap(m1s,DB(0,a1))) (ap(m2s,DB(0,a1))))))
	  p
      end
  | Ap(Ap(Imp,m1),m2) ->
      begin
	try
	  imp (existstochoice1 m1 (not p)) m2
	with ExistsToChoiceDone
	  -> imp m1 (existstochoice1 m2 p)
      end
  | _ -> raise ExistsToChoiceDone
  
let rec existstochoice m =
  try
    existstochoice (existstochoice1 m true)
  with ExistsToChoiceDone -> m

let already_preprocessed = ref false

let rec preprocess_finite_quants m =
  match m with
  | Ap(m1,m2) -> Ap(preprocess_finite_quants m1,preprocess_finite_quants m2)
  | Lam(a1,m1) -> Lam(a1,preprocess_finite_quants m1)
  | Forall(a) ->
    begin
      stp_finite a;
      match Hashtbl.find stp_finite_elts a with (*** Replace it with all instances ***)
      | (e0::elts) -> Lam(Ar(a,Prop),(List.fold_left (fun w e -> conj w (Ap(DB(0,Ar(a,Prop)),e))) (Ap(DB(0,(Ar(a,Prop))),e0)) elts))
      | _ -> raise (GenericError "Empty type in preprocess_finite_quants")
    end
  | _ -> m

let norm_if flag f x = if get_bool_flag flag then norm name_def (f x) else x

let preprocess m =
  let m1 = norm_if "LEIBEQ_TO_PRIMEQ" leibeq_to_primeq m in
  let m2 = norm_if "EXISTSTOCHOICE" existstochoice m1 in
  let m3 = norm_if "BASETYPESFINITE" preprocess_finite_quants m2 in
  m3

let preprocess1 m =
  if (!already_preprocessed) then m else preprocess m

let process_negation mlit m nm =
  let (h,args) = head_spine nm in
  begin
    if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m);
    match h with
    | False -> () (*** do nothing ***)
    | Imp ->
	begin
	  match args with
	    [m1;m2] -> negimp_rule mlit nm m1 m2
	  | _ -> raise (GenericError "Neg Imp should have had exactly two arguments; there's a bug")
	end
    | Forall(_) -> (*** search code for ~Forall is above ***)
	raise (GenericError "Neg Forall should have had exactly one argument; there's a bug.")
    | Eq(a) ->
	let r = if (mkprooftermp ()) then (Some(NegPropRule(nm))) else None in
	begin
	  match args with
	    [m1;m2] ->
	      begin
		if (m1 = m2) then new_search_clause [-mlit] r (*** negation of reflexivity ***)
		else if (get_bool_flag "SYM_EQ") then sym_eq_clauses (-mlit) a m1 m2; (*** Equivalence of = with symmetric version. In earlier versions of Satallax (< 2.2) I sent m1=m2 and m2=m1 to the same literal. ***)
		match a with
		| Ar(a1,a2) -> (*** FE ***)
(***				  let m3 = neg (forall a1 (eq a2 (norm name_def (Ap (shift m1 0 1,DB (0,a1)))) (norm name_def (Ap (shift m2 0 1,DB (0,a1)))))) in  ***)
		    let m3 = norm name_def (neg (forall a1 (eq a2 (Ap (m1,DB (0,a1))) (Ap (m2,DB (0,a1)))))) in (*** No need to shift, since no dangling DB's [Thanks to Teucke!] ; Mar 15, normalize at the end to handle final eta (see FQ too) ***)
		    insertWithPriority (get_int_flag "POST_FEQ_DELAY") (ProcessProp1 m3);
		    if (get_bool_flag "INSTANTIATE_WITH_FUNC_DISEQN_SIDES") then
		      begin
			possibly_new_instantiation a m1;
			possibly_new_instantiation a m2
		      end;
		    let m3lit = !get_literal_fn2 m3 in
		    new_search_clause [-mlit;m3lit] r
		| Prop -> (*** BE ***)
		    let m1lit = !get_literal_fn2 m1 in
		    let m2lit = !get_literal_fn2 m2 in
		    insertWithPriority (get_int_flag "POST_NEQO_L_DELAY") (ProcessProp1 m1);
		    insertWithPriority (get_int_flag "POST_NEQO_R_DELAY") (ProcessProp1 m2);
		    insertWithPriority (get_int_flag "POST_NEQO_NL_DELAY") (ProcessProp1 (normneg m1));
		    insertWithPriority (get_int_flag "POST_NEQO_NR_DELAY") (ProcessProp1 (normneg m2));
		    new_search_clause [-mlit;m1lit;m2lit] r;
		    new_search_clause [-mlit;-m1lit;-m2lit] r
		| Base(aname) -> (*** decompose, confront, Choice accessible, special accessible ***)
		    if ((get_bool_flag "FILTER_NEGEQ") && (filterp mlit)) then
		      ()
		    else
		      begin
			Hashtbl.add neqns aname (mlit,m1,m2);
			List.iter
			  (fun (otherlit,n1,n2) -> (** (delayed) confrontation **)
			    consider_confrontation a mlit m1 m2 otherlit n1 n2)
			  (Hashtbl.find_all peqns aname);
			possibly_new_instantiation a m1;
			possibly_new_instantiation a m2;
			let (lh,largs) = head_spine m1 in
			let (rh,rargs) = head_spine m2 in
			begin
			  match (lh,rh) with
			  | (Choice(la),Choice(ra)) when (la = ra) ->
			      decompose mlit largs rargs r
			  | (Name (lhname,_),Name (rhname,_)) when ((lhname = rhname) && (decomposable lhname)) ->
			      decompose mlit largs rargs r
			  | _ -> ()
			end;
			choice_rule lh largs;
			choice_rule rh rargs;
				      (** Mar 2012 **)
			if ((get_bool_flag "HOUNIF1") && (get_bool_flag "HOUNIF1MATE")) then
			  begin
			    hounif1 (!verbosity) (to_meta nm) [] [] [] (get_int_flag "HOUNIF1BOUND") false possibly_new_instantiation
			  end
					(*** To Do: Handle Special Cases for Categorized Names ***)
		      end
	      end
	  | _ -> raise (GenericError "Neg Eq should have had exactly 2 arguments; there's a bug")
	end
    | Choice(a) ->
	if ((get_bool_flag "FILTER_NEGATM") && (filterp mlit)) then
	  ()
	else
	  begin
	    let pmd = get_int_flag "PRE_CHOICE_MATING_DELAY_NEG" in
	    Hashtbl.add nchoiceatoms a (mlit,args);
	    List.iter (fun (plit,pargs) ->
	      if (not (pargs = args)) then
		insertWithPriority pmd (Mating(plit,mlit,pargs,args))
		  )
	      (Hashtbl.find_all pchoiceatoms a);
	    choice_rule h args;
				      (** Mar 2012 **)
	    if ((get_bool_flag "HOUNIF1") && (get_bool_flag "HOUNIF1MATE")) then
	      begin
		hounif1 (!verbosity) (to_meta nm) [] [] [] (get_int_flag "HOUNIF1BOUND") false possibly_new_instantiation
	      end
	  end
    | Name(x,_) -> (** negative atom **)
	if ((get_bool_flag "FILTER_NEGATM") && (filterp mlit)) then
	  ()
	else
	  begin
	    if (decomposable x) then
	      begin
		let pmd = get_int_flag "PRE_MATING_DELAY_NEG" in
		Hashtbl.add natoms x (mlit,args);
		List.iter (fun (plit,pargs) ->
		  if (not (pargs = args)) then
		    insertWithPriority pmd (Mating(plit,mlit,pargs,args))
		      )
		  (Hashtbl.find_all patoms x)
	      end;
	    choice_rule h args;
				      (** Mar 2012 **)
	    if ((get_bool_flag "HOUNIF1") && (get_bool_flag "HOUNIF1MATE")) then
	      begin
		hounif1 (!verbosity) (to_meta nm) [] [] [] (get_int_flag "HOUNIF1BOUND") false possibly_new_instantiation
	      end
	  end
    | _ -> raise (GenericError ("Unhandled case (were logical constants normalized?) h:" ^ (trm_str h)))
  end

let process_forall mlit m a m1 =
  begin
(*    Printf.printf "Searching through semantics of %s\n" (trm_str m);
    model_2_search model4a [] a (gen_lam_body a m1); *)
    if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m; if (!dynamic_pattern_clauses) then new_pattern_clauses (-mlit) m);
    if ((get_bool_flag "FILTER_UNIV") && (filterp mlit)) then
      ()
    else
      let nmlit = (- mlit) in
      begin
	Hashtbl.add univpreds a (nmlit,m1);
        if (get_bool_flag "HOUNIF1") then hounif1 (!verbosity) (to_meta m) [] [] [] (get_int_flag "HOUNIF1BOUND") true possibly_new_instantiation; (*** Mar 2012 ***)
	let insts = (get_instantiations a) in
	begin
	  match a with
	  | Ar(a1,a2) ->
	      begin
		let rta = rtp a2 in
		begin
		  match rta with
		  | Base(rtaname) ->
		      if (not (default_elt_p rtaname)) then
			(insertWithPriority (get_int_flag "DEFAULTELT_DELAY") (DefaultElt rtaname));
		  | _ -> (*** Prop: No default element ***)
		      ()
		end;
		begin
		  if (get_bool_flag "ENUM_ITER_DEEP") then
		    begin (*** Iterative Deepening Enumeration Scheme ***)
		      if (not (enum_of_started a)) then
			let d = get_int_flag "ENUM_START" in
			begin
			  if (not (!enum_started)) then
			    let d_const = get_int_flag "IMITATE_DELAY" in
			    let d_def = get_int_flag "IMITATE_DEFN_DELAY" in
			    begin
			      enum_started := true;
			      List.iter
				(fun (x,m,sigma) ->
				  let (sigmal,rtp) = argtps_rtp sigma in
				  if (Hashtbl.mem name_def x) then
				    begin
				      if (get_bool_flag "IMITATE_DEFNS") then
					new_usable_head_rtp rtp sigmal m d_def
				    end
				  else
				    new_usable_head_rtp rtp sigmal m d_const
				      )
				!name_trm_list
			    end;
			    enum_of_start a;
			    insertWithPriority d (EnumIterDeep(get_int_flag "ENUM_ITER_DEEP_INIT",a))
			end
		    end
		  else (*** The Original Enumeration Scheme ***)
		    begin
		      begin
				      (** If we haven't started generating instantiations, start now. **)
			if (not (!enum_started)) then
			  let d = get_int_flag "ENUM_START" in
			  let d_o = get_int_flag "ENUM_O" in
			  let d_i = get_int_flag "ENUM_SORT" in
			  let d_const = get_int_flag "IMITATE_DELAY" in
			  let d_def = get_int_flag "IMITATE_DEFN_DELAY" in
			  begin
			    enum_started := true;
			    insertWithPriority (d + d_o) (EnumTp(d_o,Prop,Prop));
			    List.iter
			      (fun beta -> insertWithPriority (d + d_i) (EnumTp(d_i,Base(beta),Base(beta))))
			      !name_base_list;
			    List.iter
			      (fun (x,m,sigma) ->
				let (sigmal,rtp) = argtps_rtp sigma in
				if (Hashtbl.mem name_def x) then
				  begin
				    if (get_bool_flag "IMITATE_DEFNS") then
				      new_usable_head_rtp rtp sigmal m d_def
				  end
				else
				  new_usable_head_rtp rtp sigmal m d_const
				    )
			      !name_trm_list
			  end
		      end;
		      begin
			if (not (enum_of_started a)) then
			  let d = get_int_flag "ENUM_START" in
			  begin
			    enum_of_start a;
			    insertWithPriority d (Enum(0,[],a,(fun m -> let m = norm name_def m in possibly_new_instantiation a m)))
			  end
		      end
		    end
		end
	      end
	  | Prop -> ()
	  | Base(aname) ->
	      begin
		match insts with
		| [] ->
		    insertWithPriority (get_int_flag "DEFAULTELTINST_DELAY") (DefaultEltInst aname)
		| _ -> ()
	      end
	end;
	List.iter
	  (fun w -> ignore (forall_rule nmlit a m1 w))
	  insts
      end
  end

let process_equality mlit m a m1 m2 =
  let r = if (mkprooftermp ()) then (Some(PosPropRule(m))) else None in
  begin
    if ((not (m1 = m2)) && (get_bool_flag "SYM_EQ")) then sym_eq_clauses mlit a m1 m2; (*** Equivalence of = with symmetric version. In earlier versions of Satallax (< 2.2) I sent m1=m2 and m2=m1 to the same literal. ***)
    if ((get_bool_flag "PATTERN_CLAUSES_TRANSITIVITY_EQ") && (not (Hashtbl.mem pattern_clauses_transitivity_types a))) then
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
      end;
    match a with
    | Ar(a1,a2) -> (*** FQ ***)
	if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m);
(***				  let m3 = forall a1 (eq a2 (norm name_def (Ap (shift m1 0 1,DB (0,a1)))) (norm name_def (Ap (shift m2 0 1,DB (0,a1))))) in ***)
	let m3 = norm name_def (forall a1 (eq a2 (Ap (m1,DB (0,a1))) (Ap (m2,DB (0,a1))))) in (*** See FE above for why there's no shift on m1 and m2. Mar 15 2011: Normalize after everything, to make sure the case of a final eta is handled, e.g., forall x.s=x where s has no x free eta reduces. ***)
	insertWithPriority (get_int_flag "POST_NFEQ_DELAY") (ProcessProp1 m3);
	let m3lit = !get_literal_fn2 m3 in
	new_search_clause [-mlit;m3lit] r
    | Prop -> (*** BQ ***)
	if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m);
	let m1lit = !get_literal_fn2 m1 in
	let m2lit = !get_literal_fn2 m2 in
	insertWithPriority (get_int_flag "POST_EQO_L_DELAY") (ProcessProp1 m1);
	insertWithPriority (get_int_flag "POST_EQO_R_DELAY") (ProcessProp1 m2);
	insertWithPriority (get_int_flag "POST_EQO_NL_DELAY") (ProcessProp1 (normneg m1));
	insertWithPriority (get_int_flag "POST_EQO_NR_DELAY") (ProcessProp1 (normneg m2));
	new_search_clause [-mlit;m1lit;-m2lit] r;
	new_search_clause [-mlit;-m1lit;m2lit] r
    | Base(aname) -> (*** confront ***)
	if ((get_bool_flag "FILTER_POSEQ") && (filterp mlit)) then
	  ()
	else
	  begin
	    if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m);
	    Hashtbl.add peqns aname (mlit,m1,m2);
	    List.iter
	      (fun (otherlit,n1,n2) -> (*** (delayed) confrontation ***)
		consider_confrontation a otherlit n1 n2 mlit m1 m2)
	      (Hashtbl.find_all neqns aname);
	  end;
				      (** Mar 2012 **)
	if ((get_bool_flag "HOUNIF1") && (get_bool_flag "HOUNIF1MATE")) then
	  begin
	    hounif1 (!verbosity) (to_meta m) [] [] [] (get_int_flag "HOUNIF1BOUND") true possibly_new_instantiation
	  end
  end

let process_unprocessed_prop mlit m =
  match m with
  | Ap(Ap(Imp,Ap(Forall(a),m1)),False) ->
      begin
	if ((!enable_pattern_clauses) && (get_bool_flag "PATTERN_CLAUSES_FORALL_AS_LIT")) then (apply_pattern_clauses mlit m);
	ignore (negforall_rule mlit a m1)
      end
  | Ap(Ap(Imp,nm),False) -> process_negation mlit m nm
  | Ap(Forall(a),m1) -> process_forall mlit m a m1 (*** Instantiate ***)
  | _ ->
      begin
	let (h,args) = head_spine m in
	match h with
	| False ->
	    let r = if (mkprooftermp ()) then (Some(PosPropRule(m))) else None in
	    let flit = !get_literal_fn2 False in
	    new_search_clause [-flit] r
	| Imp ->
	    begin
	      if (!enable_pattern_clauses) then (apply_pattern_clauses mlit m);
	      match args with
		[m1;m2] -> imp_rule mlit m m1 m2
	      | _ -> raise (GenericError "Imp should have had exactly two arguments; there's a bug")
	    end
	| Forall(_) -> (*** search code for Forall is above ***)
	    raise (GenericError "Forall should have had exactly one argument; there's a bug.")
	| Eq(a) ->
	    begin
	      match args with
		[m1;m2] -> process_equality mlit m a m1 m2
	      | _ -> raise (GenericError "Eq should have had exactly 2 arguments; there's a bug")
	    end
	| Choice(a) ->
	    let pmd = get_int_flag "PRE_CHOICE_MATING_DELAY_POS" in
	    if ((get_bool_flag "FILTER_POSATM") && (filterp mlit)) then
	      ()
	    else
	      begin
		if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m);
		Hashtbl.add pchoiceatoms a (mlit,args);
		List.iter (fun (nlit,nargs) ->
		  if (not (args = nargs)) then
		    insertWithPriority pmd (Mating(mlit,nlit,args,nargs));
		  )
		  (Hashtbl.find_all nchoiceatoms a);
		choice_rule h args;
				      (** Mar 2012 **)
		if ((get_bool_flag "HOUNIF1") && (get_bool_flag "HOUNIF1MATE")) then
		  begin
		    hounif1 (!verbosity) (to_meta m) [] [] [] (get_int_flag "HOUNIF1BOUND") true possibly_new_instantiation
		  end
	      end
	| Name(x,_) -> (** positive atom **)
	    if ((get_bool_flag "FILTER_POSATM") && (filterp mlit)) then
	      ()
	    else
	      begin
		if (!enable_pattern_clauses && not (!apply_pattern_clauses_early)) then (apply_pattern_clauses mlit m);
		if (decomposable x) then
		  begin
		    let pmd = get_int_flag "PRE_MATING_DELAY_POS" in
		    Hashtbl.add patoms x (mlit,args);
		    List.iter (fun (nlit,nargs) ->
		      if (not (args = nargs)) then
			insertWithPriority pmd (Mating(mlit,nlit,args,nargs));
		      )
		      (Hashtbl.find_all natoms x)
		  end;
		choice_rule h args; (*** This was missing and caused some incompleteness (eg, CHOICE6 in mode59c). - Chad, Jan 25, 2011 ***)
				      (** Mar 2012 **)
		if ((get_bool_flag "HOUNIF1") && (get_bool_flag "HOUNIF1MATE")) then
		  begin
		    hounif1 (!verbosity) (to_meta m) [] [] [] (get_int_flag "HOUNIF1BOUND") true possibly_new_instantiation
		  end
			  (*** To Do: Handle Special Cases for Categorized Names ***)
	      end
	| _ -> raise (GenericError ("Unhandled case (were logical constants normalized?) h:" ^ (trm_str h)))
      end
	
	
let rec process_search_option p op =
  match op with
  | ProcessProp1(m) ->
      begin
	if (not (Hashtbl.mem processed m)) then
	  begin
	    if !translucent_defns then
	      let m2 = norm name_def_all m in (*** in case some abbrevs occurring in m are translucent ***)
	      if m = m2 then
		process_search_option p (ProcessProp2(m)) (*** none were translucent, the usual case ***)
	      else (*** some were translucent ***)
		let mlit = !get_literal_fn2 m in
		Hashtbl.add processed m p;
		let m2lit = !get_literal_fn2 m2 in
		new_search_clause [mlit;-m2lit] (if (mkprooftermp()) then (Some(DeltaRule)) else None);
		new_search_clause [-mlit;m2lit] (if (mkprooftermp()) then (Some(DeltaRule)) else None);
		insertWithPriority !fiTRANSLUCENT_EXPAND_DELAY (ProcessProp2(m2))
	    else
	      process_search_option p (ProcessProp2(m)) (*** there are no translucent defns at all, so don't even check ***)
	  end
      end
  | ProcessProp2(m) -> (*** in this case, assume all translucent defns have been expanded ***)
      if (not (Hashtbl.mem processed m)) then
	begin
	  let mlit = !get_literal_fn2 m in
	  if ((!not_in_prop_model_delay_p) && (!minisatsearchcounter = 0) && ((minisat_modelValue mlit) > 0)) then (*** Chad: Nov 2011 - delay if not true in the current prop approx; Chad: Dec 2012 - added condition that minisatsearchcounter = 0 so that modelValue is only called if the last interaction with minisat actually called search. Otherwise we may get segmentation faults. The effect is that if MINISAT_SEARCH_PERIOD > 1 and NOT_IN_PROP_MODEL_DELAY > 0, then we only check if the prop is in the model when we happen to have called minisat to search. ***)
	    begin
	      if (!verbosity > 8) then Printf.printf "using prop model to delay working on %d %s\n" mlit (trm_str m);
	      insertWithPriority (!not_in_prop_model_delay) op
	    end
	  else
	    begin
	      Hashtbl.add processed m p;
	      if (!verbosity > 8) then Printf.printf "working on %d %s\n" mlit (trm_str m);
	      process_unprocessed_prop mlit m
	    end
	end
  | Mating(plit,nlit,pargs,nargs) ->
      if (!verbosity > 9) then Printf.printf "Mating %d %d\n" plit nlit;
      ignore (mate plit nlit pargs nargs)
  | Confront(eqlit,neqlit,a,s,t,u,v) ->
      ignore (confront a eqlit s t neqlit u v)
  | DefaultElt(aname) -> ignore (default_elt aname)
  | DefaultEltInst(aname) -> (*** If there are no instantiations of the sort, use the default elt. ***)
      let a = Base aname in
      let insts = (get_instantiations a) in
      begin
	match insts with
	| [] -> 
	    let m = default_elt aname in
	    possibly_new_instantiation a m
	| _ -> ()
      end
  | NewInst(a,m) ->
      process_instantiation a m; (*** Must process it now and make it passive ***)
  | EnumIterDeep(d,a) ->
      for i = (!typesgenerated) to (d - 1)
      do
	generate_types i
      done;
      typesgenerated := d;
      List.iter
	(fun m -> (possibly_new_instantiation a m))
	(enum_depth d [] a); (*** Build a list of all of terms of type a in the empty ctx of depth <= d ***)
      insertWithPriority !fiENUM_ITER_DEEP_DELAY (EnumIterDeep(d + 1 + !fiENUM_ITER_DEEP_INCR,a)) (*** Next time, go deeper [as well as using the new constants generated since then] ***)
  | EnumTp(d,ar,a) ->
      let dar = d + !fiENUM_ARROW in
      insertWithPriority dar (EnumTp(dar,ar,Ar(a,a)));
      List.iter
	(fun (br,b,de) ->
	  insertWithPriority (dar + de) (EnumTp(dar + de,ar,Ar(b,a)));
	  insertWithPriority (dar + de) (EnumTp(dar + de,br,Ar(a,b)))
	    )
	(usable_types ());
      process_new_type ar a d
  | EnumAp(d,gamma,[],h,c) ->
      c h (*** h is the completed term, call continuation c with it. **)
  | EnumAp(d,gamma,(sigma::sigmal),h,c) ->
      insertWithPriority d (Enum(d,gamma,sigma,fun m -> insertWithPriority d (EnumAp(d,gamma,sigmal,norm name_def (ap(h,m)),c))))
  | Enum(d,gamma,Ar(sigma,tau),c) ->
      insertWithPriority d (Enum(d,sigma::gamma,tau,fun m -> c (Lam(sigma,m))))
  | Enum(d,gamma,(Base(alpha) as a),c) ->
      let pd = !fiPROJECT_DELAY in
      let pchoice = !fiENUM_CHOICE in
      begin
	enum_projections pd (d + pd) gamma gamma 0 a c;
	(** imitations **)
	List.iter
	  (fun (sigmal,h,pimit) ->
	    insertWithPriority (d + pimit) (EnumAp(d + pimit,gamma,sigmal,h,c));
	  )
	  (usable_heads_rtp a);
	new_term_continuation_rtp a (fun (sigmal,h,pimit) -> insertWithPriority (d + pimit) (EnumAp(d + pimit,gamma,sigmal,h,c)));
	(*** Polymorphic Logical Constants: Choice ***)
	if (!verbosity > 5) then begin print_string("Considering enum with choice"); print_newline(); flush stdout end;
	let choiceauxfn = (fun b de ->
	  let (bargtps,_) = argtps_rtp b in (*** rtp of b must be a ***)
	  insertWithPriority (d + pchoice + de) (EnumAp(d + pchoice + de,gamma,(Ar(b,Prop)::bargtps),Choice(b),c)))
	in
	List.iter (fun (b,de) -> choiceauxfn b de)
	  (usable_types_rtp a);
	new_type_continuation_rtp a choiceauxfn
      end
  | Enum(d,gamma,Prop,c) ->
      let pd = !fiPROJECT_DELAY in
      let pimp = !fiENUM_IMP in
      let pfalse = !fiENUM_FALSE in
      let pneg = !fiENUM_NEG in
      let pforall = !fiENUM_FORALL in
      let peq = !fiENUM_EQ in
      let pchoice = !fiENUM_CHOICE in
      begin
	enum_projections pd (d + pd) gamma gamma 0 Prop c;
	(** imitations **)
	List.iter
	  (fun (sigmal,h,pimit) ->
	    insertWithPriority (d + pimit) (EnumAp(d + pimit,gamma,sigmal,h,c));
	  )
	  (usable_heads_rtp Prop);
	new_term_continuation_rtp Prop (fun (sigmal,h,pimit) -> insertWithPriority (d + pimit) (EnumAp(d + pimit,gamma,sigmal,h,c)));
	(*** Logical Constants ***)
	insertWithPriority (d + pfalse) (EnumAp(d + pfalse,gamma,[],False,c));
	insertWithPriority (d + pimp) (EnumAp(d + pimp,gamma,[Prop;Prop],Imp,c));
	insertWithPriority (d + pneg) (EnumAp(d + pneg,gamma,[Prop],logicnorm Neg,c)); (*** This isn't needed for completeness, but it seems like overkill to wait for -> False to be generated. - Chad, Dec 2010 ***)
	(*** Polymorphic Logical Constants: Eq, Forall, Choice ***)
	let choiceauxfn = (fun b de ->
	  let (bargtps,_) = argtps_rtp b in (*** rtp of b must be Prop ***)
	  insertWithPriority (d + pchoice + de) (EnumAp(d + pchoice + de,gamma,(Ar(b,Prop)::bargtps),Choice(b),c)))
	in
	List.iter (fun (b,de) -> choiceauxfn b de)
	  (usable_types_rtp Prop);
	new_type_continuation_rtp Prop choiceauxfn;
	let alleqauxfn = (fun b de ->
	  insertWithPriority (d + pforall + de) (EnumAp(d + pforall + de,gamma,[Ar(b,Prop)],Forall(b),c));
	  insertWithPriority (d + peq + de) (EnumAp(d + peq + de,gamma,[b;b],Eq(b),c)))
	in
	List.iter
	  (fun (_,b,de) -> alleqauxfn b de)
	  (usable_types ());
	new_type_continuation
	  alleqauxfn
      end
  | Filter(d) ->
      try
	let (d1,_) = peekAtNext() in (*** peek to make sure there is some other option, use this to delay the next Filter ***)
	(*** Put Filter back on priority queue, with higher delay ( = lower priority) ***)
	let d2 = d1 + !fiFILTER_INCR in
	insertWithPriority d2 (Filter d2);
	if (get_bool_flag "FILTER_UNIV_USABLE") then
	  Hashtbl.iter (fun a (n,_) -> filterneg n)
	    univpreds;
	if (get_bool_flag "FILTER_POSATM_USABLE") then
	  begin
	    Hashtbl.iter (fun x (n,_) -> filterneg n)
	      patoms;
	    Hashtbl.iter (fun x (n,_) -> filterneg n)
	      pchoiceatoms
	  end;
	if (get_bool_flag "FILTER_NEGATM_USABLE") then
	  begin
	    Hashtbl.iter (fun x (n,_) -> filterneg n)
	      natoms;
	    Hashtbl.iter (fun x (n,_) -> filterneg n)
	      nchoiceatoms
	  end;
	if (get_bool_flag "FILTER_POSEQ_USABLE") then
	  Hashtbl.iter (fun x (n,_,_) -> filterneg n)
	    peqns;
	if (get_bool_flag "FILTER_NEGEQ_USABLE") then
	  Hashtbl.iter (fun x (n,_,_) -> filterneg n)
	    neqns;
      with
      | Not_found -> () (*** If this is the only option, quit ***)

let print_model_pfterm () = match (!mkproofterm) with
  | Some ModelTrue -> print_model minisat_modelValue true
  | Some Model -> print_model minisat_modelValue false
  | _ -> ()


let search_main () =
  try
    while true do
      let (p,op) = peekAtNext() in
      if (!verbosity > 5) then Printf.printf "Option (Priority %d): %s\n" p (searchoption_str op);
      let op = getNext () in
      try process_search_option p op
      with Not_found -> raise (GenericError "Not_found raised while processing search option")
    done
  (* no more options available *)
  with Not_found -> print_model_pfterm (); minisat_result ()

let pos_heads : (trm,unit) Hashtbl.t = Hashtbl.create 10
let neg_heads : (trm,unit) Hashtbl.t = Hashtbl.create 10
let eqn_heads : (trm,unit) Hashtbl.t = Hashtbl.create 10
let diseqn_heads : (trm,unit) Hashtbl.t = Hashtbl.create 10

let rec set_relevance_info_tm m =
  match m with
  | Lam(a,m1) -> set_relevance_info_tm m1
  | _ ->
      match (head_spine m) with
      | (Name(x,_) as h,s) ->
	  Hashtbl.add diseqn_heads h ();
	  ignore (List.map set_relevance_info_tm s)
      |	_ -> ()

let rec set_relevance_info m pos =
  match m with
  | Lam(a,m1) -> set_relevance_info m1 pos
  | _ ->
      match (head_spine m) with
      | (Name(x,_) as h,s) ->
	  ignore (List.map set_relevance_info_tm s);
	  if pos then
	    Hashtbl.add pos_heads h ()
	  else
	    Hashtbl.add neg_heads h ()
      | (Eq(_),[m1;m2]) ->
	  begin
	    match (head_spine m1) with
	    | (Name(x,_) as h,s) ->
		if pos then
		  Hashtbl.add eqn_heads h ()
		else
		  (Hashtbl.add diseqn_heads h ();
		   ignore (List.map set_relevance_info_tm s))
	    |  _ -> ();
	    match (head_spine m2) with
	    | (Name(x,_) as h,s) ->
		if pos then
		  Hashtbl.add eqn_heads h ()
		else
		  (Hashtbl.add diseqn_heads h ();
		   ignore (List.map set_relevance_info_tm s))
	    |  _ -> ()
	  end
      | (Imp,[m1;m2]) ->
	  begin
	    set_relevance_info m1 (not pos);
	    set_relevance_info m2 pos
	  end
      | (Forall(_),[m1]) -> set_relevance_info m1 pos
      | (_,_) -> ()

let rec relevance_delay m pos d =
  if (d <= 0) then
    0
  else
    match m with
    | Lam(a,m1) -> relevance_delay m1 pos d
    | _ ->
	match (head_spine m) with
	| (Name(x,_) as h,s) ->
	    if ((pos && (Hashtbl.mem neg_heads h)) || ((not pos) && (Hashtbl.mem pos_heads h))) then
	      d - 1
	    else
	      d
	| (Eq(_),[m1;m2]) ->
	    begin
	      let d2 =
		match (head_spine m1) with
		| (Name(x,_) as h,s) ->
		    if ((pos && (Hashtbl.mem diseqn_heads h)) || ((not pos) && (Hashtbl.mem eqn_heads h))) then
		      d - 1
		    else
		      d
		| _ -> d
	      in
		match (head_spine m2) with
		| (Name(x,_) as h,s) ->
		    if ((pos && (Hashtbl.mem diseqn_heads h)) || ((not pos) && (Hashtbl.mem eqn_heads h))) then
		      d2 - 1
		    else
		      d2
		| _ -> d2
	    end
	| (Imp,[m1;m2]) -> relevance_delay m1 (not pos) (relevance_delay m2 pos d)
	| (Forall(_),[m1]) -> relevance_delay m1 pos d
	| (_,_) -> d


let process_and_insert insertfun m =
      let mn = preprocess1 m in
      match (choiceop_axiom mn) with
      | Some(x,a) ->
	  declare_choiceop x a (mn,m)
      | None ->
	  begin
	    insertfun mn;
	    let mlit = !get_literal_fn1 mn in
	    Hashtbl.add assumption_lit mlit (mn,m);
	    new_assumption_lit mlit;
	    if (get_bool_flag "INITIAL_SUBTERMS_AS_INSTANTIATIONS") then
	      begin
		if (!verbosity > 4) then Printf.printf "---- Initial Subterms as Instantiations BEGIN ----\n";
		if (!verbosity > 4) then Printf.printf "---- m = %s ----\n" (trm_str m);
		if (!verbosity > 4) then Printf.printf "---- mn = %s ----\n" (trm_str mn);
		ignore (subterms_as_instantiations mn 0);
		if (!verbosity > 4) then Printf.printf "---- Initial Subterms as Instantiations END ----\n"
	      end
	  end

let insert_conjecture mn =
  if get_bool_flag "USE_MODELS" then gen_models mn;
  insertWithPriority 0 (ProcessProp1 mn);
  if (get_int_flag "RELEVANCE_DELAY" > 0) then
    set_relevance_info mn false

let insert_axiom mn =
  if get_bool_flag "USE_MODELS" then gen_models mn;
  let ad = get_int_flag "AXIOM_DELAY"
  and rd = relevance_delay mn true (get_int_flag "RELEVANCE_DELAY") in
  insertWithPriority (ad + rd) (ProcessProp1 mn)

let insert_filter_command d = insertWithPriority d (Filter d)

let put_ax_on_queue ax =
  let axlit = !get_literal_fn1 ax in
  Hashtbl.add assumption_lit axlit (ax,ax);
  new_assumption_lit axlit;
  insertWithPriority (get_int_flag "AXIOM_DELAY") (ProcessProp1 ax);
  if (!verbosity > 1) then Printf.printf "Putting axiom on queue %s\n" (trm_str ax)

let should_filter () =
     get_bool_flag "FILTER_UNIV_USABLE"
  || get_bool_flag "FILTER_POSATM_USABLE"
  || get_bool_flag "FILTER_NEGATM_USABLE"
  || get_bool_flag "FILTER_POSEQ_USABLE"
  || get_bool_flag "FILTER_NEGEQ_USABLE"

let search_1 b1 b2 =
  let _ = minisat_init (!verbosity) in
  if (!verbosity > 3) then print_endline "Initialized minisat";

  (*** Process "conjecture" part first - March 18 2011 ***)
  List.iter (process_and_insert insert_conjecture) b1;
  (*** Process "axiom" part second - March 18 2011 ***)
  List.iter (process_and_insert insert_axiom) b2;

  if should_filter () then insert_filter_command (get_int_flag "FILTER_START");

  if get_bool_flag "BASETYPESFINITE" then
    Hashtbl.iter (fun _ -> List.iter put_ax_on_queue) stp_finite_axs;

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
  match b1 with
    (m::pr) ->
      begin
	match m with
	| Ap(Ap(Imp,Ap(Ap(Eq(_),m1),m2)),False) when (m1 = m2) ->
	    if (mkprooftermp ()) then
	      raise (Unsatisfiable (Some (NegReflR(m))))
	    else
	      raise (Unsatisfiable None)
	| Ap(Ap(Imp,Ap(Forall(a),m1)),False) ->
	    begin
	      let (ws,w) = get_fresh_name a in
	      if (!verbosity > 5) then begin print_string("Using Fresh Witness " ^ (trm_str w)); print_newline(); flush stdout end;
	      process_new_name a w (get_int_flag "NEW_HEAD_ENUM_DELAY");
	      let m1w = (norm name_def (ap(m1,w))) in
	      if (!verbosity > 8) then (print_string(" m1w = " ^ (trm_str m1w)); print_newline());
	      let nm1w = normneg m1w in
	      if get_bool_flag "USE_MODELS" then extend_models nm1w;
	      begin
		try
		  split_global_disjunctions (nm1w::pr) b2 b bs sgn cnj
		with
		| Unsatisfiable(Some(r1)) ->
		    raise (Unsatisfiable(Some(NegAllR(a,m1,ws,r1))))
	      end
	    end
	| Ap(Ap(Imp,nm),False) ->
	    let (h,args) = head_spine nm in
	    begin
	      match h with
	      | False -> split_global_disjunctions pr b2 b bs sgn cnj (*** drop ~False ***)
	      | Imp ->
		  begin
		    match args with
		      [m1;m2] ->
			begin
			  try
			    split_global_disjunctions (m1::(normneg m2)::pr) b2 b bs sgn cnj
			  with
			  | Unsatisfiable(Some(r1)) ->
			      raise (Unsatisfiable (Some (NegImpR(m1,m2,r1))))
			end
		    | _ -> raise (GenericError "foo3")
		  end
	      | Eq(Ar(a1,a2)) ->
		  begin
		    match args with
		      [m1;m2] ->
			let m1s = shift m1 0 1 in
			let m2s = shift m2 0 1 in
			begin
			  try
			    split_global_disjunctions
			      ((norm name_def (normneg (forall a1 (eq a2 (ap(m1s,DB(0,a1))) (ap(m2s,DB(0,a1)))))))::pr)
			      b2 b bs sgn cnj
			  with
			  | Unsatisfiable(Some(r1)) ->
			      raise (Unsatisfiable (Some (NegEqFR(a1,a2,m1,m2,r1))))
			end
		    | _ -> raise (GenericError "foo3")
		  end		  
	      | Eq(Prop) ->
		  begin
		    match args with
		      [m1;m2] ->
		      begin
		        try split_global_disjunctions (m1::(normneg m2)::pr) b2 b bs sgn cnj
		        with e -> handle_binop_ex e (fun r1 r2 -> NegEqOR(m1,m2,r1,r2)) (lazy (split_global_disjunctions ((normneg m1)::m2::pr) b2 b bs sgn cnj)) sgn
		      end
		    | _ -> raise (GenericError "foo3")
		  end
	      | _ ->
		  split_global_disjunctions pr b2 (m::b) bs sgn cnj
	    end
	| Ap(Forall(a),m1) when get_bool_flag "BASETYPESFINITE" -> (*** Apr 2012 - for checking satisfiability in finite models ***)
	    begin
              stp_finite a;
              let elts = Hashtbl.find stp_finite_elts a in (*** Replace it with all instances ***)
              split_global_disjunctions (List.append (List.map (fun e -> (norm name_def (Ap(m1,e)))) elts) pr) b2 b bs sgn cnj
	    end
	| _ ->
	    let (h,args) = head_spine m in
	    begin
	      match h with
	      | False -> if (mkprooftermp ()) then raise (Unsatisfiable (Some FalseR)) else raise (Unsatisfiable None)
	      | Imp ->
		  begin
		    match args with
		      [m1;m2] ->
		      begin
		        try split_global_disjunctions ((normneg m1)::pr) b2 b bs sgn cnj
		        with e -> handle_binop_ex e (fun r1 r2 -> ImpR(m1,m2,r1,r2)) (lazy (split_global_disjunctions (m2::pr) b2 b bs sgn cnj)) sgn
		      end
		    | _ -> raise (GenericError "foo3")
		  end
	      | Eq(Prop) ->
		  begin
		    match args with
		      [m1;m2] ->
		      begin
		        try split_global_disjunctions (m1::m2::pr) b2 b bs sgn cnj
		        with e -> handle_binop_ex e (fun r1 r2 -> EqOR(m1,m2,r1,r2)) (lazy (split_global_disjunctions ((normneg m1)::(normneg m2)::pr) b2 b bs sgn cnj)) sgn
		      end
		    | _ -> raise (GenericError "foo3")
		  end
	      | _ ->
		  split_global_disjunctions pr b2 (m::b) bs sgn cnj
	    end
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


let setup_pattern_clauses () =
  if (get_bool_flag "ENABLE_PATTERN_CLAUSES") then
    begin
      enable_pattern_clauses := true;
      if (get_bool_flag "NONFORALL_PATTERN_CLAUSES_USABLE") then
	nonforall_pattern_clauses_usable := true;
      if (get_bool_flag "DYNAMIC_PATTERN_CLAUSES") then
	dynamic_pattern_clauses := true;
      if (get_bool_flag "PATTERN_CLAUSES_EARLY") then
	begin
	  if (get_bool_flag "APPLY_PATTERN_CLAUSES_EARLY") then
	    begin
	      get_literal_fn1 := get_literal_and_make_and_apply_pattern_clause;
	      apply_pattern_clauses_early := true
	    end
	  else
	    get_literal_fn1 := get_literal_and_make_pattern_clause;
	  if (!dynamic_pattern_clauses) then
	    begin
	      if (get_bool_flag "APPLY_PATTERN_CLAUSES_EARLY") then
		get_literal_fn2 := get_literal_and_make_and_apply_pattern_clause
	      else
		get_literal_fn2 := get_literal_and_make_pattern_clause;
	      dynamic_pattern_clauses := false
	    end
	end
    end;

  (*** Chad: April 6, 2011 ***)
  pattern_clauses_forall_as_lit := get_bool_flag "PATTERN_CLAUSES_FORALL_AS_LIT";
  pattern_clauses_onlyallstrict := get_bool_flag "PATTERN_CLAUSES_ONLYALLSTRICT";
  pattern_clauses_eqnlits := get_bool_flag "PATTERN_CLAUSES_EQNLITS"

let setup_basetypes () =
  if (not (!nontheorem)) then
  begin
    if (get_bool_flag "BASETYPESTOPROP") then
      raise (GenericError "The flag BASETYPESTOPROP must be false unless trying to determine (Counter)Satisfiablity (-N on the command line).");
    if (get_bool_flag "BASETYPESFINITE") then
      raise (GenericError "The flag BASETYPESFINITE must be false unless trying to determine (Counter)Satisfiablity (-N on the command line).");
  end;

  (*** Apr 2012: If BASETYPESFINITE is true, then add fresh names for the elements and axiom that says they cover all the elements ***)
  if (get_bool_flag "BASETYPESFINITE") then
    Hashtbl.iter (fun x _ -> finite_base_type x (get_int_flag "BASETYPESMAXSIZE")) name_base


(*** Chad: Nov 2011 ***)
let setup_prop_model_delay () =
  not_in_prop_model_delay := get_int_flag "NOT_IN_PROP_MODEL_DELAY";
  not_in_prop_model_delay_p := (!not_in_prop_model_delay > 0)

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
  then List.partition (Hashtbl.mem part_of_conjecture) (List.rev ms) (* reversal is essential, otherwise speed can be halved! (apparently) *)
  else ([], ms)

let search () =
  minisatsearchperiod := get_int_flag "MINISAT_SEARCH_PERIOD";
  setup_pattern_clauses ();
  setup_basetypes ();
  setup_prop_model_delay ();

  search_init ();

  (*** split branch into conjecture part (b1) and axiom part (b2) ***)
  let (b1, b2) = split_conjecture_axioms !initial_branch in
  if (get_bool_flag "SPLIT_GLOBAL_DISJUNCTIONS")
  then search_split_global_disjs b1 b2
  else search_1 b1 b2

