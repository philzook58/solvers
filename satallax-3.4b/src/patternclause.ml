open Syntax
open Match
open Log
open State
open Atom
open Error
open Priorityqueue
open Searchoption
open Flags
open Refut

(*** (int of nalllit,locevars,unmatched,abslits,dlist,strictlits,rew,ml,pl,il,cg)
  nalllit : negated literal of universally quantified formula from which I've made this clause.
  locevars : evars local to this clause
  unmatched : metawffs that are not yet ground
  abslits : literals of grounded metawffs
  dlist : disagreement pairs
  strictlits : (optional) list of literals which contained a strict occurence of every metavar in the original clause
  rew : If equational lits have been used to rewrite, this contains the information about the rewrite step: (bool [right to left?],stp [type of eqn],metatrm list)
  ml : list of metatrms that will be used to construct a proof if the clause is used
  pl : predicates for quantified formulas.
  il : instantiations for nonvacuous quantifiers
  cg : function for constructing the propositional clauses once the pattern clause has been fully instantiated.
 ***)

type pattern_clause = {
  nalllit : int
; locevars : evar list
; unmatched : metatrm list
; abslits : int list
; dlist : dpair list
; strictlitsopt : metatrm list option
; rew : (bool * stp * metatrm list) list option
; ml : metatrm list
; pl : metatrm list
; il : metatrm list
; cg : trm list -> trm list -> trm list -> trm list -> unit
}

let pattern_clauses : pattern_clause list ref = ref []
let pattern_clauses_usable : (int * trm) list ref = ref []
exception TrivialClause

(*** April 6, 2011 - Chad, I want to dynamically turn these on and off.  The immediate application is to make pattern clauses for transitivity of equation. ***)
let pattern_clauses_forall_as_lit : bool ref = ref false 
let pattern_clauses_onlyallstrict : bool ref = ref false 
let pattern_clauses_eqnlits : bool ref = ref false 

(*** The pattern clause has become ground.  Put it in the set of propositional clauses. ***)
let apply_pattern_clause_2 nalllit ml pl il rewc cg =
  if (!verbosity > 40) then
    begin
      Printf.printf "* apply_pattern_clause_2\n";
      Printf.printf "-------\n";
      Printf.printf "%d\n" nalllit;
      Printf.printf "ml\n";
      List.iter (fun m -> Printf.printf ". %s\n" (trm_str m)) ml;
      Printf.printf "pl\n";
      List.iter (fun m -> Printf.printf ". %s\n" (trm_str m)) pl;
      Printf.printf "il\n";
      List.iter (fun m -> Printf.printf ". %s\n" (trm_str m)) il;
      Printf.printf "rewc\n";
      List.iter (fun (re,a,ml) -> Printf.printf ". %s Rewrite at %s\n" (if re then "<-" else "->") (stp_str a); (List.iter (fun m -> Printf.printf " %s\n" (trm_str m)) ml)) rewc;
      Printf.printf "-------\n";
    end;
  List.iter
    (fun (re,a,ml) ->
      match ml with
	[p;l;r;pl;pr] ->
	  begin
	    let e = if re then eq a r l else eq a l r in
	    let epr = imp e pr in
	    let epy0 = norm name_def (Lam(a,imp (if re then eq a (DB(0,a)) l else eq a l (DB(0,a))) (Ap(p,DB(0,a))))) in
	    let epy = Ap(Forall(a),epy0) in
	    let plepy = imp pl epy in
	    let ao = Ar(a,Prop) in
	    let pplepy0 = norm name_def (Lam(ao,imp (Ap(DB(0,ao),l)) (Ap(Forall(a),Lam(a,imp (if re then eq a (DB(0,a)) l else eq a l (DB(0,a))) (Ap(DB(1,ao),DB(0,a)))))))) in
	    let pplepy = Ap(Forall(ao),pplepy0) in
	    let ppxepy0 = norm name_def (Lam(a,Ap(Forall(ao),Lam(ao,imp (Ap(DB(0,ao),DB(1,a))) (Ap(Forall(a),Lam(a,imp (if re then eq a (DB(0,a)) (DB(2,a)) else eq a (DB(2,a)) (DB(0,a))) (Ap(DB(1,ao),DB(0,a)))))))))) in
	    let ppxepy = Ap(Forall(a),ppxepy0) in
	    let el = get_literal e in
	    let prl = get_literal pr in
	    let pll = get_literal pl in
	    let eprl = get_literal epr in
	    let epyl = get_literal epy in
	    let plepyl = get_literal plepy in
	    let pplepyl = get_literal pplepy in
	    let ppxepyl = get_literal ppxepy in
	    new_search_clause [ppxepyl] (if (mkprooftermp()) then if re then Some(Known(ppxepyl,coqknown("@eq_ind_r","eqEr'"),[a])) else Some(Known(ppxepyl,coqknown("@eq_ind","eqE'"),[a])) else None);
	    new_search_clause [(- ppxepyl);pplepyl] (if (mkprooftermp()) then Some(InstRule(a,ppxepy0,l)) else None);
	    new_search_clause [(- pplepyl);plepyl] (if (mkprooftermp()) then Some(InstRule(ao,pplepy0,p)) else None);
	    new_search_clause [(- plepyl);(- pll);epyl] (if (mkprooftermp()) then Some(PosPropRule(plepy)) else None);
	    new_search_clause [(- epyl);eprl] (if (mkprooftermp()) then Some(InstRule(a,epy0,r)) else None);
	    new_search_clause [(- eprl);(- el);prl] (if (mkprooftermp()) then Some(PosPropRule(epr)) else None)
	  end
      |	_ -> raise (GenericError "Problem with Rewrite in a Pattern Clause"))
    rewc;
  cg [] ml pl il

let allstrictp evars p =
  let xl = update_strict [] p in
  try
    ignore (List.find (fun x -> (not (mem_evar x xl))) evars); (*** If we successfully find such an x, then p does not contain a strict occurrence of all evars ***)
    false
  with
  | Not_found -> true (*** p contains a strict occurrence of all evars ***)

(*** Apply a pattern clause to a ground formula using pattern matching. ***)
(*** m is the negation of some formula n that may be true; mlit is the literal of m. ***)
(*** The idea of the pattern clause is this:
 Either nalllit is true (negation of the forall),
 or one of the unmatched metawffs must be true,
 or one of the abslits (lits of ground wffs) must be true.
 1. By matching a member of unmatched against m, we can obtain a partially instantiated instance of the pattern clause.
    In the instance, we have removed at least one member of unmatched (the one that matched m) and we put mlit onto abslits.
 2. Optionally, we can use equations in unmatched for rewriting.
    Suppose n is a member of unmatched that is an equation n1 =(a) n2.
    Suppose m is of the form C[t] where t has no free DB's and t has type a.
    If n1 matches t, then we can form a new pattern clause that can be semantically justified by Leibniz equality.
    We replace the unmatched literal n1 =(a) n2 with C[n1] | -C[n2], partially instantiated.
    Since C[n1] is C[t], we add mlit to abslits.  We remove the unmatched equation n and replace it with -C[n2].
 ***)
let rec apply_pattern_clause ({nalllit; locevars; unmatched; abslits; dlist; strictlitsopt; rew; ml; pl; il; cg} as c) mlit m =
  begin
    if (!verbosity > 40) then
      begin
	Printf.printf "* apply_pattern_clause called with mlit %d: %s\nand clause %d %s %s\n" mlit (trm_str m)
	  (-nalllit)
	  (String.concat " " (List.map string_of_evar locevars))
	  (String.concat " " (List.map string_of_int abslits));
	Printf.printf "unmatched\n";
	List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m)) unmatched;
	match strictlitsopt with
	| Some(strictlits) ->
	    begin
	      Printf.printf "strict lits\n";
	      List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m)) strictlits
	    end
	| _ -> ()
      end;
    if (not (List.mem (- mlit) abslits)) then (*** Unless it would be a trivial clause with both mlit and -mlit ***)
      begin
	List.iter
	  (fun n ->
	    apply_pattern_clause_1 c n mlit m;
	    match rew with
	    | Some _ ->
	      begin
		match n with
		| MAp(MAp(MGround(Eq(a)),n1),n2) -> (*** n is an unmatched equational metawff. We may rewrite with it. ***)
		    begin
		      match strictlitsopt with
		      | Some(strictlits)-> (*** In this case, only rewrite fromtrm to totrm when fromtrm has strict occurrences of all metavars ***)
			  begin
			    if (allstrictp locevars n1) then (*** Note: If this flag is true, then evars and locevars are the same ***)
			      apply_pattern_clause_eqn c n a n1 n2 (normneg m) (fun m -> m) false 0;
			    if (allstrictp locevars n2) then
			      apply_pattern_clause_eqn c n a n2 n1 (normneg m) (fun m -> m) true 0
			  end
		      | _ ->
			  begin
			    apply_pattern_clause_eqn c n a n1 n2 (normneg m) (fun m -> m) false 0;
			    apply_pattern_clause_eqn c n a n2 n1 (normneg m) (fun m -> m) true 0
			  end
		    end
		| _ -> ()
	      end
	    | None -> ()
	  )
	  begin
	    match strictlitsopt with
	    | Some strictlits -> strictlits
	    | None -> unmatched
	  end
      end
  end
(*** n is an unmatched literal, try matching against m ***)
and apply_pattern_clause_1 {nalllit; locevars; unmatched; abslits; dlist; strictlitsopt; rew; ml; pl; il; cg} n mlit m =
  try
    begin
      if (!verbosity > 40) then
	begin
	  Printf.printf "** Trying to match %s\n" (metatrm_str n)
	end;
      let evarassoc = ref [] in
      let locevars2 = ref [] in
      List.iter
	(fun (e,x) ->
	  match (!x) with
	  | Some xn -> ()
	  | None ->
	      begin
		let y = copy_evar (!verbosity) (e,x) in
		evarassoc := ((e,y)::(!evarassoc));
		locevars2 := (y::(!locevars2))
	      end)
	locevars;
      let nc = meta_copy n (!evarassoc) in
      let dlistc = List.map (fun (gamma0,m0,n0,b0) -> (gamma0,meta_copy m0 (!evarassoc),n0,b0)) dlist in
      if (!verbosity > 40) then
	begin
	  Printf.printf "*** Calling pattern_match with dpairs\n";
	  List.iter
	    (fun (_,m0,n0,b0) ->
	      Printf.printf ". %s\n =? %s\n : %s\n" (metatrm_str m0) (trm_str n0) (stp_str b0)
	    )
	    (([],nc,m,Prop)::dlistc)
	end;
      let dlist2 = pattern_match (([],nc,m,Prop)::dlistc) in
      if (!verbosity > 40) then
	begin
	  Printf.printf "*** Matched - locevars2\n";
	  List.iter
	    (fun (e,x) ->
	      match (!x) with
	      | Some n -> Printf.printf "%s := %s\n" (string_of_evar (e,x)) (metatrm_str n)
	      | None -> Printf.printf "%s\n" (string_of_evar (e,x))
	    )
	    (!locevars2);
	  Printf.printf "*** remaining dpairs\n";
	  List.iter
	    (fun (_,m0,n0,b0) ->
	      Printf.printf ". %s\n =? %s\n : %s\n" (metatrm_str m0) (trm_str n0) (stp_str b0)
	    )
	    dlist2
	end;
      let unmatched2 = ref [] in
      let abslits2 = ref (mlit::abslits) in
      List.iter
	(fun p ->
	  if (not (p == n)) then (*** skip this one, because mlit was already put onto abslits2 ***)
	    begin
	      let p = (meta_copy p (!evarassoc)) in
	      if (!verbosity > 40) then
		Printf.printf "p = %s\n" (metatrm_str p);
	      try
		let p2 = meta_to_ground name_def p in
		if (!verbosity > 40) then
		  Printf.printf "p2 = %s\n" (trm_str p2);
		let gl = get_literal p2 in
		if (List.mem (- gl) (!abslits2)) then
		  raise TrivialClause
		else if (not (List.mem gl (!abslits2))) then
		  begin
		    insertWithPriority (get_int_flag "PATTERN_CLAUSES_DELAY") (ProcessProp1 p2);
		    abslits2 := (gl::(!abslits2))
		  end
	      with
	      | NotGround ->
		  unmatched2 := (p::(!unmatched2));
	    end
	)
	unmatched;
      match (!unmatched2) with
      | (_::_) ->
	  (*** If we are here, then strictlitsopt is None. ***)
	  let mlc = List.map (fun m0 -> meta_copy m0 (!evarassoc)) ml in
	  let plc = List.map (fun m0 -> meta_copy m0 (!evarassoc)) pl in
	  let ilc = List.map (fun m0 -> meta_copy m0 (!evarassoc)) il in
	  let rewc =
	    begin
	      match rew with
	      | Some rll -> Some (List.map (fun (b,a,ml0) -> (b,a,List.map (fun m0 -> meta_copy m0 (!evarassoc)) ml0)) rll)
	      | None -> None
	    end
	  in
	  new_pattern_clause_3 {nalllit; locevars = !locevars2; unmatched = !unmatched2; abslits = !abslits2; dlist = dlist2; strictlitsopt; rew = rewc; ml = mlc; pl = plc; il = ilc; cg}
      | [] ->
	  begin (*** clause has been fully instantiated ***)
	    match (dlist2) with
	    | (_::_) ->
		begin
		  raise (GenericError "Match succeeded, but left disagreement pairs. Bug")
		end
	    | _ ->
		begin
		  try
		      let mlc2 = List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) ml in
		      let plc2 = List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) pl in
		      let ilc2 = List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) il in
		      let rewc2 =
			begin
			  match rew with
			  | Some rll -> (List.map (fun (b,a,ml0) -> (b,a,List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) ml0)) rll)
			  | None -> []
			end
		      in
		      apply_pattern_clause_2 nalllit mlc2 plc2 ilc2 rewc2 cg
		  with
		  | NotGround ->
		      raise (GenericError ("Match succeeded, but something is unexpectedly not ground(1)"))
		end
	  end
    end
  with
  | TrivialClause -> ()
  | PatternMatchFailed -> ()
(*** Rewrite with in m equation n:n1 =(a) n2 ***)
(*** If rev, then n is actually n2 =(a) n1. ***)
and apply_pattern_clause_eqn ({nalllit; locevars; unmatched; abslits; dlist; strictlitsopt; rew; ml; pl; il; cg} as c) n a n1 n2 m ctx rev indx =
  if (!verbosity > 40) then Printf.printf "** apply_pattern_clause_eqn %s\n" (trm_str m);
  let b = tpof m in
  if ((a = b) && (termNoDBs m)) then
    begin
      try
	if (!verbosity > 40) then
	  begin
	    Printf.printf "** Trying to match %s\nwith subterm %s\n" (metatrm_str n1) (trm_str m)
	  end;
	let evarassoc = ref [] in
	let locevars2 = ref [] in
	List.iter
	  (fun (e,x) ->
	    match (!x) with
	    | Some xn -> ()
	    | None ->
		begin
		  let y = copy_evar (!verbosity) (e,x) in
		  evarassoc := ((e,y)::(!evarassoc));
		  locevars2 := (y::(!locevars2))
		end)
	  locevars;
	let nc = meta_copy n1 (!evarassoc) in
	let dlistc = List.map (fun (gamma0,m0,n0,b0) -> (gamma0,meta_copy m0 (!evarassoc),n0,b0)) dlist in
	if (!verbosity > 40) then
	  begin
	    Printf.printf "*** Calling pattern_match with dpairs\n";
	    List.iter
	      (fun (_,m0,n0,b0) ->
		Printf.printf ". %s\n =? %s\n : %s\n" (metatrm_str m0) (trm_str n0) (stp_str b0)
	      )
	      (([],nc,m,a)::dlistc)
	  end;
	let dlist2 = pattern_match (([],nc,m,a)::dlistc) in
	if (!verbosity > 40) then
	  begin
	    Printf.printf "*** Matched - locevars2\n";
	    List.iter
	      (fun (e,x) ->
		match (!x) with
		| Some n -> Printf.printf "%s := %s\n" (string_of_evar (e,x)) (metatrm_str n)
		| None -> Printf.printf "%s\n" (string_of_evar (e,x))
	      )
	      (!locevars2);
	    Printf.printf "*** remaining dpairs\n";
	    List.iter
	      (fun (_,m0,n0,b0) ->
		Printf.printf ". %s\n =? %s\n : %s\n" (metatrm_str m0) (trm_str n0) (stp_str b0)
	      )
	      dlist2
	  end;
	let unmatched2 = ref [] in
	let abslits2 = ref abslits in
	List.iter
	  (fun p ->
	    let p = (meta_copy p (!evarassoc)) in
	    if (!verbosity > 40) then
	      Printf.printf "p = %s\n" (metatrm_str p);
	    try
	      let p2 = meta_to_ground name_def p in
	      if (!verbosity > 40) then
		Printf.printf "p2 = %s\n" (trm_str p2);
	      let gl = get_literal p2 in
	      if (List.mem (- gl) (!abslits2)) then
		raise TrivialClause
	      else if (not (List.mem gl (!abslits2))) then
		begin
		  insertWithPriority (get_int_flag "PATTERN_CLAUSES_EQN_DELAY") (ProcessProp1 p2);
		  abslits2 := (gl::(!abslits2))
		end
	    with
	    | NotGround ->
		unmatched2 := (p::(!unmatched2));
	  )
	  ((metanorm (ctx n2))::unmatched); (** Replace n with C[n2] **)
	match (!unmatched2) with
	| (_::_) ->
	  (*** If we are here, then strictlitsopt is None ***)
	    let mlc = List.map (fun m0 -> meta_copy m0 (!evarassoc)) ml in
	    let plc = List.map (fun m0 -> meta_copy m0 (!evarassoc)) pl in
	    let ilc = List.map (fun m0 -> meta_copy m0 (!evarassoc)) il in
	    let n2c = meta_copy n2 (!evarassoc) in
	    let rewc =
	      begin
		match rew with
		| Some rll -> Some ((rev,a,[MLam(a,ctx (MGround(DB(indx,a))));nc;n2c;ctx nc;ctx n2c])::(List.map (fun (b,a,ml0) -> (b,a,List.map (fun m0 -> meta_copy m0 (!evarassoc)) ml0)) rll))
		| None -> None
	      end
	    in
	    new_pattern_clause_3 {nalllit; locevars = !locevars2; unmatched = !unmatched2; abslits = !abslits2; dlist = dlist2; strictlitsopt; rew = rewc; ml = mlc; pl = plc; il = ilc; cg}
	| [] ->
	    begin (*** clause has been fully instantiated ***)
	      match (dlist2) with
	      | (_::_) ->
		  begin
		    raise (GenericError "Match succeeded, but left disagreement pairs. Bug")
		  end
	      | _ ->
		  begin
		    try
		      let mlc2 = List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) ml in
		      let plc2 = List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) pl in
		      let ilc2 = List.map (fun m0 -> meta_to_ground name_def (meta_copy m0 (!evarassoc))) il in
		      let n2c = meta_copy n2 (!evarassoc) in
		      let rewc2 =
			begin
			  match rew with
			  | Some rll ->
			      let rewc = ((rev,a,[MLam(a,ctx (MGround(DB(indx,a))));nc;n2c;ctx nc;ctx n2c])::(List.map (fun (b,a,ml0) -> (b,a,List.map (fun m0 -> meta_copy m0 (!evarassoc)) ml0)) rll)) in
			      List.map (fun (re,a,ml) -> (re,a,List.map (fun m -> meta_to_ground name_def m) ml)) rewc
			  | None -> []
			end
		      in
		      apply_pattern_clause_2 nalllit mlc2 plc2 ilc2 rewc2 cg
		    with
		    | NotGround ->
			raise (GenericError ("Match succeeded, but something is unexpectedly not ground(2)"))
		  end
	    end
      with
      | TrivialClause -> ()
      | PatternMatchFailed -> ()
    end;
  match m with
  | Lam(b1,m1) -> apply_pattern_clause_eqn c n a n1 n2 m1 (fun m1 -> ctx (MLam(b1,m1))) rev (indx + 1)
  | Ap(m1,m2) ->
      apply_pattern_clause_eqn c n a n1 n2 m1 (fun m1 -> ctx (MAp(m1,to_meta m2))) rev indx;
      apply_pattern_clause_eqn c n a n1 n2 m2 (fun m2 -> ctx (MAp(to_meta m1,m2))) rev indx
  | _ -> ()
and new_pattern_clause_3 ({nalllit;locevars;unmatched;abslits;dlist;strictlitsopt;rew;ml;pl;il;cg} as c) = (*** Process a new clause by trying it with every ground formula encountered so far. ***)
  if (!verbosity > 40) then
    begin
      Printf.printf "* new_pattern_clause_3 ";
	  begin
	    Printf.printf "%d\n" nalllit;
	    Printf.printf "locevars\n";
	    List.iter
	      (fun (e,x) ->
		match (!x) with
		| Some n -> Printf.printf "%s := %s\n" (string_of_evar (e,x)) (metatrm_str n)
		| None -> Printf.printf "%s\n" (string_of_evar (e,x))
	      )
	      locevars;
	    Printf.printf "unmatched\n";
	    List.iter
	      (fun m -> Printf.printf "%s\n" (metatrm_str m))
	      unmatched;
	    Printf.printf "abslits";
	    List.iter
	      (fun m -> Printf.printf " %d" m)
	      abslits;
	    Printf.printf "\ndlist:\n";
	    List.iter
	      (fun (_,m0,n0,b0) ->
		Printf.printf ". %s\n =? %s\n : %s\n" (metatrm_str m0) (trm_str n0) (stp_str b0)
	      )
	      dlist;
	    begin
	      match strictlitsopt with
	      |	Some strictlits ->
		  begin
		    Printf.printf "strict lits\n";
		    List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m)) strictlits
		  end
	      |	_ -> ()
	    end;
	    Printf.printf "ml\n";
	    List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m)) ml;
	    Printf.printf "pl\n";
	    List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m)) pl;
	    Printf.printf "il\n";
	    List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m)) il;
	  end;
	  Printf.printf "** apply new clause to all usable BEGIN\n"
    end;  
  List.iter (fun (mlit,m) -> apply_pattern_clause c mlit m)
    (!pattern_clauses_usable);
  if (!verbosity > 40) then
    Printf.printf "** apply new clause to all usable END\n";
  pattern_clauses := (c::!pattern_clauses)

(*** Create a new pattern clause, possibly computing the strict literals and eqn lits depending on flag settings. ***)
let new_pattern_clause_3a nalllit evars unmatched abslits dlist ml pl il cg =
  if (!pattern_clauses_onlyallstrict) then
    begin
      let strictlits = ref [] in
      List.iter
	(fun p ->
	  if (allstrictp evars p) then
	      strictlits := (p::(!strictlits))
	)
	unmatched;
      match (!strictlits) with
      | (_::_) ->
	  new_pattern_clause_3 {nalllit; locevars = evars;unmatched;abslits;dlist; strictlitsopt = Some !strictlits; rew = if (!pattern_clauses_eqnlits) then Some [] else None; ml; pl; il; cg}
      | [] -> () (*** No strict literals, so drop the pattern clause. ***)
    end
  else
    new_pattern_clause_3 {nalllit; locevars = evars; unmatched; abslits; dlist; strictlitsopt = None; rew = if (!pattern_clauses_eqnlits) then Some [] else None; ml; pl; il; cg}

(*** Apply all pattern clauses so far against the negation of the new ground formula m ***)
let apply_pattern_clauses mlit m =
  if (!verbosity > 40) then
    begin
      Printf.printf "* apply_pattern_clauses %d %s\n" mlit (trm_str m)
    end;
  let nm = normneg m in (*** Dec 28, 2010 - Chad: We should match against the negation of m. ***)
  let nmlit = (- mlit) in
  begin
    if (!verbosity > 40) then Printf.printf "apply_pattern_clauses called with mlit %d\n" mlit;
    pattern_clauses_usable := (nmlit,nm)::(!pattern_clauses_usable);
    List.iter (fun c -> apply_pattern_clause c nmlit nm) (!pattern_clauses)
  end

let rec new_pattern_clauses_2 nalllit ml evars strict unmatched abslits remp remi cg =
  if (!verbosity > 40) then
    begin
      Printf.printf "* new_pattern_clauses_2 ";
      Printf.printf "%d\n" nalllit;
      Printf.printf "ml\n";
      List.iter
	(fun m -> Printf.printf "%s\n" (metatrm_str m))
	ml;
      Printf.printf "evars\n";
      List.iter
	(fun (e,x) ->
	  match (!x) with
	  | Some n -> Printf.printf "%s := %s\n" (string_of_evar (e,x)) (metatrm_str n)
	  | None ->
	      if (mem_evar (e,x) strict) then
		Printf.printf "%s (strict)\n" (string_of_evar (e,x))
	      else
		Printf.printf "%s\n" (string_of_evar (e,x))
	)
	evars;
      Printf.printf "unmatched\n";
      List.iter
	(fun m -> Printf.printf "%s\n" (metatrm_str m))
	unmatched;
      Printf.printf "abslits";
      List.iter
	(fun m -> Printf.printf " %d" m)
	abslits;
      Printf.printf "\nremp\n";
      List.iter
	(fun m -> Printf.printf "%s\n" (metatrm_str m))
	remp;
      Printf.printf "remi\n";
      List.iter
	(fun m -> Printf.printf "%s\n" (metatrm_str m))
	remi;
    end;  
  match ml with
  | (MGround(False)::mr) -> (*** If it's false, then drop the corresponding lit ***)
      new_pattern_clauses_2 nalllit mr evars strict unmatched abslits remp remi
	(fun ml ll pl il ->
	  new_search_clause [(- (get_literal False))] (if (mkprooftermp()) then (Some(PosPropRule(False))) else None);
	  cg (False::ml) ll pl il)
  | (MAp(MAp(MGround(Imp),MGround(False)),MGround(False))::mr) -> () (*** If it's true, then all clauses would be useless ***)
  | (((MAp(MAp(MGround(Imp),m1),MGround(False))) as m)::mr) -> (*** ~m1::mr, treat m1 as a literal only ***)
      new_pattern_clauses_2a nalllit m mr evars strict unmatched abslits remp remi cg
  | (MAp(MAp(MGround(Imp),MAp(MAp(MGround(Imp),m1),MGround(False))),m2)::mr) ->  (*** (~m1 -> m2)::mr, rec call with m1::m2::mr ***)
      new_pattern_clauses_2 nalllit (m1::m2::mr) evars strict unmatched abslits
	remp remi
	(fun ml ll pl il ->
	  match ml with
	  | (m1::m2::mr) ->
	      let m = imp (normneg m1) m2 in
	      begin
		new_search_clause [(- (get_literal m));(get_literal m1);(get_literal m2)]
		  (if (mkprooftermp ()) then (Some(PosPropRule(m))) else None);
		cg (m::mr) ll pl il
	      end
	  | _ -> raise (GenericError "Bug in Code for Pattern Clauses 2"))
  | (MAp(MAp(MGround(Imp),m1),m2)::mr) -> (*** (m1 -> m2)::mr, rec call with ~m1::m2::mr ***)
      let m1n = (MAp(MAp(MGround(Imp),m1),MGround(False))) in
      new_pattern_clauses_2 nalllit (m1n::m2::mr) evars strict unmatched abslits
	remp remi
	(fun ml ll pl il ->
	  match ml with
	  | (m1n::m2::mr) ->
	      let m1 = normneg m1n in
	      let m = imp m1 m2 in
	      begin
		new_search_clause [(- (get_literal m));(get_literal m1n);(get_literal m2)]
		  (if (mkprooftermp ()) then (Some(PosPropRule(m))) else None);
		cg (m::mr) ll pl il
	      end
	  | _ -> raise (GenericError "Bug in Code for Pattern Clauses 3"))
  | (m::mr) ->
      begin
	begin (*** Treat formula as a literal in the clause (unless it's a forall, then whether or not we do depends on a flag.) ***)
	  match m with
	  | MAp(MGround(Forall(a)),m1) ->
	      if (!pattern_clauses_forall_as_lit) then (*** Use pattern_clauses_forall_as_lit which is (get_bool_flag "PATTERN_CLAUSES_FORALL_AS_LIT"), unless we've temporarily changed it. ***)
		new_pattern_clauses_2a nalllit m mr evars strict unmatched abslits remp remi cg
	  | _ ->
	      new_pattern_clauses_2a nalllit m mr evars strict unmatched abslits remp remi cg
	end;
	(*** If it's a forall, then make it an evar ***)
	if (!verbosity > 40) then Printf.printf "** Treating first metawff as a forall:\n%s\n" (metatrm_str m);
	match m with
	| MAp(MGround(Forall(a)),((MLam(_,m1)) as p1)) when (metatermNotFreeIn m1 0) -> (*** trivial quantifier, go beneath without making an evar ***)
	    new_pattern_clauses_2 nalllit
	      ((metashift m1 0 (-1))::mr)
	      evars strict unmatched abslits
	      (p1::remp) remi
	      (fun ml ll pl il ->
		match (ml,pl) with
		| ((m1::mr),(p1::pr)) ->
		    let m = Ap(Forall(a),p1) in
		    new_search_clause [(- (get_literal m));(get_literal m1)]
		      (if (mkprooftermp ()) then (Some(InstRule(a,p1,let (_,w) = get_fresh_name a in w (*** This could be anything of the right type. Taking a fresh name emphasizes this. ***)
							       )))
		      else None);
		    cg (m::mr) ll pr il
		| _ -> raise (GenericError "Bug in Code for Pattern Clauses 4"))
	| MAp(MGround(Forall(a)),((MLam(_,m1)) as p1)) -> (*** make an evar ***)
	    let (x,xsub) = new_evar (!verbosity) [] a in
	    new_pattern_clauses_2 nalllit
	      ((metanorm (metasubst m1 0 xsub))::mr)
	      (x::evars) strict unmatched abslits
	      (p1::remp) (xsub::remi)
	      (fun ml ll pl il ->
		match (ml,pl,il) with
		| ((m1::mr),(p1::pr),(i1::ir)) ->
		    let m = Ap(Forall(a),p1) in
		    new_search_clause [(- (get_literal m));(get_literal m1)]
		      (if (mkprooftermp ()) then (Some(InstRule(a,p1,i1))) else None);
		    cg (m::mr) ll pr ir
		| _ -> raise (GenericError "Bug in Code for Pattern Clauses 5"))
	| _ -> ()
      end
  | [] ->
      begin
	match evars with
	| [] -> ()
	| _ ->
	    try
	      let ns = List.find (fun x -> (not (mem_evar x strict))) evars in
	      if (!verbosity > 40) then
		Printf.printf "Cannot make a pattern clause, nonstrict evar %s\n" (string_of_evar ns);
	    with
	    | Not_found ->
		begin
		  if (!verbosity > 4) then
		    begin
		      Printf.printf "Creating new pattern clause for %d: %s\n%s\n"
			(-nalllit)
			(String.concat " " (List.map string_of_evar evars))
			(String.concat " " (List.map string_of_int abslits));
		      List.iter (fun m -> Printf.printf ". %s\n" (metatrm_str m))
			unmatched
		    end;
		  new_pattern_clause_3a nalllit evars unmatched abslits [] unmatched remp remi cg
		end
      end
and new_pattern_clauses_2a nalllit m mr evars strict unmatched abslits remp remi cg =
  try
    let m0 = meta_to_ground name_def m in
    (*** If there are no free evars in the formula m, then put it on abslits, not unmatched ***)
    insertWithPriority (get_int_flag "PATTERN_CLAUSES_DELAY") (ProcessProp1 m0); (*** Also put it on the queue to be processed. ***)
    let m0l = get_literal m0 in
    new_pattern_clauses_2 nalllit mr evars strict unmatched (m0l::abslits) remp remi
      (fun ml ll pl il -> cg (m0::ml) ll pl il)
  with
  | NotGround ->
      new_pattern_clauses_2 nalllit mr evars (update_strict strict m) (m::unmatched) abslits remp remi
      (fun ml ll pl il ->
	match ll with
	| (l::lr) -> cg (l::ml) lr pl il
	| _ -> raise (GenericError "Bug in Code for Pattern Clauses 6"))

(*** nalllit is something the literal of the negation of a forall formula; m is the forall formula ***)
let new_pattern_clauses nalllit m =
 let mm = to_meta m in
 new_pattern_clauses_2 nalllit [mm] [] [] [] [] [] [] (fun _ _ _ _ -> ());;
