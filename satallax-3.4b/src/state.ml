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

exception CoqProofTooBig of int

let clauses : clause list ref = ref []
let clausesTable : (clause,unit) Hashtbl.t = Hashtbl.create 10

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

let conjecturename : string ref = ref "claim"
let conjecture : (trm * trm) option ref = ref None
type proofkind = TSTP | CoqScript | CoqSPfTerm | HOCore | Model | ModelTrue | IsarScript | PfInfo | PfUseful | PfFormdeps
let mkproofterm = ref None
let mkprooftermp () = OptionE.is_some !mkproofterm
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
let name_base_list : string list ref = ref []
let name_tp : (string,stp) Hashtbl.t = Hashtbl.create 100
let name_trm : (string,(trm * stp) * bool ref) Hashtbl.t = Hashtbl.create 100
let name_trm_list : (string * trm * stp) list ref = ref []
let translucent_defns : bool ref = ref false
let name_def_empty : (string,trm) Hashtbl.t = Hashtbl.create 1
let name_def : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_def_all : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_def_prenorm : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_hyp : (string,trm) Hashtbl.t = Hashtbl.create 100
let name_hyp_inv : (trm,string * trm) Hashtbl.t = Hashtbl.create 100 (*** associate a normalized/logic normalized term with the name of the assumption it came from and its original prenormalized form ***)
let assumption_lit : (int,trm * trm) Hashtbl.t = Hashtbl.create 100 (*** associate assumption literals with their term after preprocessing and before preprocessing ***)

(** applies neg-, beta- and delta-normalization**)
let coqnorm m =
  let m = betanorm name_def_prenorm m in
  let (n,_) = negnorm1 m in n
(** partially normalizes, without expanding certain defns (e.g., is_of) **)
let partialnormalize pt = norm name_def (logicnorm pt)
(** applies full satallax normalization**)
let normalize pt = norm name_def_all (logicnorm pt)
let belnorm pt = norm name_def_empty (logicnorm pt)

let coqknown (x,y) =
  if (!coq2) then y else x

let mult_timeout f =
  match (!timeout) with
  | Some tm -> timeout := Some (tm *. f)
  | None -> ()

let requireSet0a () =
  let a = Base "set" in
  let b = PName "set" in
  Hashtbl.add coq_used_names "In" ();
  Hashtbl.add coq_used_names "Subq" ();
  Hashtbl.add coq_names "In" "In";
  Hashtbl.add coq_names "Subq" "Subq";
  coqsig_const := ("In",Ar(a,Ar(a,Prop)))::!coqsig_const;
  coqsig_const := ("Subq",Ar(a,Ar(a,Prop)))::!coqsig_const;
  coqsig_def := ("Subq",PLam([("x",b);("y",b)],PAll(["z",b],PAp(PAp(PImplies,PAp(PAp(PName "In",PName "z"),PName "x")),PAp(PAp(PName "In",PName "z"),PName "y")))))::!coqsig_def;
  coqsig_def_trm := ("Subq",Lam(a,Lam(a,Ap(Forall(a),Lam(a,Ap(Ap(Imp,Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(2,a))),Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(1,a))))))))::!coqsig_def_trm;
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
  let trm = Name(x,tp) in
  Hashtbl.add name_tp x tp;
  Hashtbl.add name_trm x ((trm, tp), ref false);
  name_trm_list := (x, trm, tp)::!name_trm_list

(*** March 31, 2011 - Chad - THF policy regarding definitions. (See comments before declare_definition_real below. ***)
exception TreatAsAssumption

let next_fresh_name : int ref = ref 0

let rec get_fresh_name a =
  let x = make_fresh_name !next_fresh_name in
  incr next_fresh_name;
  if !coq then ignore (coqify_name x coq_names coq_used_names);
  if ((Hashtbl.mem name_base x) || (Hashtbl.mem name_tp x)) then
    get_fresh_name a
  else
    begin
      declare_name_type x a;
      (x, Name(x, a))
    end


let initial_branch : trm list ref = ref []
let initial_branch_prenorm : trm list ref = ref []

let processed : (trm,int) Hashtbl.t = Hashtbl.create 100
let clause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref = ref (Hashtbl.create 100)

let allclauses : clause list ref = ref [] (* allclauses is only used if formdeps is activated, in which case someone wants useless information. it contains all the clauses that were used in all searches across different subgoals; doesn't get reset. Aug 2016 *)
let allclause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref = ref (Hashtbl.create 100)

exception DuplicateClause

let insert_clause c r =
(***  (Printf.printf "inserting search clause %s: %s\n" (List.fold_left (fun x y -> if ((String.length x) == 0) then (string_of_int y) else (x ^ " " ^ (string_of_int y))) "" c) (match r with (Some r) -> (ruleinfo_str r) | _ -> "None"); flush stdout); ***)
  if (Hashtbl.mem clausesTable c) then
    (*** Chad: April 4, 2011: Check if the clause has already been added before.  If it has, raise DuplicateClause. (Otherwise, we may end up with bad rule info -- e.g., a later rule which will violate freshness) ***)
(***    Printf.printf "duplicate clause %s: %s\n" (List.fold_left (fun x y -> if ((String.length x) == 0) then (string_of_int y) else (x ^ " " ^ (string_of_int y))) "" c) (match r with (Some r) -> (ruleinfo_str r) | _ -> "None"); flush stdout; ***)
     raise DuplicateClause
  else
    begin
      Hashtbl.add clausesTable c ();
      clauses := c::!clauses;
      if !mkproofterm = Some(PfFormdeps) then allclauses := c::!allclauses;
      match r with
      | Some(r) ->
	  Hashtbl.add (!clause_ruleinfo) c r;
	  if !mkproofterm = Some(PfFormdeps) then
	    Hashtbl.add (!allclause_ruleinfo) c r;
      | None -> ()
    end



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
	raise (Unsatisfiable (Some (AssumptionConflictR(l))))
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
	raise (Unsatisfiable (Some (SearchR (minclauses, Hashtbl.find cri))))
      else
	raise (Unsatisfiable None)

let patoms : (string,int * (trm list)) Hashtbl.t = Hashtbl.create 10
let natoms : (string,int * (trm list)) Hashtbl.t = Hashtbl.create 10

let pchoiceatoms : (stp,int * (trm list)) Hashtbl.t = Hashtbl.create 10
let nchoiceatoms : (stp,int * (trm list)) Hashtbl.t = Hashtbl.create 10

let peqns : (string,int * trm * trm) Hashtbl.t = Hashtbl.create 10
let neqns : (string,int * trm * trm) Hashtbl.t = Hashtbl.create 10

let univpreds : (stp,(int * trm)) Hashtbl.t = Hashtbl.create 10
let instantiations : (stp,(trm,unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 10
let instantiationslist : (stp,trm list) Hashtbl.t = Hashtbl.create 10
let default_elts : (string,trm) Hashtbl.t = Hashtbl.create 10

let set_default_elt aname x = Hashtbl.add default_elts aname x

let set_default_elt_if_needed a x =
  match a with
  | Base(aname) ->
      if (not (Hashtbl.mem default_elts aname)) then set_default_elt aname x
  | _ -> ()

let default_elt aname =
  try
    Hashtbl.find default_elts aname
  with
  | Not_found ->
      let a = Base aname in
      let (_,x) = get_fresh_name a in
      begin
	set_default_elt aname x;
	x
      end

let default_elt_p aname =
  Hashtbl.mem default_elts aname

let get_instantiations a =
  try
    Hashtbl.find instantiationslist a
  with Not_found -> []

let known_instantiation a m =
  try
    let h = Hashtbl.find instantiations a in
    Hashtbl.find h m;
    true
  with Not_found -> false

let cons_instantiation m ml =
    let iordcyc = get_int_flag "INSTANTIATION_ORDER_CYCLE" in
    let iordmask = get_int_flag "INSTANTIATION_ORDER_MASK" in
    if (iordcyc < 2) then
      begin
	if (iordmask mod 2 = 0) then
	  (m::ml)
	else
	  (ml @ [m])
      end
    else
      let j = List.length ml mod iordcyc in
      begin
	if ((iordmask lsr j) mod 2 = 0) then
	  (m::ml)
	else
	  (ml @ [m])
      end

let add_instantiation_2 a m =
  try
    let ml = Hashtbl.find instantiationslist a in
    Hashtbl.replace instantiationslist a (cons_instantiation m ml)
  with Not_found ->
    Hashtbl.add instantiationslist a [m]

let add_instantiation a m =
  try
    let h = Hashtbl.find instantiations a in
    Hashtbl.add h m ();
    add_instantiation_2 a m;
    set_default_elt_if_needed a m
  with Not_found ->
    let h : (trm,unit) Hashtbl.t = Hashtbl.create 10 in
    Hashtbl.add instantiations a h;
    Hashtbl.add h m ();
    add_instantiation_2 a m;
    set_default_elt_if_needed a m

let choiceopnames : (string,(stp * trm * trm)) Hashtbl.t = Hashtbl.create 10

let choiceop_axiom m =
  match m with
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap (Forall _,
		 Lam (_,
		      Ap (Ap (Imp, Ap (DB (1, Ar (_, Prop)), DB (0, _))),
			  Ap (DB (1, Ar (_, Prop)),
			      Ap (Name (x, Ar (Ar (_, Prop), _)),
				  DB (1, Ar (_, Prop)))))))))
    -> Some(x,a)
  | Ap (Forall (Ar (a, Prop)),
	Lam (Ar (_, Prop),
	     Ap
	       (Ap (Imp,
		    Ap
		      (Ap (Imp,
			   Ap (Forall _,
			       Lam (_,
				    Ap (Ap (Imp, Ap (DB (1, Ar (_, Prop)), DB (0, _))),
					False)))),
		       False)),
		Ap (DB (0, Ar (_, Prop)),
		    Ap (Name (x, Ar (Ar (_, Prop), _)),
			DB (0, Ar (_, Prop)))))))
    -> Some(x,a)
  | _ -> None

let declare_choiceop x a (m,mb) = Hashtbl.add choiceopnames x (a,m,mb)

let choiceop m =
  match m with
  | Choice(a) -> Some(a)
  | Name(x,_) ->
      begin
	try
	  let (a,_,_) = Hashtbl.find choiceopnames x in
	  Some(a)
	with
	| Not_found -> None
      end
  | _ -> None

let filtered : (int,unit) Hashtbl.t = Hashtbl.create 10

let part_of_conjecture : (trm,unit) Hashtbl.t = Hashtbl.create 10

type namecategory =
    ChoiceOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary choice operator (in particular, tl[i] is this one) ***)
   | DescrOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary description operator (in particular, tl[i] is this one) ***)
   | IfThenElse of int * int * stp list (*** (i,n,sigmal) where length of sigmal is n, 0 <= i < n, Name has type o -> sigmal -> sigmal -> sigmal[i] ***)
   | ReflexiveBinary
   | IrreflexiveBinary
   | SymmetricBinary
   | ReflexiveSymmetricBinary
   | IrreflexiveSymmetricBinary

let constrainedName : (string,namecategory) Hashtbl.t = Hashtbl.create 10

let decomposable x =
   try
   let c = Hashtbl.find constrainedName x in (*** Some categorized names are decomposable and some are not ***)
   match c with
   | IfThenElse _ -> false (*** TO DO: Check that n-ary if-then-else need not be decomposable ***)
   (*** TO DO: Should *Binary cases be decomposable? ***)
   | _ -> true
   with Not_found -> true (*** A name is decomposable by default ***)

(*** Set completep to false if I use a mode that makes the search incomplete, so that failure does not imply satisfiability.
     Currently there is no such mode. - Chad, Oct 2010 ***)
let completep = ref true

let get_timeout_default x = match (!timeout) with Some y -> y | None -> x

let st_include_fun : (string -> unit) ref = ref (fun x -> raise (GenericError("Bug when including file " ^ x)))
let st_find_read_thf_fun : (string -> string -> unit) ref = ref (fun d x -> raise (GenericError("Bug when including file " ^ x)))

let print_coqsig c =
  let rec print_coqsig_base l =
    match l with
        (x :: r) ->
	        print_coqsig_base r;
          if !mkproofterm = Some IsarScript then
            if x <> "i" (*FIXME "$i"="i"*) then
              (*there's no need to redeclare $i*)
              (*FIXME to avoid name clashes, could suffix names with something*)
              Printf.fprintf c "typedecl %s\n" x
            else ()
	  else if !mkproofterm = Some TSTP then (* Don't print Coq declarations when tstp was requested. Chad, May 3 2016 *)
	    ()
          else
	    if (not (!coq2)) then Printf.fprintf c "Variable %s:SType.\n" x
      | [] -> ()
  in
  let rec print_coqsig_const l =
    match l with
        ((x, a) :: r) ->
	        begin
	          print_coqsig_const r;
	          try
	            ignore (List.assoc x (!coqsig_def));
	          with
	            | Not_found ->
	                begin
		          try
			    if !mkproofterm = Some IsarScript then
                              begin
				Printf.fprintf c "consts %s :: \"" x;
				print_stp_isar c a (* coq_names *) false;
		                Printf.fprintf c "\"\n"
                              end
			    else if !mkproofterm = Some TSTP then (* Don't print Coq declarations when tstp was requested. Chad, May 3 2016 *)
			      ()
			    else
                              begin
				Printf.fprintf c "Variable %s : " x;
				if (!coq2) then print_stp_coq2 c a false else print_stp_coq c a coq_names false;
				Printf.fprintf c ".\n"
                              end
		          with
		          | Not_found ->
		              begin
		                if (c != stdout) then close_out c;
		                raise (GenericError("A Satallax bug caused a problem creating the Coq/Isar file."))
		              end
	                end
	        end
      | [] -> ()
  in
  let rec print_coqsig_def l =
    match l with
        ((x,a)::r) ->
	        begin
	          print_coqsig_def r;
	          try
	            let m = List.assoc x (!coqsig_def) in
                    if !mkproofterm = Some IsarScript then
	              begin
	                Printf.fprintf c "definition %s :: \"" x;
	                print_stp_isar c a (* coq_names *) false;
	                Printf.fprintf c "\"\n where \"%s == (" x;
	                print_pretrm_isar c m coq_names coq_used_names (-1) (-1);
	                Printf.fprintf c ")\"\n"
	              end
                    else if !mkproofterm = Some TSTP then (* Don't print Coq declarations when tstp was requested. Chad, May 3 2016 *)
		      ()
                    else
	              begin
	                Printf.fprintf c "Definition %s : " x;
	                if (!coq2) then print_stp_coq2 c a false else print_stp_coq c a coq_names false;
	                Printf.fprintf c "\n := ";
	                if (!coq2) then print_pretrm_coq2 c m (-1) (-1) else print_pretrm_coq c m coq_names coq_used_names (-1) (-1);
	                Printf.fprintf c ".\n"
	              end
	          with
	          | Not_found -> ()
	        end
    | [] -> ()
  in
  let rec print_coqsig_hyp l =
    match l with
      ((x, t)::r) ->
	begin
	  try
            if !mkproofterm = Some IsarScript then
	      begin
	        print_coqsig_hyp r;
	        Printf.fprintf c "assumes %s : \"" x;
	                (* print_pretrm_isar c m coq_names coq_used_names (-1) (-1); *)
                trm_to_isar c (coqnorm t) (TermP.Variables.make ());
	        Printf.fprintf c "\"\n"
              end
            else if !mkproofterm = Some CoqScript then
                (*have Syntax.trm but need Syntax.pretrm, so look it up*)
              let pt = List.assoc x !coqsig_hyp in
	      begin
	        Printf.fprintf c "Hypothesis %s : " x;
	        if (!coq2) then print_pretrm_coq2 c pt (-1) (-1) else print_pretrm_coq c pt coq_names coq_used_names (-1) (-1);
	        Printf.fprintf c ".\n"
              end
	    else if !mkproofterm = Some TSTP then (* I have no idea why I was printing Coq Hypotheses when tstp was requested. - Chad, May 3 2016 *)
	      ()
            else
              failwith "Printing of hypotheses: Unrecognised proof-output format."
	  with
	  | Not_found ->
	      begin
		if (c != stdout) then close_out c;
		raise (GenericError("A Satallax bug caused a problem creating the Coq file."))
	      end
	end
    | [] -> ()
  in
    if (not (!coqlocalfile)) then
      begin
        begin
          match (!mkproofterm) with
            |	Some CoqSPfTerm ->
	              begin
	                Printf.fprintf c "Require Export stt3.\n";
	              end
            |	Some CoqScript ->
	              begin
	                Printf.fprintf c "Add LoadPath \"%s/itp/coq\".\n" Config.satallaxdir;
	                Printf.fprintf c "Require Import stttab.\n";
	                Printf.fprintf c "Section SatallaxProblem.\n"
	              end
            |	Some IsarScript ->
	              begin
	                Printf.fprintf c "theory SatallaxProblem\n";
	                Printf.fprintf c "imports Satallax\n";
	                Printf.fprintf c "begin\n"
	              end
            |	_ -> ()
        end;
        print_coqsig_base !coqsig_base;
        print_coqsig_const !coqsig_const;
        print_coqsig_def !coqsig_const;
        if !mkproofterm = Some IsarScript then
	  Printf.fprintf c "\nlemma\n";
        print_coqsig_hyp !coqsig_hyp_trm;
        match (!conjecture) with
          | Some (t,_) ->
              if !mkproofterm = Some IsarScript then
	        begin
	          Printf.fprintf c "shows %s : \"" (Hashtbl.find coq_hyp_names (!conjecturename));
	                (* print_pretrm_isar c m coq_names coq_used_names (-1) (-1); *)
	          trm_to_isar c (coqnorm t) (TermP.Variables.make ());
	          Printf.fprintf c "\"\n";
                  (*FIXME currently all definitions are unfolded, irrespective of whether when they're used. This seems to reflect Satallax's usage anyway.*)
                  if List.length !coqsig_def > 0 then
	            Printf.fprintf c "unfolding %s\n" (String.concat " " (List.map (fun (s, _) -> s ^ "_def") !coqsig_def))
	        end
              else if !mkproofterm = Some TSTP then (* Don't print Coq declarations when tstp was requested. Chad, May 3 2016 *)
		()
		  
              else
	        begin
	          Printf.fprintf c "Theorem %s : " (Hashtbl.find coq_hyp_names (!conjecturename));
	          (* FIXME: account for !coq2? *)
	          trm_to_coq c (coqnorm t) (TermP.Variables.make ()) (-1) (-1);
(*	          if (!coq2) then print_pretrm_coq2 c m (-1) (-1) else print_pretrm_coq c m coq_names coq_used_names (-1) (-1); *) (*** No longer supported to get rid of dependence on pretrm ***)
	          Printf.fprintf c ".\n"
	        end
          | None ->
              if !mkproofterm = Some IsarScript then
                Printf.fprintf c "shows claim : \"False\"\n"
              else if !mkproofterm = Some TSTP then (* Don't print Coq declarations when tstp was requested. Michael Faerber, 25 Jun 2018 *)
		()
              else
                Printf.fprintf c "Theorem claim : False.\n"
      end
	
let declare_base_type a =
  if (!coq) then
    begin 
      let y = coqify_name a coq_names coq_used_names in
      coqsig_base := (y::!coqsig_base)
    end;
  Hashtbl.add name_base a ();
  name_base_list := (a::!name_base_list);
  if (get_bool_flag "CHOICE_AS_DEFAULT") then
    set_default_elt a (norm name_def (ap(Choice (Base a),Lam(Base a,False))))

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
	begin
	  match m with
	    PType -> (*** Actually unused. - April 20 2012 ***)
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Hashtbl.mem name_tp x) then raise (Redeclaration x);
	      declare_base_type x
	  | PName "$type" -> (*** The case that's used. Added April 20 2012 ***)
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Hashtbl.mem name_tp x) then raise (Redeclaration x);
	      declare_base_type x
	  | _ ->
	      let tp = st_to_stp m in
	      add_ontology_type x tp al;
	      if (Hashtbl.mem name_base x) then raise (Redeclaration x);
	      if (Hashtbl.mem name_tp x) then raise (Redeclaration x);
	      if (!coq) then
		begin
		  let y = coqify_name x coq_names coq_used_names in
		  coqsig_const := (y,tp)::!coqsig_const
		end;
	      declare_name_type x tp
	end
    | _ -> raise (GenericError ("Incorrect format for type declaration " ^ name))
  end

let rec init_probitem m =
  match m with
  | ProbDef(x,a,m,al,w) ->
      begin
	try
	  if (get_bool_flag "ALL_DEFS_AS_EQNS") then
	    raise TreatAsAssumption
	  else
	  begin
	    Hashtbl.add name_def_prenorm x m;
	    let m0 = logicnorm m in
	    let m2 = norm name_def m0 in
	    if (!verbosity > 20) then Printf.printf "name_def %s %s\n" x (trm_str m2);
	    Hashtbl.add name_def_all x (norm name_def_all m2);
	    if not (translucent_defn_p m) then
	      begin
		(* TODO: really set translucent definitions to true? *)
		translucent_defns := true;
		Hashtbl.add name_def x m2
	      end
	  end
	with TreatAsAssumption ->
	  init_probitem (ProbAx(x,"hypothesis",Ap(Ap(Eq(a),Name(x,a)),m),al,w))
      end
  | ProbAx(name,role,tm,al,w) ->
      begin
	let m0 = logicnorm tm in
	let tmn = norm name_def m0 in
	Hashtbl.add name_hyp name tmn;
	Hashtbl.add name_hyp_inv tmn (name,tm);
	if (!verbosity > 20) then Printf.printf "name_hyp %s %s\n" name (trm_str tmn);
	initial_branch_prenorm := tm::(!initial_branch_prenorm);
	initial_branch := tmn::(!initial_branch)
      end
  | ProbConj(name,tm,al,w) ->
      begin
	conjecturename := name;
	if (name != "claim") then
	  ignore (coqify_name name coq_hyp_names coq_used_names);
	let ntm = Ap(Neg,tm) in
	let ntmn = norm name_def (logicnorm ntm) in
	initial_branch_prenorm := (ntm::(!initial_branch_prenorm));
	if (!verbosity > 20) then Printf.printf "name_conj negated %s %s\n" name (trm_str ntmn);
	initial_branch := (ntmn::(!initial_branch));
	conjecture := Some (tm,ntmn);
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
let declare_definition_real x m al =
  if (Hashtbl.mem name_base x) then raise (Redeclaration x);
  if (Hashtbl.mem name_def x) then raise TreatAsAssumption; (*** treat it as an assumption per THF policy. - Mar 31, 2011 - Chad ***)
(*** raise (Redeclaration x); ***)
  try
    let tp = Hashtbl.find name_tp x in
    let tm = belnorm (st_to_trm_given_stp m tp) in
    try 
      let (_,r) = Hashtbl.find name_trm x in
      if (!r) then
	raise TreatAsAssumption (*** It's already been used, treat 'definition' as an assumption. ***)
      else
	raise Not_found
    with
    | Not_found ->
	begin
	  if (!coq) then (*** Coq proofs now only work for non-slaves ***)
	    begin (*** The name was coqified when the type was declared. ***)
	      try
		let y = Hashtbl.find coq_names x in
		coqsig_def := (y,m)::!coqsig_def;
		coqsig_def_trm := (y,tm)::!coqsig_def_trm
	      with
	      | Not_found -> raise (GenericError("Could not find Coq version of name " ^ x))
	    end;
	  add_ontology_term x tm;
	  let w = defpreweight tm al in
	  probsig := ProbDef(x,tp,tm,al,w)::!probsig
	end
  with
  | Not_found ->
      begin (*** Giving a definition without giving it's type isn't allowed in THF anymore.  I'm still allowing it.  ***)
	if ((!verbosity > 0) && (not (!coqglobalfile)) && (not (!coqlocalfile))) then Printf.printf "WARNING: %s defined without giving type first.\n" x;
	let (tm,tp) = st_to_trm m in
	let tm = belnorm tm in
	if (!coq) then
	  begin
	    let y = coqify_name x coq_names coq_used_names in
	    coqsig_const := (y,tp)::!coqsig_const;
	    coqsig_def := (y,m)::!coqsig_def;
	    coqsig_def_trm := (y,tm)::!coqsig_def_trm
	  end;
	declare_name_type x tp;
	let w = defpreweight tm al in
	probsig := ProbDef(x,tp,tm,al,w)::!probsig
      end

let rec declare_thf_logic_formula (name:string) (role:string) (m:pretrm) (al:(string * string) list) =
  begin
    if !verbosity > 4 then (Printf.printf "declare_thf_logic_formula %s %s\n" name role; flush stdout);
    if (!verbosity > 20) then (Printf.printf "annotations:\n"; List.iter (fun (a,b) -> Printf.printf "%s: %s\n" a b) al; flush stdout);
    if ((role = "axiom") || (role = "hypothesis") || (role = "assumption") || (role = "lemma") || (role = "theorem") || (role = "corollary")) then
      begin
	if (Hashtbl.mem name_hyp name) then raise (Redeclaration name);
	let tm = st_to_trm_given_stp m Prop in
	let tm = belnorm tm in
	if (!coq) then (** Giving Coq proofs will now only work for non-slaves since the pretrm is used **)
	  begin
	    let y = coqify_name name coq_hyp_names coq_used_names in
	    coqsig_hyp := ((y,m)::!coqsig_hyp);
	    coqsig_hyp_trm := ((y,tm)::!coqsig_hyp_trm)
	  end;
	let w = axpreweight tm al in
	probsig := ProbAx(name,role,tm,al,w)::!probsig
      end
    else if (role = "conjecture") then
      begin
	match (!conjecture) with
	| Some _ -> raise (GenericError "Problem file has more than one conjecture.")
	| None ->
	    let tm = st_to_trm_given_stp m Prop in
	    let tm = belnorm tm in
	    let w = conjpreweight tm al in
	    probsig := ProbConj(name,tm,al,w)::!probsig
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
let enum_started = ref false
let enum_of_started_ : (stp,unit) Hashtbl.t = Hashtbl.create 5
let enum_of_started a =
  Hashtbl.mem enum_of_started_ a
let enum_of_start a =
  Hashtbl.add enum_of_started_ a ()
let type_continuations_rtp : (stp option,(stp -> int -> unit)) Hashtbl.t = Hashtbl.create 5
let term_continuations_rtp : (stp,(stp list * trm * int -> unit)) Hashtbl.t = Hashtbl.create 5
let usableTypes_rtp : (stp,(stp * int)) Hashtbl.t = Hashtbl.create 5
let usableTypes : (stp * stp * int) list ref = ref []
let usableHeads_rtp : (stp,(stp list * trm * int)) Hashtbl.t = Hashtbl.create 5

let new_type_continuation_rtp ar f =
  Hashtbl.add type_continuations_rtp (Some ar) f

let new_type_continuation f =
  Hashtbl.add type_continuations_rtp None f

let iter_type_continuations_rtp ar a d =
  List.iter (fun f -> f a d) (Hashtbl.find_all type_continuations_rtp (Some ar))

let iter_type_continuations a d =
  List.iter (fun f -> f a d) (Hashtbl.find_all type_continuations_rtp None)

let new_term_continuation_rtp ar f =
  Hashtbl.add term_continuations_rtp ar f

let iter_term_continuations_rtp ar sigmal m p =
  List.iter (fun f -> f (sigmal,m,p)) (Hashtbl.find_all term_continuations_rtp ar)

let new_usable_type_rtp ar a d =
  Hashtbl.add usableTypes_rtp ar (a,d);
  usableTypes := ((ar,a,d)::(!usableTypes))

let usable_types_rtp ar = Hashtbl.find_all usableTypes_rtp ar

let usable_types () = !usableTypes

let new_usable_head_rtp ar sigmal m n = Hashtbl.add usableHeads_rtp ar (sigmal,m,n)

let usable_heads_rtp ar = Hashtbl.find_all usableHeads_rtp ar

(*** search init ***)
let search_init () =
  (*** Add initial instantiations: true and false for o ***)
  add_instantiation Prop False;
  add_instantiation Prop (neg False)
  
(*** reset search ***)
let reset_search () =
  begin
    Hashtbl.clear clausesTable;
    clauses := [];
    clause_ruleinfo := Hashtbl.create 100;
    Searchoption.reset_pqueues ();
    Hashtbl.clear patoms;
    Hashtbl.clear natoms;
    Hashtbl.clear pchoiceatoms;
    Hashtbl.clear nchoiceatoms;
    Hashtbl.clear peqns;
    Hashtbl.clear neqns;
    Hashtbl.clear univpreds;
    Hashtbl.clear instantiations;
    Hashtbl.clear processed;
    enum_started := false;
    Hashtbl.clear enum_of_started_;
    Hashtbl.clear type_continuations_rtp;
    Hashtbl.clear term_continuations_rtp;
    Hashtbl.clear usableTypes_rtp;
    usableTypes := [];
    Hashtbl.clear usableHeads_rtp;
    Hashtbl.clear choiceopnames;
    Hashtbl.clear filtered;
    Eproverstate.reset_eprover_state ();
    search_init()
  end

let print_branch =
  List.iteri (fun i m -> Printf.printf "%d %s\n" (i+1) (trm_str m))

(* select_list l [i1; ...; in] = [nth l in; ...; nth l i1] *)
let select_list l = List.rev_map (List.nth l)

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
