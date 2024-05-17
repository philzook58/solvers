(* Lash *)
(* ported from Satallax file: pfterm/proofterm.ml *)

open Flags
open State
open Log
open Atom
open String
open Syntax
open Search
open Refutation
open Flag
open Suche
open Translation
open Latex
open Coq
open Branch
open Norm
open Refut
open Error

let loc_literal_to_trm l = ftm_trm name_tp [] (literal_to_trm l)
let loc_get_literal m = get_literal (trm_ftm name_def_f m)
let preprocess m = ftm_trm name_tp [] m

(** to String functions for debugging**)

(** Debug function: Alternative way to print terms **)
 let rec trm_struct m =
  match m with
    Name(x,_) -> x
  | False -> "False"
  | Imp -> "Imp"
  | Forall(_) -> "Forall"
  | Eq(_) -> "Eq"
  | Choice(_) -> "Sepsilon"
  | True -> "True"
  | And -> "And"
  | Or -> "Or"
  | Iff -> "Iff"
  | Neg -> "Neg"
  | Exists(_) -> "Exists" 
  | DB(i,a) -> "DB(" ^ (string_of_int i) ^","^ (stp_str a)  ^")"
  | Lam(a,m) -> "Lam(" ^ (stp_str a) ^ "," ^ (trm_struct m)^")"
  | Ap(m1,m2) -> "Ap("^ (trm_struct m1) ^ "," ^ (trm_struct m2) ^")"                   
       
(** Statistic **)

(* statcount is an attempt to guess the size of the final refutation after timeout stopped the search *)
let statcount = ref (Hashtbl.create 100) 
let update_statcount h s w b =
if b then 
let (zs,zw,n) = try Hashtbl.find !statcount h with Not_found -> (0,0,0) in
Hashtbl.replace !statcount h (zs+s,zw+w,n+1)

(* statistic extract simple information from a refutation: size, depth, width, No. cuts, No. rewrites, No. NYIs, No. timeouts *)
let statistic r  =
let _ = Hashtbl.clear !statcount in
let rec statistic1 r h b =
 match r with
 | Conflict(s,ns) -> (1,1,1,0,0,0,0)
 | Fal(_) -> (1,1,1,0,0,0,0)
 | NegRefl(s) -> (1,1,1,0,0,0,0)
 | Implication(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
        let _ = update_statcount h (s1+s2+1) (w1+w2) b in 
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Disjunction(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegConjunction(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegImplication(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | Conjunction(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | NegDisjunction(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1) 
 | All(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | NegAll(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | Exist(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1) 
 | NegExist(_,_,r1,_,_,_) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | Mating(_,_,_, rs) -> begin ( try ignore (List.hd rs) with Failure(_) -> failwith "Mating refutation list is empty" );
	let (s1,d1,w1,c1,re1,nyi1,t1) = List.fold_left (fun (s,d,w,c,re,nyi,t) r -> let (s',d',w',c',re',nyi',t') = statistic1 r (h+1) b in (s+s',max d' (d-1) +1,w+w',c+c',re+re',nyi+nyi',t+t')) (1,1,0,0,0,0,0) rs in
	let _ = update_statcount h s1 w1 b in	
	(s1,d1,w1,c1,re1,nyi1,t1)
	end
 | Decomposition(_,_,rs)-> begin ( try ignore (List.hd rs) with Failure(_) -> failwith"Decomposition refutation list is empty"  );
	let (s1,d1,w1,c1,re1,nyi1,t1) = List.fold_left (fun (s,d,w,c,re,nyi,t) r -> let (s',d',w',c',re',nyi',t') = statistic1 r (h+1) b in (s+s',max d' (d-1) +1,w+w',c+c',re+re',nyi+nyi',t+t')) (1,1,0,0,0,0,0) rs in
	let _ = update_statcount h s1 w1 b in	
	(s1,d1,w1,c1,re1,nyi1,t1)
	end
 | Confront(_,_,_,_,_,_,r1,r2) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Trans(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) (w1) b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)
 | NegEqualProp(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | EqualProp(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2) 
 | NegAequivalenz(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Aequivalenz(_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | NegEqualFunc(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in	
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | EqualFunc(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | ChoiceR(_,_,_,_,r1,r2) -> 
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2,re1+re2,nyi1+nyi2,t1+t2)
 | Cut(l,r1,r2) -> if debug_litcount then Printf.printf "cut on %d\n" (loc_get_literal l);
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let (s2,d2,w2,c2,re2,nyi2,t2) = statistic1 r2 (h+1) b in
	let _ = update_statcount h (s1+s2+1) (w1+w2) b in
	(1+s1+s2,max d1 d2 +1,w1+w2,c1+c2+1,re1+re2,nyi1+nyi2,t1+t2)
 | DoubleNegation(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1,nyi1,t1)   
 | Rewrite(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1+1,nyi1,t1)    
 | Delta(_,_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1+1,nyi1,t1)
 | KnownResult(_,name,al,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1+1,nyi1,t1)
 | NYI(_,_,r1) ->
	let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r1 (h+1) b in
	let _ = update_statcount h (s1+1) w1 b in
	(1+s1,d1 +1,w1,c1,re1,nyi1+1,t1) 
 | Timeout -> 
	let (zs,zw,n) =if b then (1,1,1) else try Hashtbl.find !statcount h with Not_found -> (1,1,1) in
	(zs/n,1,zw/n,0,0,0,1)   
(* | _ -> failwith "unknown refutation case in statistic" *)
in 
let (s1,d1,w1,c1,re1,nyi1,t1) = statistic1 r 0 true in
let (s2,_,w2,_,_,_,_) = statistic1 r 0 false in
(s1,s2,d1,w1,w2,c1,re1,nyi1,t1)

(** MAIN **)
let tstp : bool ref = ref false;;


let print_latex_search (size,_,depth,width,_,cut,rewrite,notyetImpl,_) lat c =
  if (result_latex && width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n ***)\n" 
  size depth width lat
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d \n \n  %%endLatex \n ***)\n" size depth width


let print_latex_translation (size,_,depth,width,_,cut,rewrite,notyetImpl,_) lat c =
  if (result_latex &&  width < 50 && depth < 30) then
  Printf.fprintf c "(*** \n %%beginLatex \n size %d depth %d width %d cuts %d rewrite  %d NYI %d \n \n \\begin{tabular}{c} \n %s \\end{tabular} \n\n %%endLatex \n***)" 
  size depth width cut rewrite notyetImpl lat
  else if (result_latex) then Printf.fprintf c "(*** \n %%beginLatex \n \n \n Translation successful, probably \n \n size %d depth %d width %d cuts %d rewrite %d  NYI %d \n %%endLatex \n***)" size depth width cut rewrite notyetImpl 
  ; flush stdout


let print_refutation_result (refutation,_,searchTime,isTimeout) =
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,timeouts) = statistic refutation in
  let hasTimedout = isTimeout || timeouts > 0 in
  if hasTimedout then (if !verbosity > 0 then Printf.printf  "Timeout!  time %d ms size %d depth %d width %d cuts %d rewrite %d NYI %d timeouts %d \n" searchTime size depth width cut rewrite notyetImpl timeouts)
  else
  begin
    if result_print_search then Printf.printf  "%s\n" (ref_str refutation);
    if (!verbosity > 3) then Printf.printf "Search time %d ms size %d depth %d width %d \n" searchTime size depth width;
  end;
  (refutation, hasTimedout)
  
let get_initbranch () =
  let initbranch1 = (List.rev !initial_branch) in
  List.map preprocess initbranch1 (*** Chad, Aug 2011: Preprocess to handle LEIBEQ_TO_PRIMEQ here as well as in suche.ml. Example: SYO348^5.p ***)

let get_initbranch_prenorm () =
  let go pn =
    let p = onlynegnorm pn in
    if debug_translation then Printf.printf "%s = %s \n" (trm_str pn) (trm_str p); p in
  List.map go (List.rev !initial_branch_prenorm)
  

let get_refutation initbranch r =
  (* get assumptions *)
  let b = List.map loc_get_literal initbranch in
  (* call search *)
  let (_,con,_,_) as sr = search_refutation b r in
  if assert_condition && not (Dependency.is_empty (Dependency.diffunion [] [con] [b])) && !verbosity > 0 then
    Printf.printf "Error with refutation: Still open conditions\n";
  sr

let do_translate branch refutation =
      try
	if pftrm_eager_rewrite then
	  eager_translate branch refutation
	else
	  lazy_translate branch refutation
      with TranslateFailure -> safe_translate branch refutation (*** Chad Aug 2011 : Fall back on safe_translate ***)

let get_translation branch refutation =
  if debug_translation then (Printf.printf "About to translate. Branch assoc with prenorm:\n"; List.iter (fun (m,p) -> Printf.printf "trm: %s\npre: %s\n" (trm_str m) (trm_str p)) branch);
(* The flag pftrm_eager_rewrite decides wether rewrites are eagerly or lazily handled *) 
  let prenorm_refutation = do_translate branch refutation in

  if debug_translation then (Printf.printf "Translated prenorm_refutation\n%s\n" (ref_str prenorm_refutation));
  prenorm_refutation

let print_prenorm_ref_result transTime stats prenorm_refutation =
  let (size,_,depth,width,_,cut,rewrite,notyetImpl,_) as stats = statistic prenorm_refutation  in
  if result_print_translation then Printf.printf  "%s\n" (ref_str prenorm_refutation);
  if (!verbosity > 3) then Printf.printf  "Translation NYI %d time %d ms size %d depth %d width %d cuts %d rewrite %d  \n" notyetImpl transTime size depth width cut rewrite
  
  

let print_coq_proof printer c r =
  if (!verbosity > vold) then print_refut r;

	(*** Search ***)

  let initbranch = get_initbranch () in
  let (refutation, hasTimedout) = print_refutation_result (get_refutation initbranch r) in

  if hasTimedout then raise Timeout;
	(*** Translation  ***)

(* get prenormalized assumptions *)
  let initbranch_prenorm = get_initbranch_prenorm () in

  let beforeTrans= Sys.time() in
(* Branch is an association list from normalized terms to their prenormalized counterparts *)
  let branch = (List.combine initbranch initbranch_prenorm) in
  let prenorm_refutation = get_translation branch refutation in
  let transTime= int_of_float ((Sys.time() -. beforeTrans) *. 1000.0) in

  let (size, _,_,_,_,_,_,_,_) as stats = statistic prenorm_refutation in
  print_prenorm_ref_result transTime stats prenorm_refutation;

	(*** Output Coq ***)

  let beforeCoq= Sys.time() in
  printer size prenorm_refutation;
  let coqTime= int_of_float ((Sys.time() -. beforeCoq) *. 1000.0) in
  if !result_coq then if (!verbosity > 3) then Printf.printf  "Coq output done: time %d  \n" coqTime ;

  print_latex_search stats (ref_to_lat initbranch refutation) c;
  print_latex_translation stats (ref_to_lat initbranch_prenorm prenorm_refutation) c

let coq_proofscript_printer c size prenorm_refutation = 
  if (!tstp) then ref_tstp c prenorm_refutation
  else
    begin
      if !result_coq then
        if size < maxcoqproofsize then
          ref_coq c prenorm_refutation
        else raise (CoqProofTooBig size)
      else if !result_isabellehol then
        if size < max_isabellehol_proofsize then
          ref_isabellehol c prenorm_refutation
        else raise (CoqProofTooBig size) (*FIXME replace with IsabelleHOLProofTooBig*)
    end

let print_coq_proofscript c r =
  if (!verbosity > vold) then Printf.printf  "starting print_coq_proofscript.\n";
  print_coq_proof (coq_proofscript_printer c) c r

let print_coq_sproofterm c r =
  if (!verbosity > vold) then Printf.printf "starting print_coq_proofspfterm.\n";
  let printer size prenorm_refutation =
    if (!result_coq && size < maxcoqproofsize)
    then ref_coq_spfterm c prenorm_refutation
    else raise (CoqProofTooBig size) in
  print_coq_proof printer c r

(*** Chad, August 2011: Added this way of printing proof information at the request of Jasmin Blanchette. ***)
let print_hocore c r =
  let don : (string,unit) Hashtbl.t = Hashtbl.create 1000 in
  let report_name name =
    if (not (Hashtbl.mem don name)) then
      begin
	Printf.fprintf c "%s\n" name;
	Hashtbl.add don name ()
      end
  in
  let rec hocore_1 c r a =
    if (!verbosity > 50) then
      begin
	Printf.printf "hocore_1 r\n";
	print_refut r;
	Printf.printf "hocore_1 a BEGIN\n";
	List.iter (fun (m,n) -> Printf.printf "%s : %s\n" n (trm_str m)) a;
	Printf.printf "hocore_1 a END\n";
      end;
    match r with
    | SearchR(cl,cr) ->
	List.iter
	  (fun c0 ->
	    try
	      if (!verbosity > 50) then
		begin
		  Printf.printf "Calling cr on clause ";
		  List.iter (fun i -> Printf.printf "%d\n" i) c0;
		  Printf.printf "\n";
		end;
	      match (cr c0) with
	      |	ChoiceRule(m,p) when get_tag m = FT_Name ->
		 begin
                   let eps = get_no m in
		   if (!verbosity > 50) then Printf.printf "cr found it's a choice rule\n";
		   try
		     let (_,choiceax,_) = Hashtbl.find choiceopnames eps in
		     let name = List.assoc choiceax a in
		     report_name name
		   with
		     Not_found -> ()
		 end
	      |	ri ->
		  begin
		    if (!verbosity > 50) then Printf.printf "cr found it has rule info %s\n" (ruleinfo_str ri);
		  end
	    with (** Assumptions have no associated rule info **)
	      Not_found ->
		begin
		  if (!verbosity > 50) then Printf.printf "cr found no rule info\n";
		  match c0 with
		  | [l] ->
		      begin
			let tm = loc_literal_to_trm l in
			try
			  report_name (List.assoc tm a)
			with Not_found -> ()
		      end
		  | _ -> raise (GenericError "Non-Unit Assumption") (*** Unexpected case: Non-unit Assumption ***)
		end)
	  cl
    | AssumptionConflictR(_) -> (*** There must be a formula (m,name) on a such that (~m,name2) is on a. Otherwise, there's a bug. ***)
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,m),False)),name)::ar) ->
	      begin
		try
		  report_name (List.assoc m ar);
		  report_name name
		with
		| Not_found -> find_conflict ar
	      end
	  | ((m,name)::ar) ->
	      let nm = Ap(Ap(Imp,m),False) in
	      begin
		try
		  report_name (List.assoc nm ar);
		  report_name name
		with
		| Not_found -> find_conflict ar
	      end
	  | [] -> raise (GenericError "Assumption Conflict Not Found")
	in
	find_conflict a
    | FalseR ->
	begin
	  try
	    report_name (List.assoc False a)
	  with Not_found -> raise (GenericError "Assumption 'False' Not Found")
	end
    | NegReflR(_) ->
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,Ap(Ap(Eq(_),m),n)),False)),name)::_) when (m = n) -> report_name name
	  | (_::ar) -> find_conflict ar
	  | [] -> raise (GenericError "Assumption of Negated Reflexive Equation Not Found")
	in
	find_conflict a
	  (*** Otherwise, follow the refutation, adding things to the assoc list a as we break down the formulas. ***)
    | NegImpR(_,_,_,m,n,r) ->
	begin
	  try
	    let name = List.assoc (neg (imp m n)) a in
	    hocore_1 c r ((m,name)::(normneg n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (imp m n)))))
	end
    | ImpR(_,_,_,m,n,r1,r2) ->
	begin
	  try
	    let name = List.assoc (imp m n) a in
	    hocore_1 c r1 ((normneg m,name)::a);
	    hocore_1 c r2 ((n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (imp m n))))
	end
    | NegAllR(b,_,_,m,x,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Forall(b),m))) a in
	    hocore_1 c r (((norm name_def (neg (Ap(m,Name(x,b))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (Ap(Forall(b),m))))))
	end
    | NegEqFR(a1,a2,_,_,m,n,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))) a in
	    hocore_1 c r (((norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))))))
	end
    | EqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (eq mk_prop m n) a in
	    hocore_1 c r1 ((m,name)::(normneg n,name)::a);
	    hocore_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (eq mk_prop m n))))
	end
    | NegEqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (neg (eq mk_prop m n)) a in
	    hocore_1 c r1 ((m,name)::(normneg n,name)::a);
	    hocore_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str (neg (eq mk_prop m n)))))
	end
  in
  let rec add_conjs cnl cl a =
    match (cnl,cl) with
    | (cn::cnr,(_,ntmn)::cr) -> add_conjs cnr cr ((ftm_trm name_tp [] ntmn,cn)::a)
    | _ -> a
  in
  let a = add_conjs !conjecturenames !conjecture (Hashtbl.fold (fun k v l -> (v,k)::l) name_hyp []) in
  hocore_1 c r a

(*** Chad, August 2016 *)
let print_pfinfo c r =
  let don : (string,unit) Hashtbl.t = Hashtbl.create 1000 in
  let report_name name =
    if (not (Hashtbl.mem don name)) then
      begin
	Printf.fprintf c "%s\n" name;
	Hashtbl.add don name ()
      end
  in
  let rec pfinfo_1 c r a =
    if (!verbosity > 50) then
      begin
	Printf.printf "pfinfo_1 r\n";
	print_refut r;
	Printf.printf "pfinfo_1 a BEGIN\n";
	List.iter (fun (m,n) -> Printf.printf "%s : %s\n" n (trm_str_nice m)) a;
	Printf.printf "pfinfo_1 a END\n";
      end;
    match r with
    | SearchR(cl,cr) ->
	Printf.printf "%% Subproof BEGIN\n";
	let decused = ref false in
	let matused = ref false in
	let chused = ref false in
	List.iter
	  (fun c0 ->
	    Printf.printf "Clause:";
	    List.iter (fun i -> Printf.printf " %d" i) c0;
	    Printf.printf "\n";
	    try
	      match (cr c0) with
	      |	ChoiceRule(m,p) when get_tag m = FT_Name ->
		 begin
                   let eps = get_no m in
		   if (!verbosity > 50) then Printf.printf "cr found it's a choice rule\n";
		   try
		     let (_,choiceax,_) = Hashtbl.find choiceopnames eps in
		     let name = List.assoc choiceax a in
		     report_name name
		   with
		     Not_found -> ()
		 end
	      |	ri ->
		  begin
		    Printf.printf "Rule: %s\n" (ruleinfo_str ri);
		    match ri with
		    | MatingRule(_,_) -> matused := true
		    | NegPropRule(m) when get_tag m = FT_Eq && not (get_l m == get_r m) && is_base (ty_f_rev (get_no m)) -> decused := true
		    | ChoiceRule(_,_) -> chused := true
		    | _ -> ()
		  end
	    with (** Assumptions have no associated rule info **)
	      Not_found ->
		begin
		  match c0 with
		  | [l] ->
		      let tm = loc_literal_to_trm l in
		      Printf.printf "Assumption: %s\n" (trm_str_nice tm)
		  | _ -> raise (GenericError "Non-Unit Assumption") (*** Unexpected case: Non-unit Assumption ***)
		end)
	  cl;
	if !decused then Printf.printf "%% Decomposition Rule used in subproof.\n";
	if !matused then Printf.printf "%% Mating Rule used in subproof.\n";
	if !chused then Printf.printf "%% Choice Rule used in subproof.\n";
	if !decused || !matused || !chused then Printf.printf "%% A non-EBG Rule used in subproof.\n";
	Printf.printf "%% Subproof END\n"
    | AssumptionConflictR(_) -> (*** There must be a formula (m,name) on a such that (~m,name2) is on a. Otherwise, there's a bug. [2016: Or it conflicts with a 'known'] ***)
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,m),False)),name)::ar) ->
	      begin
		try
		  report_name (List.assoc m ar);
		  report_name name
		with
		| Not_found -> find_conflict ar
	      end
	  | ((m,name)::ar) ->
	      let nm = Ap(Ap(Imp,m),False) in
	      begin
		try
		  report_name (List.assoc nm ar);
		  report_name name
		with
		| Not_found -> find_conflict ar
	      end
	  | [] -> raise (GenericError "Assumption Conflict Not Found")
	in
	find_conflict a
    | FalseR ->
	begin
	  try
	    report_name (List.assoc False a)
	  with Not_found -> raise (GenericError "Assumption 'False' Not Found")
	end
    | NegReflR(_) ->
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,Ap(Ap(Eq(_),m),n)),False)),name)::_) when (m = n) -> report_name name
	  | (_::ar) -> find_conflict ar
	  | [] -> raise (GenericError "Assumption of Negated Reflexive Equation Not Found")
	in
	find_conflict a
	  (*** Otherwise, follow the refutation, adding things to the assoc list a as we break down the formulas. ***)
    | NegImpR(_,_,_,m,n,r) ->
	begin
	  try
	    let name = List.assoc (neg (imp m n)) a in
	    pfinfo_1 c r ((m,name)::(normneg n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (imp m n)))))
	end
    | ImpR(_,_,_,m,n,r1,r2) ->
	begin
	  try
	    let name = List.assoc (imp m n) a in
	    pfinfo_1 c r1 ((normneg m,name)::a);
	    pfinfo_1 c r2 ((n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (imp m n))))
	end
    | NegAllR(b,_,_,m,x,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Forall(b),m))) a in
	    pfinfo_1 c r (((norm name_def (neg (Ap(m,Name(x,b))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (Ap(Forall(b),m))))))
	end
    | NegEqFR(a1,a2,_,_,m,n,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))) a in
	    pfinfo_1 c r (((norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))))))
	end
    | EqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (eq mk_prop m n) a in
	    pfinfo_1 c r1 ((m,name)::(normneg n,name)::a);
	    pfinfo_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (eq mk_prop m n))))
	end
    | NegEqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (neg (eq mk_prop m n)) a in
	    pfinfo_1 c r1 ((m,name)::(normneg n,name)::a);
	    pfinfo_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (eq mk_prop m n)))))
	end
  in
  let rec add_conjs cnl cl a =
    match (cnl,cl) with
    | (cn::cnr,(_,ntmn)::cr) -> add_conjs cnr cr ((ftm_trm name_tp [] ntmn,cn)::a)
    | _ -> a
  in
  let a = add_conjs !conjecturenames !conjecture (Hashtbl.fold (fun k v l -> (v,k)::l) name_hyp []) in
  pfinfo_1 c r a

(*** Chad, August 2016 *)
let print_pfuseful c r o =
  let usefulform : (int,string) Hashtbl.t = Hashtbl.create 1000 in
  let usefulfrom : (int,int) Hashtbl.t = Hashtbl.create 1000 in
  let usefulinsts : (int,stp * trm) Hashtbl.t = Hashtbl.create 1000 in
  let record_useful_common c0 =
    match c0 with
    | (h::r) ->
	if not (Hashtbl.mem usefulform (-h)) then Hashtbl.add usefulform (-h) "";
	List.iter
	  (fun l ->
	    if not (Hashtbl.mem usefulform l) then Hashtbl.add usefulform l "";
	    Hashtbl.add usefulfrom (-h) l)
	  r
    | [] -> raise (Failure "Clause for common rule with no head?")
  in
  let record_useful_conn c0 =
    match c0 with
    | (h1::h2::r) ->
	if not (Hashtbl.mem usefulform (-h1)) then Hashtbl.add usefulform (-h1) "";
	if not (Hashtbl.mem usefulform (-h2)) then Hashtbl.add usefulform (-h2) "";
	List.iter
	  (fun l ->
	    if not (Hashtbl.mem usefulform l) then Hashtbl.add usefulform l "";
	    Hashtbl.add usefulfrom (-h1) l;
	    Hashtbl.add usefulfrom (-h2) l)
	  r
    | [h1] -> raise (Failure "Clause for conn rule with only one head?")
    | [] -> raise (Failure "Clause for conn rule with no head?")
  in
  let rectopfrom l z =
    Hashtbl.add usefulfrom l z
  in
  let rec pfuseful_1 c r a =
    match r with
    | SearchR(cl,cr) ->
	List.iter
	  (fun c0 ->
	    try
	      match (cr c0) with
	      | DeltaRule -> record_useful_common c0
	      | NegPropRule(_) -> record_useful_common c0
	      | PosPropRule(_) -> record_useful_common c0
	      | InstRule(a,m,n) ->
		  record_useful_common c0;
		  begin
		    match c0 with
		    | (h::_) -> Hashtbl.add usefulinsts (-h) (ty_f_rev a,ftm_trm name_tp [] n)
		    | [] -> raise (Failure "InstRule with no head?")
		  end
	      | FreshRule(_,_,_) -> record_useful_common c0
	      | MatingRule(_,_) -> record_useful_conn c0
	      | ConfrontationRule(_,_) -> record_useful_conn c0
	      |	ChoiceRule(m,p) when get_tag m = FT_Name ->
                 let eps = get_no m in
		 let choicename =
		   try
		     let (_,choiceax,_) = Hashtbl.find choiceopnames eps in
		     let name = List.assoc choiceax a in
		     ("choice:" ^ name)
		   with
		     Not_found -> "choice"
		 in
		 begin
		   List.iter
		     (fun l -> Hashtbl.add usefulform l choicename)
		     c0
		 end
	      |	ChoiceRule(_,p) ->
		  begin
		    List.iter
		      (fun l -> Hashtbl.add usefulform l "choice")
		      c0
		  end
	      | Known(l,x,_) ->
		  Hashtbl.add usefulform l ("known:" ^ x)
	    with (** Assumptions have no associated rule info **)
	      Not_found ->
		begin
		  match c0 with
		  | [l] ->
		      let name =
			try
			  "assumption:" ^ (List.assoc (loc_literal_to_trm l) a)
			with
			  Not_found -> "assumption"
		      in		  
		      Hashtbl.add usefulform l name
		  | _ -> raise (GenericError "Non-Unit Assumption") (*** Unexpected case: Non-unit Assumption ***)
		end)
	  cl;
    | AssumptionConflictR(_) -> (*** There must be a formula (m,name) on a such that (~m,name2) is on a. Otherwise, there's a bug. ***)
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,m),False)),name)::ar) ->
	      begin
		try
		  let name2 = List.assoc m ar in
		  let l = loc_get_literal m in
		  Hashtbl.add usefulform l ("top:" ^ name);
		  Hashtbl.add usefulform (-l) ("top:" ^ name2);
		with
		| Not_found -> find_conflict ar
	      end
	  | ((m,name)::ar) ->
	      let nm = Ap(Ap(Imp,m),False) in
	      begin
		try
		  let name2 = List.assoc nm ar in
		  let l = loc_get_literal nm in
		  Hashtbl.add usefulform l ("top:" ^ name);
		  Hashtbl.add usefulform (-l) ("top:" ^ name2)
		with
		| Not_found -> find_conflict ar
	      end
	  | [] -> raise (GenericError "Assumption Conflict Not Found")
	in
	find_conflict a
    | FalseR ->
	begin
	  try
	    let name = List.assoc False a in
	    Hashtbl.add usefulform (loc_get_literal False) ("top:" ^ name)
	  with Not_found -> raise (GenericError "Assumption 'False' Not Found")
	end
    | NegReflR(_) ->
	let rec find_conflict a =
	  match a with
	  | ((((Ap(Ap(Imp,Ap(Ap(Eq(_),m),n)),False)) as emm),name)::_) when (m = n) ->
	      let lemm = loc_get_literal emm in
	      Hashtbl.add usefulform lemm ("top:" ^ name)
	  | (_::ar) -> find_conflict ar
	  | [] -> raise (GenericError "Assumption of Negated Reflexive Equation Not Found")
	in
	find_conflict a
	  (*** Otherwise, follow the refutation, adding things to the assoc list a as we break down the formulas. ***)
    | NegImpR(_,_,_,m,n,r) ->
	begin
	  try
	    let mn = neg (imp m n) in
	    let name = List.assoc mn a in
	    let lmn = loc_get_literal mn in
	    Hashtbl.add usefulform lmn ("top:" ^ name);
	    rectopfrom lmn (loc_get_literal m);
	    rectopfrom lmn (-(loc_get_literal n));
	    pfuseful_1 c r ((m,name)::(normneg n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (imp m n)))))
	end
    | ImpR(_,_,_,m,n,r1,r2) ->
	begin
	  try
	    let mn = imp m n in
	    let name = List.assoc mn a in
	    let lmn = loc_get_literal mn in
	    Hashtbl.add usefulform lmn ("top:" ^ name);
	    rectopfrom lmn (-(loc_get_literal m));
	    rectopfrom lmn (loc_get_literal n);
	    pfuseful_1 c r1 ((normneg m,name)::a);
	    pfuseful_1 c r2 ((n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (imp m n))))
	end
    | NegAllR(b,_,_,m,x,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Forall(b),m))) a in
	    let l1 = loc_get_literal (neg (Ap(Forall(b),m))) in
	    let l2 = loc_get_literal (norm name_def (neg (Ap(m,Name(x,b))))) in
	    Hashtbl.add usefulform l1 ("top:" ^ name);
	    rectopfrom l1 l2;
	    pfuseful_1 c r (((norm name_def (neg (Ap(m,Name(x,b))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (Ap(Forall(b),m))))))
	end
    | NegEqFR(a1,a2,_,_,m,n,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))) a in
	    let l1 = loc_get_literal (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))) in
	    let l2 = loc_get_literal (norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))) in
	    Hashtbl.add usefulform l1 ("top:" ^ name);
	    rectopfrom l1 l2;
	    pfuseful_1 c r (((norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))))))
	end
    | EqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (eq mk_prop m n) a in
	    let l1 = loc_get_literal (eq mk_prop m n) in
	    let lm = loc_get_literal m in
	    let ln = loc_get_literal n in
	    Hashtbl.add usefulform l1 ("top:" ^ name);
	    rectopfrom l1 lm;
	    rectopfrom l1 ln;
	    rectopfrom l1 (-lm);
	    rectopfrom l1 (-ln);
	    pfuseful_1 c r1 ((m,name)::(normneg n,name)::a);
	    pfuseful_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (eq mk_prop m n))))
	end
    | NegEqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (neg (eq mk_prop m n)) a in
	    let l1 = -(loc_get_literal (eq mk_prop m n)) in
	    let lm = loc_get_literal m in
	    let ln = loc_get_literal n in
	    Hashtbl.add usefulform l1 ("top:" ^ name);
	    rectopfrom l1 lm;
	    rectopfrom l1 ln;
	    rectopfrom l1 (-lm);
	    rectopfrom l1 (-ln);
	    pfuseful_1 c r1 ((m,name)::(normneg n,name)::a);
	    pfuseful_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (eq mk_prop m n)))))
	end
  in
  let rec add_conjs cnl cl a =
    match (cnl,cl) with
    | (cn::cnr,(_,ntmn)::cr) -> add_conjs cnr cr ((ftm_trm name_tp [] ntmn,cn)::a)
    | _ -> a
  in
  let a = add_conjs !conjecturenames !conjecture (Hashtbl.fold (fun k v l -> (v,k)::l) name_hyp []) in
  pfuseful_1 c r a;
  Printf.printf "Useful formulas:\n";
  let don : (int,trm) Hashtbl.t = Hashtbl.create 1000 in
  let depslist : (int * int) list ref = ref [] in
  Hashtbl.iter
    (fun k _ ->
      if not (Hashtbl.mem don k) then
	begin
	  Printf.printf "%d %s\n" k (trm_str_nice (loc_literal_to_trm k));
	  List.iter (fun v -> if not (v = "") then Printf.printf "%s;" v) (Hashtbl.find_all usefulform k);
	  Printf.printf "\n";
	  Hashtbl.add don k (loc_literal_to_trm k)
	end)
    usefulform;
  Printf.printf "Dependencies:\n";
  Hashtbl.iter
    (fun k _ ->
      let ll = Hashtbl.find_all usefulfrom k in
      if not (ll = []) then
	begin
	  Printf.printf "%d:" k;
	  List.iter (fun v -> if Hashtbl.mem usefulform v then (Printf.printf " %d" v; depslist := (v,k)::!depslist)) ll;
	  Printf.printf "\n";
	end)
    don;
  Printf.printf "Instantiations:\n";
  Hashtbl.iter
    (fun k _ ->
      let ll = Hashtbl.find_all usefulinsts k in
      if not (ll = []) then
	begin
	  Printf.printf "%d: (%d)\n" k (List.length ll);
	  List.iter (fun (_,n) -> Printf.printf "%s\n" (trm_str_nice n)) ll
	end)
    don;
  match o with
  | Some(o) ->
      let f = open_out_bin o in
      output_value f don;
      output_value f !depslist;
      close_out f
  | None -> ()
    
(*** Chad - July 2012 - output proof script in tstp format. ***)
(*** Chad, Dec 2016: Newer tstp proof: print defns of propositions referenced, defns of eigenvars using choice, propositional clauses using symbols for propositions corresponding to assumptions and rules, and a final step of false by propositional unsatisfiability **)
let print_tstp c (r : Refut.refut) =
  refut_tstp c r

    (*** Chad, August 2016 *)
let print_pfformdeps c r o =
  let handledclause : (int list,unit) Hashtbl.t = Hashtbl.create 1000 in
  let formdepsform : (int,bool) Hashtbl.t = Hashtbl.create 1000 in
  let formdepsfrom : (int,int list) Hashtbl.t = Hashtbl.create 1000 in
  let formdepsinsts : (int,stp * trm) Hashtbl.t = Hashtbl.create 1000 in
  let record_formdeps_common c0 b =
    match c0 with
    | (h::r) ->
	if not (Hashtbl.mem formdepsform (-h)) then Hashtbl.add formdepsform (-h) b;
	List.iter
	  (fun l ->
	    if not (Hashtbl.mem formdepsform l) then Hashtbl.add formdepsform l b;
	    Hashtbl.add formdepsfrom l [-h])
	  r
    | [] -> raise (Failure "Clause for common rule with no head?")
  in
  let record_formdeps_conn c0 b =
    match c0 with
    | (h1::h2::r) ->
	if not (Hashtbl.mem formdepsform (-h1)) then Hashtbl.add formdepsform (-h1) b;
	if not (Hashtbl.mem formdepsform (-h2)) then Hashtbl.add formdepsform (-h2) b;
	List.iter
	  (fun l ->
	    if not (Hashtbl.mem formdepsform l) then Hashtbl.add formdepsform l b;
	    Hashtbl.add formdepsfrom l [-h1;-h2])
	  r
    | [h1] -> raise (Failure "Clause for conn rule with only one head?")
    | [] -> raise (Failure "Clause for conn rule with no head?")
  in
  let rectopfrom l z =
    Hashtbl.add formdepsfrom z [l]
  in
  let handle_clause b cr c0 =
    if not (Hashtbl.mem handledclause c0) then
      try
	Hashtbl.add handledclause c0 ();
	match (cr c0) with
	| DeltaRule -> record_formdeps_common c0 b
	| NegPropRule(_) -> record_formdeps_common c0 b
	| PosPropRule(_) -> record_formdeps_common c0 b
	| InstRule(a,m,n) ->
	    record_formdeps_common c0 b;
	    begin
	      match c0 with
	      | (h::_) -> Hashtbl.add formdepsinsts (-h) (ty_f_rev a,ftm_trm name_tp [] n)
	      | [] -> raise (Failure "InstRule with no head?")
	    end
	| FreshRule(_,_,_) -> record_formdeps_common c0 b
	| MatingRule(_,_) -> record_formdeps_conn c0 b
	| ConfrontationRule(_,_) -> record_formdeps_conn c0 b
	|	ChoiceRule(_,p) ->
	    begin
	      List.iter
		(fun l -> Hashtbl.add formdepsform l b)
		c0
	    end
	| Known(l,x,_) ->
	    Hashtbl.add formdepsform l b
      with (** Assumptions have no associated rule info **)
	Not_found ->
	  begin
	    match c0 with
	    | [l] ->
		Hashtbl.add formdepsform l b
	    | _ -> raise (GenericError "Non-Unit Assumption") (*** Unexpected case: Non-unit Assumption ***)
	  end
  in
  let rec pfformdeps_1 c r a =
    match r with
    | SearchR(cl,cr) -> List.iter (handle_clause true cr) cl
    | AssumptionConflictR(_) -> (*** There must be a formula (m,name) on a such that (~m,name2) is on a. Otherwise, there's a bug. ***)
	let rec find_conflict a =
	  match a with
	  | (((Ap(Ap(Imp,m),False)),name)::ar) ->
	      let l = loc_get_literal m in
	      Hashtbl.add formdepsform l true;
	      Hashtbl.add formdepsform (-l) true
	  | ((m,name)::ar) ->
	      let nm = Ap(Ap(Imp,m),False) in
	      let l = loc_get_literal nm in
	      Hashtbl.add formdepsform l true;
	      Hashtbl.add formdepsform (-l) true
	  | [] -> ()
	in
	find_conflict a
    | FalseR ->
	begin
	  try
	    Hashtbl.add formdepsform (loc_get_literal False) true
	  with Not_found -> raise (GenericError "Assumption 'False' Not Found")
	end
    | NegReflR(_) ->
	let rec find_conflict a =
	  match a with
	  | ((((Ap(Ap(Imp,Ap(Ap(Eq(_),m),n)),False)) as emm),name)::_) when (m = n) ->
	      let lemm = loc_get_literal emm in
	      Hashtbl.add formdepsform lemm true
	  | (_::ar) -> find_conflict ar
	  | [] -> raise (GenericError "Assumption of Negated Reflexive Equation Not Found")
	in
	find_conflict a
	  (*** Otherwise, follow the refutation, adding things to the assoc list a as we break down the formulas. ***)
    | NegImpR(_,_,_,m,n,r) ->
	begin
	  try
	    let mn = neg (imp m n) in
	    let name = List.assoc mn a in
	    let lmn = loc_get_literal mn in
	    Hashtbl.add formdepsform lmn true;
	    rectopfrom lmn (loc_get_literal m);
	    rectopfrom lmn (-(loc_get_literal n));
	    pfformdeps_1 c r ((m,name)::(normneg n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (imp m n)))))
	end
    | ImpR(_,_,_,m,n,r1,r2) ->
	begin
	  try
	    let mn = imp m n in
	    let name = List.assoc mn a in
	    let lmn = loc_get_literal mn in
	    Hashtbl.add formdepsform lmn true;
	    rectopfrom lmn (-(loc_get_literal m));
	    rectopfrom lmn (loc_get_literal n);
	    pfformdeps_1 c r1 ((normneg m,name)::a);
	    pfformdeps_1 c r2 ((n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (imp m n))))
	end
    | NegAllR(b,_,_,m,x,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Forall(b),m))) a in
	    let l1 = loc_get_literal (neg (Ap(Forall(b),m))) in
	    let l2 = loc_get_literal (norm name_def (neg (Ap(m,Name(x,b))))) in
	    Hashtbl.add formdepsform l1 true;
	    rectopfrom l1 l2;
	    pfformdeps_1 c r (((norm name_def (neg (Ap(m,Name(x,b))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (Ap(Forall(b),m))))))
	end
    | NegEqFR(a1,a2,_,_,m,n,r) -> 
	begin
	  try
	    let name = List.assoc (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))) a in
	    let l1 = loc_get_literal (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))) in
	    let l2 = loc_get_literal (norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))) in
	    Hashtbl.add formdepsform l1 true;
	    rectopfrom l1 l2;
	    pfformdeps_1 c r (((norm name_def (normneg (forall a1 (eq a2 (Ap(m,DB(0,a1))) (Ap(n,DB(0,a1))))))),name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (Ap(Ap(Eq(mk_ar a1 a2),m),n))))))
	end
    | EqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (eq mk_prop m n) a in
	    let l1 = loc_get_literal (eq mk_prop m n) in
	    let lm = loc_get_literal m in
	    let ln = loc_get_literal n in
	    Hashtbl.add formdepsform l1 true;
	    rectopfrom l1 lm;
	    rectopfrom l1 ln;
	    rectopfrom l1 (-lm);
	    rectopfrom l1 (-ln);
	    pfformdeps_1 c r1 ((m,name)::(normneg n,name)::a);
	    pfformdeps_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (eq mk_prop m n))))
	end
    | NegEqOR(_,_,_,m,n,r1,r2) -> 
	begin
	  try
	    let name = List.assoc (neg (eq mk_prop m n)) a in
	    let l1 = -(loc_get_literal (eq mk_prop m n)) in
	    let lm = loc_get_literal m in
	    let ln = loc_get_literal n in
	    Hashtbl.add formdepsform l1 true;
	    rectopfrom l1 lm;
	    rectopfrom l1 ln;
	    rectopfrom l1 (-lm);
	    rectopfrom l1 (-ln);
	    pfformdeps_1 c r1 ((m,name)::(normneg n,name)::a);
	    pfformdeps_1 c r2 ((normneg m,name)::(n,name)::a)
	  with Not_found -> raise (GenericError ("Unknown Assumption " ^ (trm_str_nice (neg (eq mk_prop m n)))))
	end
  in
  let rec add_conjs cnl cl a =
    match (cnl,cl) with
    | (cn::cnr,(_,ntmn)::cr) -> add_conjs cnr cr ((ftm_trm name_tp [] ntmn,cn)::a)
    | _ -> a
  in
  let a = add_conjs !conjecturenames !conjecture (Hashtbl.fold (fun k v l -> (v,k)::l) name_hyp []) in
  pfformdeps_1 c r a;
  (***
  Printf.printf "allclauses:\n";
  List.iter (fun c0 ->
    List.iter (fun l -> Printf.printf "%d " l) c0;
    if Hashtbl.mem handledclause c0 then
      Printf.printf "(used)\n"
    else
      Printf.printf "\n")
    !allclauses;
     ***)
  List.iter
    (handle_clause false (Hashtbl.find !allclause_ruleinfo))
    !allclauses;
  let usefulcnt = ref 0 in
  let uselesscnt = ref 0 in
  let don : (int,bool * trm) Hashtbl.t = Hashtbl.create 1000 in
  let depslisth : (int * int list,unit) Hashtbl.t = Hashtbl.create 1000 in
  let depslist : (int * int list) list ref = ref [] in
  Hashtbl.iter
    (fun k v ->
      if not (Hashtbl.mem don k) then
	begin
	  if v then incr usefulcnt else incr uselesscnt;
	  Hashtbl.add don k (v,loc_literal_to_trm k)
	end)
    formdepsform;
  Printf.printf "%d formulas generated, %d useful, %d useless\n" (!usefulcnt + !uselesscnt) !usefulcnt !uselesscnt;
  Hashtbl.iter
    (fun k _ ->
      let ll = Hashtbl.find_all formdepsfrom k in
      List.iter (fun v -> if not (Hashtbl.mem depslisth (k,v)) then (depslist := (k,v)::!depslist; Hashtbl.add depslisth (k,v) ())) ll)
   don;
  match o with
  | Some(o) ->
      let f = open_out_bin o in
      output_value f don;
      output_value f !depslist;
      close_out f
  | None -> ()

let refut_trms r =
  let (refutation,_,_,_) = get_refutation (get_initbranch ()) r in
  ref_trms refutation
