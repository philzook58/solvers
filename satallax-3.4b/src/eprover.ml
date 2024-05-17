open Atom
open Error
(*
open Foform
*)
open Fomapping
open State
open Refut
open Term
open Log
open Flags
open Eproverstate
open Searchoption
open Search
open Lfthform
open Lfthmapping

let eproverperiod = ref 10
let eprovertimeout = ref 1
let foffiles = ref false
let pfrecondebug = false


let e_genflags () =
  [ "-s" (* silent *)
  ; if get_bool_flag "E_AUTOSCHEDULE" then "--auto-schedule" else "--auto"
  ; "--tptp3-in"
  ; "--tb-insert-limit=" ^ (string_of_int (1000000 * !eprovertimeout))
  ] @
  (match !timeout with
  | Some _ -> ["--cpu-limit=" ^ string_of_int (int_of_float (remaining_time ()))]
  | None -> [])

let e_proofflags () =
  (if mkprooftermp () then ["--tstp-out"; "--proof-object"] else [])

(*
let write_foffile b =
  let foffilename = "/tmp/fof" ^ (string_of_float (Unix.time ())) ^ "p" in
  let foffile = open_out foffilename in
  printf_fof_file foffile b;
  close_out foffile;
  Printf.printf "./E/PROVER/eprover-ho %s %s\n%!" (get_eflags ()) foffilename;
  Unix.sleep 1 (*** sleep for a second so the names will be unique ***)
*)

let write_lfthfile () =
  let filename = "/tmp/lfth" ^ (string_of_float (Unix.time ())) ^ "p" in
  let c = open_out filename in
  fprintf_lfth_problem c;
  close_out c;
  let cmd = !Config.eprover :: filename :: e_genflags () @ e_proofflags () in
  Printf.printf "%s\n%!" (String.concat " " cmd);
  Unix.sleep 1 (*** sleep for a second so the names will be unique ***)



let read_e_core eout =
  let pcore = ref [] in
  let fcore = ref [] in
  let elines = ref [] in
  try
    while true do
      match input_line eout with
      | l when not (l = "# SZS output start CNFRefutation." || l = "# SZS output start CNFRefutation") -> ()
      | _ ->
	  while true do
	    match input_line eout with
	    | "# SZS output end CNFRefutation." -> raise Exit
	    | "# SZS output end CNFRefutation" -> raise Exit
	    | l ->
		if !verbosity > 40 then (Printf.printf "eref: %s\n" l; flush stdout);
		elines := l::!elines;
		let n = String.length l in
		let i = ref (n-1) in
		let a = ref 0 in
		while !i > 0 && l.[!i] != '(' do decr i done;
		try
		  if !i > 7 && String.sub l (!i-7) 7 = "initial" then
		    let proppart = ref false in
		    let pos = ref true in
		    while !i < n && l.[!i] != ' ' do incr i done;
		    incr i;
		    if !i + 3 >= n then raise Not_found;
		    if String.sub l !i 2 = "ax" then
		      (proppart := true; i := !i - 1)
		    else if String.sub l !i 3 = "nax" then
		      pos := false
		    else if not (String.sub l !i 3 = "pax") then
		      raise Not_found;
		    i := !i + 3;
		    while !i < n && l.[!i] != ')' do
		      let d = Char.code l.[!i] in
		      incr i;
		      if d >= 48 && d < 58 then
			a := (d-48) + !a * 10
		      else
			raise Not_found
		    done;
		    if !proppart then
		      begin
			if !verbosity > 30 then (Printf.printf "propositional matrix part of E core: %d\n" !a; flush stdout);
			pcore := !a::!pcore
		      end
		    else
		      begin
			if not !pos then a := (- !a);
			if !verbosity > 30 then (Printf.printf "formula part of E core: %d\n" !a; flush stdout);
			fcore := !a::!fcore
		      end
		with Not_found -> Printf.printf "Not_found raised with i = %d\n" !i;
	  done
    done;
    raise Exit (*** unreachable, raise here for ocaml type checking ***)
  with Exit ->
    (!pcore,!fcore,List.rev !elines)


let folabel l =
  if String.length l > 4 && (String.sub l 0 4 = "fof(" || String.sub l 0 4 = "cnf(") then
    begin
      let b = Buffer.create 5 in
      try
        for i = 4 to String.length l - 1 do
          if l.[i] = ',' then
            raise Exit
          else
            Buffer.add_char b l.[i]
        done;
        raise Not_found
      with Exit -> Buffer.contents b
    end
  else
    raise Not_found


let whitespace_p c = Char.code c <= 32

let upperalpha_p c = let cc = Char.code c in cc >= 65 && cc <= 90

let alphanum_p c = let cc = Char.code c in cc >= 48 && cc < 58 || cc >= 65 && cc <= 90 || cc >= 97 && cc <= 122

let namechar_p c = c = '_' || alphanum_p c

let fofuntp a n = let r = ref a in for i = 1 to n do r := Ar(a,!r) done; !r

let parse_e_name a gnl l n i =
  let j = ref i in
  while !j < n && namechar_p l.[!j] do
    incr j
  done;
  if !j < n then
    (String.sub l i (!j - i),l,n,!j)
  else
    let l = gnl() in
    (String.sub l i (!j - i),l,String.length l,0)

let rec skip_to_next_char gnl l n i =
  if i >= n then
    let l = gnl() in
    skip_to_next_char gnl l n i
  else
    (l,n,i)

let rec skip_whitespace gnl l n i =
  let (l,n,i) = skip_to_next_char gnl l n i in
  if whitespace_p l.[i] then
    skip_whitespace gnl l n (i+1)
  else
    (l,n,i)

let rec parse_e_fotrm a gnl l n i =
  let (l,n,i) = skip_whitespace gnl l n i in
  if l.[i] = 'c' then (*** Came from a name of non-prop base type in the problem (possibly an eigenvar/param) ***)
    let (nm,l,n,i) = parse_e_name a gnl l n (i+1) in
    (Name(nm,a),false,l,n,i)
  else if l.[i] = 'f' then (*** Came from a name of function type ultimately returning a non-prop base type in the problem ***)
    let (nm,l,n,i) = parse_e_name a gnl l n (i+1) in
    let (argl,sk,l,n,i) = parse_e_foargs a gnl l n i true in
    let tm = List.fold_left (fun x y -> Ap(x,y)) (Name(nm,fofuntp a (List.length argl))) argl in
    (tm,sk,l,n,i)
  else if upperalpha_p l.[i] then (*** Variable, just replace with choice applied to constant false to get a 'default' element of type a ***)
    let (nm,l,n,i) = parse_e_name a gnl l n i in
    (Ap(Choice(a),Lam(a,False)),false,l,n,i)
  else (*** Treat everything else as a Skolem created by E, so just parse it to continue parsing but ultimately drop the result ***)
    let (nm,l,n,i) = parse_e_name a gnl l n i in
    let (argl,_,l,n,i) = parse_e_foargs a gnl l n i true in
    let tm = List.fold_left (fun x y -> Ap(x,y)) (Name(nm,fofuntp a (List.length argl))) argl in
    (tm,true,l,n,i)
and parse_e_foargs a gnl l n i fst =
  let (l,n,i) = skip_whitespace gnl l n i in
  if l.[i] = '(' && fst then
    let (tm,sk1,l,n,i) = parse_e_fotrm a gnl l n (i+1) in
    let (argl,sk2,l,n,i) = parse_e_foargs a gnl l n i false in
    (tm::argl,sk1 && sk2,l,n,i)
  else if l.[i] = ',' && not fst then
    let (tm,sk1,l,n,i) = parse_e_fotrm a gnl l n (i+1) in
    let (argl,sk2,l,n,i) = parse_e_foargs a gnl l n i false in
    (tm::argl,sk1 && sk2,l,n,i)
  else if l.[i] = ')' && not fst then
    let (l,n,i) = skip_to_next_char gnl l n (i+1) in
    ([],false,l,n,i)
  else
    ([],false,l,n,i)

let rec parse_e_fotrms a gnl l n i =
  let (l,n,i) = skip_to_next_char gnl l n i in
  let (tm,b,l,n,i) = parse_e_fotrm a gnl l n i in
  let (l,n,i) = skip_whitespace gnl l n i in
  if l.[i] = ',' then
    let (tmr,l,n,i) = parse_e_fotrms a gnl l n (i+1) in
    if b then (*** tm has a Skolem, so drop it and all the terms following it ***)
      ([],l,n,i)
    else
      (tm::tmr,l,n,i)
  else if l.[i] = ']' then
    let (l,n,i) = skip_to_next_char gnl l n (i+1) in
    if b then (*** tm has a Skolem, so drop it ***)
      ([],l,n,i)
    else
      ([tm],l,n,i)
  else
    begin
      if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (6), ignoring.\n%s %d\n" l i; flush stdout);
      ([],l,n,i)
    end
	
let parse_e_answers_e a gnl l n i =
  let (l,n,i) = skip_to_next_char gnl l n i in
  if l.[i] = '_' then
    let (l,n,i) = skip_to_next_char gnl l n (i+1) in
    if l.[i] = ']' then
      begin
	([],l,n,i)
      end
    else
      begin
	if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (1), ignoring.\n"; flush stdout);
	([],l,n,i)
      end
  else
    begin
      if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (2), ignoring.\n"; flush stdout);
      ([],l,n,i)
    end

let rec parse_e_answers_2 a gnl l n i =
  let (l,n,i) = skip_to_next_char gnl l n i in
  if l.[i] = '(' then
    parse_e_answers_d a gnl l n (i+1)
  else if l.[i] = '[' then
    let (trml,l,n,i) = parse_e_fotrms a gnl l n (i+1) in
    if trml = [] then
      ([],l,n,i)
    else
      ([trml],l,n,i)
  else
    begin
      if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (3), ignoring.\n%s\n%d\n" l i; flush stdout);
      ([],l,n,i)
    end    
and parse_e_answers_d a gnl l n i =
  let (l,n,i) = skip_to_next_char gnl l n i in
  if l.[i] = '(' then
    parse_e_answers_d a gnl l n (i+1)
  else if l.[i] = '[' then
    let (trml,l,n,i) = parse_e_fotrms a gnl l n (i+1) in
    let (l,n,i) = skip_whitespace gnl l n i in
    if l.[i] = ')' then
      let (l,n,i) = skip_to_next_char gnl l n (i+1) in
      if trml = [] then
	([],l,n,i)
      else
	([trml],l,n,i)
    else if l.[i] = '|' then
      let (answl,l,n,i) = parse_e_answers_d a gnl l n (i+1) in
      if trml = [] then
	(answl,l,n,i)
      else
	(trml::answl,l,n,i)
    else
      begin
	if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (4), ignoring. %s %d\n" l i; flush stdout);
	([],l,n,i)
      end
  else
    begin
      if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (5), ignoring. %s %d\n" l i; flush stdout);
      ([],l,n,i)
    end

let rec parse_e_answers a gnl l n i fst =
  let (l,n,i) = skip_to_next_char gnl l n i in
  if whitespace_p l.[i] then
    parse_e_answers a gnl l n (i+1) fst
  else if l.[i] = '[' && fst || l.[i] = ',' && not fst then
    let (answl1,l,n,i) = parse_e_answers_2 a gnl l n (i+1) in (*** either an answer tuple or disjunctions of answer tuples ***)
    let (answl2,l,n,i) = parse_e_answers a gnl l n i false in
    ((answl1 @ answl2),l,n,i)
  else if l.[i] = ']' then
    let (l,n,i) = skip_to_next_char gnl l n (i+1) in
    ([],l,n,i)
  else if l.[i] = '|' then
    parse_e_answers_e a gnl l n (i+1)
  else
    begin
      if !verbosity > 0 then (Printf.printf "Unexpected case while parsing answers from E (3), ignoring.\n%s\n%i\n" l i; flush stdout);
      ([],l,n,i)
    end

let read_e_answers a eout =
  let answers = ref [] in
  try
    while true do
      match input_line eout with
      | l when String.length l > 20 && String.sub l 0 20 = "# SZS answers Tuple " ->
          if !verbosity > 25 then (Printf.printf "Answers: %s\n" l; flush stdout);
	  let get_next_line () = input_line eout in
	  let (answl,_,_,_) = parse_e_answers a get_next_line l (String.length l) 20 true in
	  if !verbosity > 10 then (Printf.printf "parse_e_answers gave:\n"; List.iter (fun ml -> List.iter (fun m -> Printf.printf " *%s" (trm_str m)) ml; Printf.printf "\n") answl; Printf.printf "\n"; flush stdout);
	  answers := answl;
	  if !answers = [] then
	    raise Not_found (*** this is what should happen if all the answers had Skolems ***)
	  else
	    raise Exit
      | _ -> ()
    done;
    raise Not_found (*** unreachable, but here for type checking ***)
  with Exit -> !answers

let rec instantiate_with s insts =
  match insts with
  | [] -> s
  | (t::_) -> (*** in principle could keep instantiating if there are multiple foralls in a row (here I'm only using the first term in each 'answer tuple') ***)
      match s with
      | Ap(Forall(a),s1) ->
	  let n = get_literal s in
	  forall_rule (- n) a s1 t
      | _ -> raise (Failure "instantiate_with called without enough foralls")





type fo =
 { poslits : (int * trm) list
 ; neglits : (int * trm) list
 ; poseqns : (int * trm) list
 ; negeqns : (int * trm) list
 }

let mated : (int * int,unit) Hashtbl.t = Hashtbl.create 10
let confronted : (int * int,unit) Hashtbl.t = Hashtbl.create 10

let print_question c foralls delayforalls fo n s =
  printf_fof_file_propmatrix c;
  List.iter (fun (n1,s1) -> printf_fof_pol_ax c n1 s1) delayforalls;
  List.iter (fun (n1,s1) -> if not (n = n1) then printf_fof_pol_ax c n1 s1) foralls;
  List.iter (fun (n1,s1) -> printf_fof_pol_ax c n1 s1) fo.poseqns;
  List.iter (fun (n1,s1) -> printf_fof_pol_ax c n1 s1) fo.negeqns;
  List.iter (fun (n1,s1) -> printf_fof_pol_ax c n1 s1) fo.poslits;
  List.iter (fun (n1,s1) -> printf_fof_pol_ax c n1 s1) fo.neglits;
  (*** Here ask the question for (n,s) -- maybe with multiple exists ***)
  printf_fof_question c n s


(*** break down first-order formulas used by E until the rest of the proof just involves equational reasoning with a propositional matrix (mating, confrontation, decomposition) ***)
let rec construct_refutation_with_e_mat fo delayforalls =
  if !verbosity > 40 then
    begin
      Printf.printf "mat\n";
      List.iter (fun (n,s) -> Printf.printf "%d: %s\n" n (trm_str s)) fo.poslits;
      List.iter (fun (n,s) -> Printf.printf "%d: %s\n" n (trm_str s)) fo.neglits;
      List.iter (fun (n,s) -> Printf.printf "%d: %s\n" n (trm_str s)) fo.poseqns;
      List.iter (fun (n,s) -> Printf.printf "%d: %s\n" n (trm_str s)) fo.negeqns;
    end;
  let newdeqns = ref [] in
  let processnew ndel =
    List.iter
      (fun de ->
	try
	  ignore (List.find (fun (_,s) -> de = s) fo.negeqns)
	with Not_found ->
	  newdeqns := de::!newdeqns)
      ndel
  in
  List.iter
    (fun (nn,na) ->
      match neg_body na with
      | Some(t1) ->
	  let (t1h,t1a) = head_spine t1 in
	  List.iter
	    (fun (pn,pa) ->
	      let (t2h,t2a) = head_spine pa in
	      if t1h = t2h && not (Hashtbl.mem mated (pn,nn)) then
		begin
		  processnew (mate pn nn t2a t1a);
		  Hashtbl.add mated (pn,nn) ();
		end)
	    fo.poslits
      | _ -> raise (Failure "not a neg atom"))
    fo.neglits;
  List.iter
    (fun (nn,ne) ->
      match neg_body ne with
      | Some(Ap(Ap(Eq(a),nel),ner)) ->
	  List.iter
	    (fun (pn,pe) ->
	      match pe with
	      | Ap(Ap(Eq(b),pel),per) ->
		  if a = b && not (Hashtbl.mem confronted (pn,nn)) then
		    begin
		      processnew (confront a pn pel per nn nel ner);
		      Hashtbl.add confronted (pn,nn) ();
		    end
	      | _ -> raise (Failure "not a pos eqn"))
	    fo.poseqns
      | _ -> raise (Failure "not a neg eqn"))
    fo.negeqns;
  construct_refutation_with_e_decompose !newdeqns delayforalls fo (*** at this point the delayed foralls may be reconsidered since some other progress has presumably been made ***)
and construct_refutation_with_e_foralls foralls delayforalls fo =
  if !verbosity > 40 then
    begin
      List.iter (fun (_,s) -> Printf.printf "%s\n" (trm_str s)) foralls;
    end;
  (*** if there is a forall here, we call E again as a 'question' with an existential to get the instantiations we need; then we may need to start the whole process again with the new ecore ***)
  match foralls with
  | [] ->
      construct_refutation_with_e_mat fo delayforalls
  | (n,s)::forallr ->
      let a =
	match s with
	| Ap(Forall(a),_) -> a
	| _ -> raise (Failure "An alleged forall was not a forall")
      in
      (* TODO: remove code duplication with `call_e` here *)
      if !foffiles then
	begin
	  let foffilename = "/tmp/fofanswer" ^ (string_of_float (Unix.time ())) ^ "p" in
	  let foffile = open_out foffilename in
	  print_question foffile foralls delayforalls fo n s;
	  close_out foffile;
	  let cmd = !Config.eprover :: "--proof-object" :: e_genflags () in
	  Printf.printf "%s < %s\n%!" (String.concat " " cmd) foffilename;
	  Unix.sleep 1; (*** sleep for a second so the names will be unique ***)
	end;
      let cmd = String.concat " " (!Config.eprover :: "--answers=1" :: e_genflags ()) in
      let (myout,myin,myerr) = Unix.open_process_full cmd [| |] in
      print_question myin foralls delayforalls fo n s;
      close_out myin;
      (*** read the answer to get the instantiations and read the new ecore in case we can further filter ***)
      try
	let instl = read_e_answers a myout in
	match instl with
	| [] ->
	    raise Not_found (*** this might mean all the instantiations had skolems ***)
	| _ ->
	    ignore(Unix.close_process_full(myout,myin,myerr));
	    let nw = List.map (instantiate_with s) instl in
	    if !verbosity > 10 then (Printf.printf "New instantiations of %d: %s:\n" n (trm_str s); List.iter (fun m -> Printf.printf "%d: %s\n" (get_literal m) (trm_str m)) nw; Printf.printf "\n"; flush stdout);
	    construct_refutation_with_e_new
	      nw [] (delayforalls @ forallr @ [(n,s)]) fo (*** Note: Include (n,s) again at the end in case it needs to be instantiated again later. ***)
      with
      | Not_found
      | End_of_file ->
	  ignore(Unix.close_process_full(myout,myin,myerr));
	  construct_refutation_with_e_foralls forallr ((n,s)::delayforalls) fo
and construct_refutation_with_e_decompose todecompose foralls fo : unit = (*** process formulas which are easy to decompose ***)
  if !verbosity > 30 then
    begin
      Printf.printf "decompose\n";
      List.iter (fun s -> Printf.printf "%s\n" (trm_str s)) todecompose;
      Printf.printf "foralls\n";
      List.iter (fun (n,s) -> Printf.printf "%d: %s\n" n (trm_str s)) foralls;
    end;
  match todecompose with
  | [] -> (*** At this point, I used to compute a new core to get rid of unused formulas, but this caused trouble since some new useful formulas are logically redundant; so deleting them led to cycles. ***)
   construct_refutation_with_e_foralls foralls [] fo
  | s::todecomposer ->
      match neg_body s with
      | Some(Ap(Ap(Imp,s1),s2)) ->
	  if not (Hashtbl.mem processed s) then process_unprocessed_prop (get_literal s) s;
	  construct_refutation_with_e_new [s1;normneg s2] todecomposer foralls fo
      | Some(Ap(Forall(a),s1)) -> (*** exists ***)
	  let ns1w = negforall_rule (get_literal s) a s1 in
	  construct_refutation_with_e_new [ns1w] todecomposer foralls fo
      | Some(Ap(Ap(Eq(Prop),t1),t2)) -> (*** diseqn treated as Equivalence ***)
	  if not (Hashtbl.mem processed s) then process_unprocessed_prop (get_literal s) s;
	  construct_refutation_with_e_new [t1;t2;normneg t1;normneg t2] todecomposer foralls fo
      | Some((Ap(Ap(Eq(a),t1),t2)) as ns) -> (*** if this is here, check if the decomposition rule can be applied ***)
	  let (t1h,t1a) = head_spine t1 in
	  let (t2h,t2a) = head_spine t2 in
	  let n = get_literal s in
	  if t1h = t2h then
	    begin
	      decompose n t1a t2a (Some(Refut.NegPropRule(ns)));
	      let newdeqns =
		List.map2
		  (fun la ra -> normneg (ueq la ra))
		  t1a t2a
	      in
	      construct_refutation_with_e_decompose (newdeqns @ todecomposer) foralls { fo with negeqns = (n,s)::fo.negeqns }
	    end
	  else
	    construct_refutation_with_e_decompose todecomposer foralls { fo with negeqns = (n,s)::fo.negeqns }
      | Some(_) -> raise (Failure "unexpected case in construct_refutation_with_e_decompose")
      | None ->
	  match s with
	  | Ap(Ap(Imp,s1),s2) ->
	      if not (Hashtbl.mem processed s) then process_unprocessed_prop (get_literal s) s;
	      construct_refutation_with_e_new [normneg s1;s2] todecomposer foralls fo
	  | Ap(Ap(Eq(Prop),s1),s2) -> (*** eqn treated as Equivalence ***)
	      if not (Hashtbl.mem processed s) then process_unprocessed_prop (get_literal s) s;
	      construct_refutation_with_e_new [s1;s2;normneg s1;normneg s2] todecomposer foralls fo
	  | _ -> raise (Failure "unexpected case in construct_refutation_with_e_decompose")
and construct_refutation_with_e_new nw todecompose foralls fo : unit = (*** classify new formulas and continue ***)
  let scons s l = if List.mem s l then l else s::l in
  let ncons (n,s) l = if List.mem_assoc n l then l else (n,s)::l in
  match nw with
  | [] -> construct_refutation_with_e_decompose todecompose foralls fo
  | s::nwr ->
      force_into_propmatrix (get_literal s); (*** just in case some clause involving s was among the propositional clauses but was omitted because there was a way to do the proof without it (eg, letting E instantiate the quantifier instead of using its instance) ***)
      match neg_body s with
      | Some(Ap(Ap(Imp,_),_))
      | Some(Ap(Forall(_),_))
      | Some(Ap(Ap(Eq(Prop),_),_))
      | Some(Ap(Ap(Eq(_),_),_)) -> (*** put onto todecompose in case the decomposition rule can be applied ***)
	  construct_refutation_with_e_new nwr (scons s todecompose) foralls fo
      | Some(_) -> construct_refutation_with_e_new nwr todecompose foralls { fo with neglits = ncons (get_literal s,s) fo.neglits }
      | None ->
	  match s with
	  | Ap(Ap(Imp,_),_)
	  | Ap(Ap(Eq(Prop),_),_) -> construct_refutation_with_e_new nwr (scons s todecompose) foralls fo
	  | Ap(Forall(a),_) -> construct_refutation_with_e_new nwr todecompose (ncons (get_literal s,s) foralls) fo
          | Ap(Ap(Eq(a),_),_) -> construct_refutation_with_e_new nwr todecompose foralls { fo with poseqns = ncons (get_literal s,s) fo.poseqns }
          | _ -> construct_refutation_with_e_new nwr todecompose foralls { fo with poslits = ncons (get_literal s,s) fo.poslits }

let construct_refutation_with_e (pcore,fcore,elines) =
  let todecompose = ref [] in
  let foralls = ref [] in
  let foposlits = ref [] in
  let foneglits = ref [] in
  let foposeqns = ref [] in
  let fonegeqns = ref [] in
  filter_unnec_from_propmatrix pcore;
  List.iter
    (fun n ->
      let s = literal_to_trm n in
      match neg_body s with
      | Some(Ap(Ap(Imp,_),_)) (*** Note that double negation falls into this case. ***)
      | Some(Ap(Forall(_),_))
      | Some(Ap(Ap(Eq(Prop),_),_)) -> todecompose := s::!todecompose (*** treat as equivalence ***)
      | Some(Ap(Ap(Eq(a),_),_)) -> fonegeqns := (n,s)::!fonegeqns
      | Some(_) -> foneglits := (n,s)::!foneglits
      | None ->
	match s with
	| Ap(Ap(Imp,_),_) -> todecompose := s::!todecompose
	| Ap(Forall(a),_) -> foralls := (n,s)::!foralls
	| Ap(Ap(Eq(Prop),s1),s2) -> todecompose := s::!todecompose (*** treat as Equivalence ***)
	| Ap(Ap(Eq(a),s1),s2) -> foposeqns := (n,s)::!foposeqns
	| _ -> foposlits := (n,s)::!foposlits) (*** This can't have Choice(a) as head since it wouldn't be considered "first-order". s must be a first-order atom or an equation. ***)
    fcore;
  construct_refutation_with_e_decompose !todecompose !foralls
    { poslits = !foposlits; neglits = !foneglits
    ; poseqns = !foposeqns; negeqns = !fonegeqns }

(*
let call_e b =
  if (!verbosity > 4) then (Printf.printf "Calling E on FOF for type %s\n" (stp_str b); flush stdout);
  if (!foffiles) then write_foffile b;
  let etimeoutnow = get_etimeoutnow () in
  if (etimeoutnow > 0) then
    begin
      if (!verbosity > 4) then Printf.printf "Calling E for %d seconds.\n" etimeoutnow;
      let (myout,myin,myerr) = Unix.open_process_full (!Config.eprover ^ get_eflags()) [| |] in
      printf_fof_file myin b;
      close_out myin;
      if (!verbosity > 4) then (Printf.printf "About to read result from eprover\n"; flush stdout);
      try
	while true do
	  match (input_line myout) with
	  | "# SZS status Unsatisfiable" ->
              if (!foffiles) then
		begin
		  let fsfilename = "/tmp/fs" ^ (string_of_float (Unix.time ())) ^ ".lisp" in
		  let fsfile = open_out fsfilename in
		  printf_fs_file fsfile b;
		  close_out fsfile;
		end;
	      begin
		match !mkproofterm with
		| None ->
		    ignore(Unix.close_process_full(myout,myin,myerr));
		    raise (Unsatisfiable None)
		| Some(TSTP) ->
                    let (pcore,fcore,elines) = read_e_core myout in
		    ignore(Unix.close_process_full(myout,myin,myerr));
		    let cri = !clause_ruleinfo in
		    raise (Unsatisfiable(Some(Eprover(List.map (fun z -> Hashtbl.find propmatrixh z) pcore,Hashtbl.find cri,fcore,elines))))
		| Some(ptk) ->
		    enable_pattern_clauses := false; (*** since we aren't doing general search anymore, turn off pattern clauses ***)
                    let ecore = read_e_core myout in
                    if pfrecondebug then verbosity := 41;
		    ignore(Unix.close_process_full(myout,myin,myerr));
		    construct_refutation_with_e ecore
	      end
	  | _ -> ()
	done
      with
      | End_of_file -> ignore(Unix.close_process_full(myout,myin,myerr))
      | Exit -> ()
    end
*)

let enough_time_for_e () =
  match !timeout with
  | Some _ -> int_of_float (remaining_time ()) > 0
  | None -> true

let call_ehoh () =
  if (!verbosity > 4) then Printf.printf "Calling E-HO\n%!";
  if (!foffiles) then write_lfthfile ();
  if enough_time_for_e () then
    begin
      let cmd = String.concat " " (!Config.eprover :: e_genflags () @ e_proofflags ()) in
      if (!verbosity > 4) then Printf.printf "Calling E-HO: %s\n%!" cmd;
      let (myout,myin,myerr) = Unix.open_process_full cmd [| |] in
      fprintf_lfth_problem myin;
      close_out myin;
      if (!verbosity > 4) then Printf.printf "About to read result from eprover\n%!";
      try
	while true do
	  match (input_line myout) with
	  | "# SZS status Unsatisfiable" ->
	      begin
		match !mkproofterm with
		| None ->
		    ignore(Unix.close_process_full(myout,myin,myerr));
		    raise (Unsatisfiable None)
		| Some(TSTP) ->
                    let (pcore,fcore,elines) = read_e_core myout in
		    ignore(Unix.close_process_full(myout,myin,myerr));
		    let cri = !clause_ruleinfo in
		    raise (Unsatisfiable(Some(Eprover(List.map (fun z -> Hashtbl.find propmatrixh z) pcore,Hashtbl.find cri,fcore,elines))))
		| Some(ptk) ->
		    enable_pattern_clauses := false; (*** since we aren't doing general search anymore, turn off pattern clauses ***)
                    let ecore = read_e_core myout in
                    if pfrecondebug then verbosity := 41;
		    ignore(Unix.close_process_full(myout,myin,myerr));
		    construct_refutation_with_e ecore
	      end
	  | _ -> ()
	done
      with
      | End_of_file -> ignore(Unix.close_process_full(myout,myin,myerr))
      | Exit -> ()
    end

(*
let new_possible_fo_formula m a =
  try
    ignore (new_possible_fo_formula_1 m a
	      (fun b -> 
		let r = Hashtbl.find fo_ecounter b in
		incr r;
		if (!r >= !eproverperiod) then (r := 0; call_e b)))
 with NotFO -> ()
*)

let new_possible_lfth_formula m a =
  try
    Lfthmapping.new_possible_lfth_formula_1 m a;
    incr lfth_ecounter;
    if !verbosity > 4 then Format.printf "r = %d, eproverperiod = %d\n%!" !lfth_ecounter !eproverperiod;
    if (!lfth_ecounter >= !eproverperiod) then
      (lfth_ecounter := 0; call_ehoh ())
 with NotLFTH -> ()

let setup_eprover () =
  if get_bool_flag "USE_E" then
(*
  if get_bool_flag "USE_EHOH" then
*)
    (if Sys.file_exists !Config.eprover
    then Atom.new_atom_actions := new_possible_lfth_formula::!Atom.new_atom_actions
    else print_endline "Warning: eprover not found!")
  ;
(*
  else if get_bool_flag "USE_E" then
    (if Sys.file_exists !Config.eprover
    then Atom.new_atom_actions := new_possible_fo_formula::!Atom.new_atom_actions
    else print_endline "Warning: eprover not found!");
*)

  setup_fomapping ();
  eproverperiod := get_int_flag "E_PERIOD";
  eprovertimeout := get_int_flag "E_TIMEOUT"
