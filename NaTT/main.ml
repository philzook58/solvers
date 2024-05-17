open Params
open Strategy
open Sym
open Term
open Trs
open Dp
open Util
open Xml
open Io

type result =
| YES
| MAYBE
| NO

(* static usable rules *)
let static_usable_rules (trs : #trs) (estimator : #Estimator.t) (dg : #dg) used_dps =
	if dg#minimal then (
		let used = Hashtbl.create 128 in
		let rec sub (Node(_,ts) as t) =
			let iterer i =
				if not (Hashtbl.mem used i) then begin
					let rule = trs#find_rule i in
					Hashtbl.add used i ();
					sub rule#r;
				end;
			in
			List.iter iterer (estimator#find_matchable t);
			List.iter sub ts;
		in
		List.iter (fun i -> let Node(_,ts) = (dg#find_dp i)#r in List.iter sub ts) used_dps;
	
		trs#fold_rules
		(fun i _ (usables,unusables) ->
			if Hashtbl.mem used i then (i::usables,unusables) else (usables,i::unusables)
		) ([],[])
	) else (
		trs#fold_rules (fun i _ is -> i::is) [], []
	)


let freeze =
	if params.freezing then
		fun (trs : #trs) (dg : #dg) ->
			comment (puts "Freezing");
			let appsyms = Freezing.auto_freeze trs dg in
			if appsyms = [] then
				(comment (puts " ... failed." << endl); false)
			else (
				comment (fun (pr : #printer) ->
					List.iter (fun (a : #sym) -> pr#putc ' '; a#output pr) appsyms;
					pr#endl;
				);
				problem trs#output;
				true
			)
	else
		fun _ _ -> false

let theory_test (trs : #trs) =
	let ths = trs#get_ths in
	let ths = StrSet.remove "A" ths in
	let ths = StrSet.remove "C" ths in
	let ths = StrSet.remove "AC" ths in
	if not (StrSet.is_empty ths) then begin
		warning (fun _ -> prerr_endline ("Unacceptable theories: " ^ StrSet.fold (^) ths ""));
		raise Unknown;
	end;;

(* extra variable test *)
let extra_test (trs : #trs) =
	let iterer i rule =
		if rule#has_extra_variable then begin
			proof (puts "Extra variable in rule " << put_int i << puts "." << endl);
			raise Nonterm;
		end;
	in
	trs#iter_rules iterer;;

(* remove trivial relative rules *)
let trivial_test (trs : #trs) =
	let iterer i rule =
		if rule#l = rule#r then begin
			if rule#is_strict then begin
				proof (puts "Trivially nonterminating rule " << put_int i << puts "." << endl);
				raise Nonterm;
			end else if rule#is_weak then begin
				proof (puts "Removing trivial weak rule " << put_int i << puts "." << endl);
				trs#remove_rule i;
			end;
		end;
	in
	trs#iter_rules iterer;;


(* rule removal processor *)
let dummy_estimator = Estimator.tcap (new trs)
let dummy_dg = new dg (new trs) dummy_estimator

let rule_remove (trs : #trs) next =
	if Array.length params.orders_rule = 0 then
		next trs
	else
		let proc_list =
			let folder p procs =
				new Wpo.t p trs dummy_estimator dummy_dg :: procs
			in
			Array.fold_right folder params.orders_rule []
		in
		let remove_strict rules =
			List.exists (fun proc -> proc#remove_rules rules) proc_list
		in
		let rec loop () =
			let rules = trs#fold_rules (fun i _ is -> i::is) [] in
			comment (puts "Number of strict rules: " << put_int trs#get_size_strict << endl);
			if trs#get_size_strict = 0 then (
				cpf (MyXML.tag "acRIsEmpty");
				YES
			) else (
				if remove_strict rules then (
					cpf (MyXML.enter "acTerminationProof");
					let ret = loop () in
					cpf(MyXML.leave "acTerminationProof");
					cpf (MyXML.leave "acRuleRemoval");
					ret
				) else (
					comment (puts " failed." << endl);
					next trs
				)
			)
		in
		loop ()

let remove_unusable (trs : #trs) (estimator : #Estimator.t) (dg : #dg) sccs =
	let dps = List.concat sccs in
	let curr_len = List.length dps in
	if curr_len < dg#count_dps then begin
(* The following assumes non-Ce compatible method is not applied *)
		log (puts "Removing unusable rules: {");
		let (_,unusables) = static_usable_rules trs estimator dg dps in
		let rule_remover i =
			if (trs#find_rule i)#is_strict then begin
				log (puts " " << put_int i);
				trs#remove_rule i;
			end;
		in
		List.iter rule_remover unusables;
		log (puts " }" << endl);
	end;;

(* reduction pair processor *)
let dp_remove (trs : #trs) (estimator : #Estimator.t) (dg : #dg) =
	let scc_sorter =
		let scc_size scc =
			List.fold_right (fun i r -> dg#get_dp_size i + r) scc 0
		in
		if params.cpf then fun sccs -> List.rev sccs (* CeTA wants this *)
		else List.sort (fun scc1 scc2 -> compare (scc_size scc1) (scc_size scc2))
	in
	let use_all_rules = ref false in
	let use_usable_rules = ref false in
	let (orders_dp, orders_edge) =
		let folder p procs =
			if not dg#minimal then p.usable <- false;
			if p.usable then begin
				use_usable_rules := true;
			end else begin
				use_all_rules := true;
			end;
			new Wpo.t p trs estimator dg :: procs
		in
		Array.fold_right folder params.orders_dp [],
		Array.fold_right folder params.orders_edge []
	in
	let all_rules =
		if !use_all_rules then
			trs#fold_rules (fun i _ is -> i::is) []
		else []
	in
	let usables =
		if !use_usable_rules then
			fun scc ->
			let ret = fst (static_usable_rules trs estimator dg scc) in
			fun proc ->
			if proc#using_usable then ret else all_rules
		else fun _ _ -> []
	in
	let remove_strict scc =
		let rec sub = function
		| [] -> None
		| proc :: procs ->
			match proc#remove_nodes (usables scc proc) scc with
			| Some scc -> Some scc
			| None -> sub procs
		in
		sub orders_dp
	in
	let remove_edges scc =
		let rec sub = function
		| [] -> false
		| proc :: procs -> proc#remove_post_edges (usables scc proc) scc || sub procs
		in
		sub orders_edge
	in
	let sccs = dg#get_sccs in
	let sccs = scc_sorter sccs in

	if dg#minimal then remove_unusable trs estimator dg sccs;

	let rec dg_proc n_sccs sccs =
		cpf (MyXML.enter "acDPTerminationProof" << MyXML.enter "acDepGraphProc");
		let ret = loop n_sccs sccs in
		cpf (MyXML.leave "acDepGraphProc" << MyXML.leave "acDPTerminationProof");
		ret
	and loop n_sccs sccs =
		comment (puts "Number of SCCs: " << put_int n_sccs << puts ", DPs: " <<
			put_int dg#count_dps << puts ", edges: " << put_int dg#count_edges << endl
		);
		loop_silent n_sccs sccs
	and loop_silent n_sccs = function
		| [] -> YES
		| scc::sccs ->
			cpf (
				MyXML.enter "component" <<
				MyXML.enclose "dps" (MyXML.enclose "rules" (dg#output_scc_xml scc))
			);
(* Please improve CeTA!
			if dg#triv_scc scc then (
				cpf (
					MyXML.enclose_inline "realScc" (puts "false") <<
					MyXML.leave "component"
				);
				loop_silent n_sccs sccs
			) else *) (
				comment (puts "	SCC {" << Abbrev.put_ints " #" scc << puts " }" << endl <<
					puts "Removing DPs: " << flush
				);
				cpf (MyXML.enclose_inline "realScc" (puts "true"));
				if List.for_all (fun i -> (dg#find_dp i)#is_weak) scc then (
					comment (puts "only weak rules." << endl);
					cpf (
						MyXML.enclose "acDPTerminationProof" (MyXML.tag "acTrivialProc") <<
						MyXML.leave "component"
					);
					loop (n_sccs - 1) sccs
				) else (
					cpf (MyXML.enter "acDPTerminationProof");
					match remove_strict scc with
					| Some rest ->
						let subsccs = dg#get_subsccs rest in
						let subsccs = scc_sorter subsccs in
						let n_sccs = n_sccs - 1 + List.length subsccs in
						let ret = dg_proc n_sccs subsccs in
						cpf (
							MyXML.leave "acRedPairProc" <<
							MyXML.leave "acDPTerminationProof" <<
							MyXML.leave "component"
						);
						if ret = YES then loop_silent n_sccs sccs else ret
					| None ->
						comment (puts "failed." << endl);
						loop_edges n_sccs (scc::sccs)
				)
			)
	and loop_edges n_sccs = function
		| [] -> YES
		| scc::sccs ->
			comment (puts "Removing edges: " << flush);
			if remove_edges scc then
				let subsccs = dg#get_subsccs scc in
				if (match subsccs with [scc'] -> List.(length scc' = length scc) | _ -> false) then
					loop_edges n_sccs (scc::sccs)
				else
					let subsccs = scc_sorter subsccs in
					let n_sccs = n_sccs - 1 + List.length subsccs in
					let ret = dg_proc n_sccs subsccs in
					if ret = YES then loop_silent n_sccs sccs else ret
			else (
				comment (puts "failed." << endl);
				Nonterm.find_loop params.max_loop trs estimator dg scc;
				cpf (
					MyXML.enclose "unknownProof" (MyXML.enclose "description" (puts "Failed!")) <<
					MyXML.leave "acDPTerminationProof" <<
					MyXML.leave "component"
				);
				MAYBE
			)
	in
	let ret = dg_proc (List.length sccs) sccs in
	if ret = YES && dg#next then (
		problem (puts "Next Dependency Pairs:" << endl << dg#output_dps);
		let sccs = dg#get_sccs in
		remove_unusable trs estimator dg sccs;
		dg_proc (List.length sccs) sccs
	) else ret;;


let dp_prove (trs : #trs) =
	if trs#is_probabilistic then begin
		comment (puts "DP for a probabilistic system" << endl);
		raise Unknown;
	end;
	(* Test for variable left-hand sides *)
	let iterer _ lr =
		let rt = root lr#l in
		if rt#is_var then
			if lr#is_strict then begin
				comment (puts "variable left-hand side" << endl);
				raise Nonterm
			end else begin
				comment (puts "weak variable left-hand side" << endl);
				raise Unknown
			end
		else ()
	in
	trs#iter_rules iterer;
	let estimator =
		match params.edge_mode with
		| E_tcap -> Estimator.tcap trs
		| _ -> Estimator.sym_trans trs
	in
	debug estimator#output;

	cpf (MyXML.enter "acDependencyPairs");
(*	cpf (MyXML.enclose "markedSymbols" (fun os -> output_string os "true");
*)	let dg = new dg trs estimator in
	dg#init;
	cpf (
		MyXML.enclose "equations" (
			MyXML.enclose "rules" (fun pr ->
				trs#iter_rules (fun _ rule -> if rule#is_weak then rule#output_xml pr;)
			)
		) <<
		MyXML.enclose "dpEquations" (
			MyXML.enclose "rules" (fun pr ->
				dg#iter_dps (fun _ dp -> if dp#is_weak then dp#output_xml pr;)
			)
		) <<
		MyXML.enclose "dps" (
			MyXML.enclose "rules" (fun pr ->
				dg#iter_dps (fun _ dp -> if dp#is_strict then dp#output_xml pr;)
			)
		) <<
		MyXML.enclose "extensions" (
			MyXML.enclose "rules" (fun (pr:#printer) ->
				let iterer i (rule:rule) =
					if rule#is_strict && trs#weakly_defines (root rule#l) then begin
						List.iter (fun (rule:#rule) -> rule#output_xml pr) (extended_rules rule);
					end;
				in
				trs#iter_rules iterer;
			)
		)
	);
	problem (puts "Dependency Pairs:" << endl << dg#output_dps);
	log dg#output_edges;
	log (dg#output_debug << endl);

	let ret = dp_remove trs estimator dg in
	cpf (MyXML.leave "acDependencyPairs");
	ret;;


let prove_termination (trs : #trs) =
	problem (puts "Input TRS:" << endl << enter 4 << trs#output << leave 4);
	cpf (
		MyXML.enclose_inline "cpfVersion" (puts "2.2") <<
		MyXML.enter "proof" <<
		MyXML.enter "acTerminationProof"
	);

	let ret =
		try
			theory_test trs;
			extra_test trs;
			trivial_test trs;
			rule_remove trs (fun trs ->
				if freeze trs dummy_dg then
					rule_remove trs dp_prove
				else if params.dp then
					dp_prove trs
				else raise Unknown
			)
		with
		| Success -> YES
		| Unknown -> MAYBE
		| Nonterm -> NO
	in
	cpf (
		MyXML.leave "acTerminationProof" <<
		MyXML.leave "proof" <<
		MyXML.enclose "origin" (
			MyXML.enclose "proofOrigin" (
				MyXML.enclose "tool" (
					MyXML.enclose_inline "name" (puts "NaTT") <<
					MyXML.enclose_inline "version" (puts version)
				)
			)
		)
	);
	ret
;;

class main =
	let err msg = prerr_endline ("Error: " ^ msg ^ "!"); exit 1 in
	let warn msg = warning(fun _ -> prerr_endline ("Warning: " ^ msg ^ ".")) in
object (x)
	val trs = new trs

	method no_ac = not(StrSet.mem "AC" trs#get_ths)

	method duplicating = trs#exists_rule (fun _ rule -> rule#is_duplicating)

	method conditional = trs#exists_rule (fun _ rule -> rule#is_conditional)

	method run =
		let prob = Txtr.parse_in (Trs.problem_xml trs) (if params.file = "" then stdin else Stdlib.open_in params.file) in
		begin match params.mode, prob with
		| MODE_default, Some mode -> params.mode <- mode
		| _ -> ()
		end;
		cpf (
			puts "<?xml version=\"1.0\"?>" << endl <<
			puts "<?xml-stylesheet type=\"text/xsl\" href=\"cpfHTML.xsl\"?>" <<
			MyXML.enter "certificationProblem xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:noNamespaceSchemaLocation=\"cpf.xsd\""
		);

		begin match params.mode with
		| MODE_higher_xml ->
			trs#output_xml_ho cout;
		| MODE_through ->
				trs#output cout;
								| MODE_xml -> trs#output_xml cout;
		| MODE_flat ->
			trs#iter_rules (fun i rule -> trs#replace_rule i (map_rule flat rule));
			trs#output cout;
		| MODE_freezing ->
			ignore (Freezing.auto_freeze trs (new dg (new trs) (Estimator.tcap (new trs))));
			trs#output cout;
		| MODE_simple ->
			if trs#exists_rule (fun _ rule -> emb_le rule#l rule#r) then
				err "Not simple";
		| MODE_dup	->
			if x#duplicating then err "Duplicating";
			warn "Non-duplicating";
			exit 0;
		| MODE_cond ->
			if x#conditional then err "Conditional";
			warn "Unconditional";
			exit 0;
		| MODE_infeasibility eqs ->
			problem (puts "Input TRS:" << endl << enter 4 << trs#output << leave 4);
			problem (puts "Infeasibility test:" << endl <<
				put_list (fun (s,t) -> puts "    " << put_term s << puts " --> " << put_term t) endl nop eqs << endl);
			let (ss,ts) = List.split eqs in
			let c = new Sym.sym_unmarked Fun " #" in
			(trs#get_sym c)#set_arity (List.length ss);
			let s = Node(c,ss) in
			let t = Node(c,ts) in
			if params.nonreach_estimator && (
				let estimator = Estimator.sym_trans trs in
				not (estimator#may_reach s t) && (
					proof (estimator#output);
					true
				)
			) || (
				let tester p =
					(new Wpo.t p trs dummy_estimator dummy_dg)#co_order t s
				in
				Array.exists tester params.orders_nonreach
			) then begin
				print_endline "YES";
			end else begin
				comment (puts "failed." << endl);
				print_endline "MAYBE";
			end;
		| _ ->
			Array.iter
				(fun p ->
					if nonmonotone p then
						err "Rule removal processor must be monotone";
				) params.orders_rule;
			let ans = prove_termination trs in
				cpf (MyXML.leave "certificationProblem" << endl);
			if params.result then
				print_endline
				(	match ans with
					| YES	-> "YES"
					| NO	-> "NO"
					| MAYBE	-> "MAYBE"
				);
		end;
end;;

begin
	try
		(new main)#run;
		exit 0;
	with
	| Unsound s ->
		prerr_newline ();
		prerr_string "Unsound: ";
		prerr_endline s;
	| Proc.Dead cmd ->
		prerr_newline ();
		prerr_string "Proccess '";
		prerr_string cmd;
		prerr_endline "' is dead!";
	| Smt.Internal s ->
		prerr_newline ();
		prerr_string "SMT error: ";
		prerr_endline s;
	| Smt.Invalid_formula(m,e) ->
		(endl << puts "Invalid formula: " << puts m << puts ": ") cerr;
		Smt.prerr_exp e;
		cerr#endl;
	| Smt.Response(s,e) ->
		prerr_newline ();
		prerr_string "Unexpected SMT solver response to '";
		prerr_string s;
		prerr_endline "':";
		Smt.prerr_exp e;
		prerr_newline ();
	| No_support(s) ->
		prerr_newline ();
		prerr_string "Not supported: ";
		prerr_endline s;
end;
print_endline "ERR";
exit 1;

