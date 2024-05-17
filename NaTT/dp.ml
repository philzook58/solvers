open Util
open Sym
open Term
open Trs
open Params
open Io

let mark_root (Node((f:#sym),ss)) = Node(mark_sym f, ss)

let guard_term (Node(f,ss) as s) = Node(new sym_marked Fun f#name, [s])

let mark_term_ac =
	match params.ac_mark_mode with
	| AC_unmark -> fun x -> x
	| AC_mark -> mark_root
	| AC_guard -> guard_term

let mark_term (Node(f,ss) as s) =
	if f#is_theoried then mark_term_ac s else mark_root s

(* Adding marked symbols *)

let add_marked_symbol_default (trs : #trs) f =
	let f' = trs#get_sym (mark_sym f) in
	f'#set_arity f#arity;;

let add_marked_symbol_ac =
	match params.ac_mark_mode with
	| AC_unmark -> fun _ _ -> ()
	| AC_mark -> add_marked_symbol_default
	| AC_guard -> fun trs f ->
		let f' = trs#get_sym (new sym_marked f#ty f#name) in
		f'#set_arity 1;;

let add_marked_symbols (trs : #trs) =
	let iterer f =
		if f#is_defined then begin
			if f#ty = Fun then begin
				add_marked_symbol_default trs f;
			end else begin
				add_marked_symbol_ac trs f;
			end;
		end;
	in
	trs#iter_syms iterer;;



(* For the new AC-DP *)
let add_marked_symbols_ac trs =
	let iterer f =
		if f#ty <> Fun && f#is_defined then begin
			add_marked_symbol_ac trs f;
		end;
	in
	trs#iter_syms iterer;;




module DG = Graph.Imperative.Digraph.Concrete(Hashed(Int))
module Components = Graph.Components.Make(DG)
module Topological = Graph.Topological.Make(DG)

module SubDG = struct
	type t = DG.t * IntSet.t
	module V = Hashed(Int)
	let iter_vertex f (g,vs) = IntSet.iter f vs
	let iter_succ f (g,vs) = DG.iter_succ (fun v2 -> if IntSet.mem v2 vs then f v2) g
	let fold_succ f (g,vs) v a =
		DG.fold_succ (fun v2 b -> if IntSet.mem v2 vs then f v2 b else b) g v a
end

module SubComponents = Graph.Components.Make(SubDG)


class dg (trs : trs) (estimator : Estimator.t) =
	(* list of lists to list of sets *)
	object (x)
		val mutable minimal = true
		val dp_table = Hashtbl.create 256
		val dg = DG.create ()
		val mutable dp_cnt = 0
		val mutable edge_all = 0
		val mutable edge_real = 0
		val mutable need_extended_rules =
			trs#is_theoried && params.acdp_mode = ACDP_new

		method add_dp dp =
			dp_cnt <- dp_cnt + 1;
			Hashtbl.add dp_table dp_cnt dp;

		(* Generate dependency pairs *)
		method generate_dp =
			let rec generate_dp_sub strength s conds (Node(g,ts) as t) =
				if (trs#strictly_defines g || g#is_theoried) && not (strict_subterm t s) then begin
					x#add_dp (new rule strength s (mark_term t) conds);
				end;
				List.iter (generate_dp_sub strength s conds) ts;
			in
			let generate_dp_default rule =
				generate_dp_sub rule#strength (mark_term rule#l) rule#conds rule#r
			in
			match params.acdp_mode with
			| ACDP_union -> fun rule ->
				generate_dp_default rule;
				if (root rule#l)#is_theoried &&
					rule#is_strict (* the weak rule itself don't have to be extended *)
				then begin
					List.iter (fun xrule -> x#add_dp (map_rule mark_term xrule)) (extended_rules rule);
				end;
			| _ -> generate_dp_default

		method init =
			(* Relative: Moving duplicating or non-dominant weak rules to *medium* rules *)
			while trs#fold_rules (fun i rule ret ->
					if rule#is_weak &&
						(rule#is_duplicating || not(trs#relative_const rule#r)) then (
						trs#replace_rule i (medium_rule rule#l rule#r);
						true)
					else ret
				) false
			do () done;
			(* minimality can be assumed if all weak rules are size preserving *)
			let tester i rule =
				rule#is_weak && rule#is_size_increasing && (
					log (puts "Detected size-increasing weak rule " << put_int i <<
						puts ". Disabling minimality." << endl
					); true)
			in
			if trs#exists_rule tester then begin
				minimal <- false;
			end;
			if trs#is_theoried then begin
				(* turn AC theory into weak rules *)
				trs#th_to_rules;
			end;
			(* Main process *)
			add_marked_symbols trs;
			let iterer i rule = x#generate_dp rule in
			trs#iter_rules iterer;
			x#make_dg;

(* Estimated dependency graph *)

		method private make_dg =
			let edged (src : rule) (tgt : rule) =
				(root src#r)#equals (root tgt#l) && (edge_all <- edge_all + 1; true) &&
				estimator#may_connect src#r tgt#l && (edge_real <- edge_real + 1; true)
			in
			Hashtbl.iter (fun i _ -> DG.add_vertex dg i) dp_table;
			Hashtbl.iter (
				fun i1 dp1 ->
				Hashtbl.iter
					(fun i2 dp2 -> if edged dp1 dp2 then DG.add_edge dg i1 i2)
					dp_table
			) dp_table;

		method private make_ac_ext =
			x#iter_dps (fun i _ -> x#remove_dp i);
			let iterer i rule =
				if (root rule#l)#is_theoried then begin
					if rule#is_strict then begin
						let iterer xrule = x#add_dp (map_rule mark_term xrule) in
						List.iter iterer (extended_rules rule);
					end else begin
						x#generate_dp rule;
					end;
				end;
			in
			trs#iter_rules iterer;
			x#make_dg;

		method next = (* if there is a next problem, then init it and say true *)
			need_extended_rules && (
				x#make_ac_ext;
				need_extended_rules <- false;
				true
			)
		method minimal = minimal
		method get_subdg scc = (dg, IntSet.of_list scc)
		method private trim_sccs f =
			List.filter (function
			| [i] when not (x#edged i i) ->
				x#remove_dp i; (* remove trivial SCC *)
				false
			| scc ->
				List.iter (fun i ->
					let fi = f i in
					DG.iter_succ (fun j ->
						if fi <> f j then x#remove_edge i j
					) dg i
				) scc;
				true
			)
		method get_sccs =
			let (n,f) = Components.scc dg in
			let sccs = Components.scc_list dg in
			x#trim_sccs f sccs
		method get_subsccs dps =
			let subdg = (dg, IntSet.of_list dps) in
			let (n,f) = SubComponents.scc subdg in
			let sccs = SubComponents.scc_list subdg in
			x#trim_sccs f sccs
		method count_dps = Hashtbl.length dp_table
		method find_dp = Hashtbl.find dp_table
		method get_dp_size i = let dp = x#find_dp i in dp#size
		method iter_dps f = Hashtbl.iter f dp_table
		method get_dps = Hashtbl.fold (fun i dp dps -> (i,dp)::dps) dp_table []
		method remove_dp i = DG.remove_vertex dg i; Hashtbl.remove dp_table i;
		method replace_dp i dp = Hashtbl.replace dp_table i dp;
		method count_edges = DG.nb_edges dg
		method edged = DG.mem_edge dg
		method remove_edge = DG.remove_edge dg
		method succ = DG.succ dg
		method iter_succ f = DG.iter_succ f dg
		method output_dp : 'a. int -> (#Io.printer as 'a) -> unit = fun i pr ->
			print_tbl_index pr "   #" (i, x#find_dp i)
		method output_dp_xml : 'a. int -> (#Io.printer as 'a) -> unit = fun i ->
			(x#find_dp i)#output_xml
		method output_dps : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			print_tbl pr "   #" dp_table
		method output_dps_xml : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			x#iter_dps (fun _ rule -> rule#output_xml pr)
		method output_scc_xml : 'a. int list -> (#Io.printer as 'a) -> unit = fun scc pr ->
			List.iter (fun i -> x#output_dp_xml i pr) scc
		method iter_edges f = DG.iter_edges f dg
		method output_edges : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "Edges:";
			pr#enter 2;
			let iterer i _ =
				let succ = DG.succ dg i in
				if succ <> [] then begin
					pr#endl;
					pr#putc '#';
					pr#put_int i;
					pr#puts " -->";
					Abbrev.put_ints " #" succ pr;
				end;
			in
			x#iter_dps iterer;
			pr#leave 2;
			pr#endl;
		method output_debug : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "  trivial edges: ";
			pr#put_int edge_all;
			pr#puts ", removed: ";
			pr#put_int (edge_all - edge_real);
	end;;
