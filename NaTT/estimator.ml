open Util
open Sym
open Term
open Trs
open Params
open Io

type 'a connects_formula =
	| False
	| Connects of ('a * 'a) list

let connects_and a b =
	match a, b with
	| False, _ -> a
	| _, False -> b
	| Connects aa, Connects bb -> Connects (aa@bb)

(* symbol transition graph *)
module SymG = Graph.Imperative.Digraph.Concrete(Hashed(String))
module SymGoper = Graph.Oper.I(SymG)

let output_path path os =
	os#puts "< ";
	List.iter (fun i -> os#put_int i; os#puts " ";) path;
	os#puts "> ";;

let output_path_to s path t (c, (u:#sym Subst.t)) os =
	output_term os s;
	output_path path os;
	output_term os t;
	os#puts "?  ";
	u#output os;;

class virtual t (trs:#trs) = object (x)

	val mutable vcounter = 0

	method virtual may_reach_0 : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool

	method may_connect_n : 'a 'b. int -> (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun n (Node(f,ss)) (Node(g,ts)) ->
			match f#ty with
			| Var -> true
			| Fun -> f#equals g && List.for_all2 (x#may_reach_n n) ss ts
			| Th "C" -> f#equals g &&
				(	match ss, ts with
					| [s1;s2], [t1;t2] ->
						(x#may_reach_n n s1 t1 && x#may_reach_n n s2 t2) ||
						(x#may_reach_n n s1 t2 && x#may_reach_n n s2 t1)
					| _ -> raise (No_support "nonbinary commutative symbol")
				)
			| _ -> f#equals g

	method may_reach_n : 'a 'b. int -> (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun n (Node(f,ss) as s) t ->
			f#is_var ||
			(root t)#is_var ||
			x#may_reach_0 s t &&
			( n = 0 || x#may_connect_n n s t ||
				let tester i =
					let rule = trs#find_rule i in
					let Node(_,ls) = rule#l in
					List.for_all2 (x#may_reach_n n) ss ls &&
					x#may_reach_n (n-1) rule#r t
				in
				let f = trs#find_sym f in
				Rules.exists tester f#weakly_defined_by ||
				Rules.exists tester f#defined_by
			)

	method may_connect : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun s t -> x#may_connect_n params.edge_length s t

	method may_reach : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
		fun s t -> x#may_reach_n params.edge_length s t

	method find_matchable :
	'a. (#sym as 'a) term -> Rules.elt list = fun s ->
		let f = trs#find_sym (root s) in
		let folder i ret =
			if x#may_connect_n 0 s (trs#find_rule i)#l then i::ret else ret
		in
		Rules.fold folder f#weakly_defined_by
		(Rules.fold folder f#defined_by [])

	method instantiate_path_sub :
		int -> sym term list -> sym term list -> (int * sym Subst.t) list =
		fun lim ss ts ->
			match ss, ts with
			| [], [] -> [(0, new Subst.t)]
			| s::ss, t::ts ->
				let cus = x#instantiate_path_sub lim ss ts in
				let folder (c,u) ret =
					let s = u#subst s in
					let t = u#subst t in
					let st = x#instantiate_path (lim-c) s t in
					List.map (cu_append (c,u)) st @ ret
				in
				List.fold_right folder cus []
			| _ -> assert false

	method instantiate_path :
	'a. int -> sym term -> sym term -> (int * sym Subst.t) list =
	fun lim (Node(f,ss) as s) (Node(g,ts) as t) ->
		debug2 ( endl << puts "& " << put_term s << puts " --> " << put_term t );
		if term_eq s t then [(0, new Subst.t)]
		else if not (x#may_reach s t) then []
		else if f#is_var then
			if VarSet.mem f#name (varset t) then [] else [(0, Subst.singleton f t)]
		else if g#is_var then
			if VarSet.mem g#name (varset s) then [] else [(0, Subst.singleton g s)]
		else
		let init =
			debug2( puts "?" << enter 1;);
			if f#equals g then (
				debug2 (endl << puts "| Inner:" << enter 1);
				let init = x#instantiate_path_sub lim ss ts in
				debug2 (leave 1);
				init
			) else []
		in
		if lim = 0 then (
			debug2 (puts "exceeded limit");
			init
		)
		else
			let folder ret i =
				let v = "i" ^ string_of_int vcounter in
				vcounter <- vcounter + 1;
				let rule = trs#find_rule i in
				debug2 (endl << enter 1 << puts "| Rewrite: " << rule#output << puts " ?");
				let l = Subst.vrename v rule#l in
				let r = Subst.vrename v rule#r in
				match Subst.unify s l with
				| Some u ->
					let s' = u#subst r in
					let t' = u#subst t in
					let rest = x#instantiate_path (lim-1) s' t' in
					debug2 (leave 1);
					List.map (cu_append (1,u)) rest @ ret
				| None ->
					debug2 ( puts " ... failed" << leave 1);
					ret
			in
			let ret = List.fold_left folder init (x#find_matchable s) in
			debug2 (leave 1);
(*			debug2 (fun os -> List.iter (fun (c,(u:#sym Subst.t)) -> os#endl; u#output os;) ret);
*)			ret

	method output : 'a. (#Io.printer as 'a) -> unit = fun os -> ()
end;;

let tcap (trs:#trs) : t = object (x)
	inherit t trs
	method may_reach_0 : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
	fun s t -> true
end;;

let sym_trans (trs:#trs) : t =
	let collapsable = ref [] in
	let sym_g = SymG.create () in
	let () =
		SymG.add_vertex sym_g  ""; (* this vertex represents arbitrary symbol *)
		let add_sym f =
			if f#is_fun then begin
				SymG.add_vertex sym_g f#name;
				SymG.add_edge sym_g "" f#name;
			end;
		in
		trs#iter_syms add_sym;
		let add_edge _ rule =
			let f = root rule#l in
			let g = root rule#r in
			if g#is_var then begin
				collapsable := f :: !collapsable;
				SymG.add_edge sym_g f#name "";
			end else begin
				SymG.add_edge sym_g f#name g#name;
			end;
		in
		trs#iter_rules add_edge;
		ignore (SymGoper.add_transitive_closure sym_g);
		SymG.remove_vertex sym_g ""; (* Remove the temporal vertex *)
	in
	let trans_sym : #sym -> #sym -> bool = fun f g ->
		f#equals g || SymG.mem_edge sym_g f#name g#name
	in
	object (x)
		inherit t trs
		method may_reach_0 : 'a 'b. (#sym as 'a) term -> (#sym as 'b) term -> bool =
			fun (Node(f,_)) (Node(g,_)) -> trans_sym f g
		method output : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "Symbol transition graph:";
			pr#enter 4;
			let iterer (f:#sym_detailed) =
				if f#is_defined then begin
					let succ = SymG.succ sym_g f#name in
					pr#endl;
					f#output pr;
					pr#puts "\t-->";
					List.iter (fun gname -> pr#putc ' '; pr#puts gname;) succ;
				end;
			in
			trs#iter_syms iterer;
			pr#leave 2;
			pr#endl;
			pr#puts "Collapsable symbols: {";
			List.iter (fun (f : #sym) -> pr#putc ' '; f#output pr;) !collapsable;
			pr#puts " }";
			pr#leave 2;
			pr#endl;
	end;;

