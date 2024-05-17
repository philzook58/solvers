open Util
open Sym
open Term
open Subst
open Io
open Txtr
open Params

type arity = Unknown | Arity of int

exception ExistsConditionalRule
exception ExistsEquation
exception UnknownTheory
exception UnknownStrategy
exception UnknownProperty
exception SymbolMissmatch;;

module Ths = StrSet
module Syms = StrSet
module Rules = IntSet

class sym_detailed (f : sym) =
	object (x:'a)
		inherit sym f#ty
		method name = f#name
		method output_xml = f#output_xml
		val mutable arity = if f#is_var then Arity 0 else Unknown
		val mutable defined_by = Rules.empty
		val mutable weakly_defined_by = Rules.empty
		val mutable p_defined_by = Rules.empty
		method original = f
		method arity_is_unknown = arity = Unknown
		method set_arity a = arity <- Arity a
		method set_theory th = ty <- Th th
		method arity =
			match arity with
			| Arity a -> a
			| _ -> raise (No_support ("arity for " ^ f#name ^ " is unknown"))
		method defined_by = defined_by
		method define_by i = defined_by <- Rules.add i defined_by
		method undefine_by i = defined_by <- Rules.remove i defined_by
		method is_defined = not (Rules.is_empty defined_by)
		method weakly_defined_by = weakly_defined_by
		method weakly_define_by i = weakly_defined_by <- Rules.add i weakly_defined_by
		method weakly_undefine_by i = weakly_defined_by <- Rules.remove i weakly_defined_by
		method is_weakly_defined = x#is_defined || not (Rules.is_empty weakly_defined_by)
		method p_defined_by = p_defined_by
		method p_define_by i = p_defined_by <- Rules.add i p_defined_by
		method p_undefine_by i = p_defined_by <- Rules.remove i p_defined_by
		method is_p_defined = not (Rules.is_empty p_defined_by)
		method is_const = not x#is_weakly_defined && not x#is_p_defined
	end;;

let print_tbl_index (pr : #Io.printer as 'a) prefix (i, (obj: #printable)) =
	pr#puts prefix;
	pr#put_int i;
	pr#puts ": ";
	obj#print pr;
	pr#endl;;

let print_tbl (pr : #Io.printer) prefix ruletbl =
	List.iter (print_tbl_index pr prefix)
	(List.sort (fun (i,_) (j,_) -> i - j) (Hashtbl.fold (fun i obj l -> (i,obj)::l) ruletbl []))

let hashtbl_exists test hashtbl =
	try
		Hashtbl.iter (fun l v -> if test l v then raise Success;) hashtbl;
		false
	with Success -> true

let hashtbl_for_all test hashtbl =
	try
		Hashtbl.iter (fun l v -> if not (test l v) then raise Success;) hashtbl;
		true
	with Success -> false


(* the class for TRSs *)
class trs =
	object (x)
		val sym_table = Hashtbl.create 64(* the symbol table *)
		val rule_table : (int, rule) Hashtbl.t = Hashtbl.create 256
		val prule_table : (int, prule) Hashtbl.t = Hashtbl.create 4
		val mutable fun_cnt = 0
		val mutable rule_cnt = 0
		val mutable strict_rule_cnt = 0
		val mutable prule_cnt = 0
		val mutable ths = Ths.empty(* the set of used built-in theories *)
(* information retrieval *)
		method get_fun_count = fun_cnt
		method get_size = rule_cnt + prule_cnt
		method get_size_strict = strict_rule_cnt + prule_cnt
		method get_ths = ths
		method is_theoried = not (Ths.is_empty ths)
		method is_probabilistic = prule_cnt > 0
(* methods for symbols *)
		method private add_sym : 'b. (#sym as 'b) -> sym_detailed =
			fun f ->
				let f' = new sym_detailed (f:>sym) in
				Hashtbl.add sym_table f#name f';
				(match f#ty with
				| Var -> f'#set_arity 0
				| Fun -> fun_cnt <- fun_cnt + 1;
				| Th th -> ths <- Ths.add th ths; fun_cnt <- fun_cnt + 1;);
				f'
		method get_sym_name name cls =
			try Hashtbl.find sym_table name
			with Not_found -> x#add_sym (new sym_unmarked cls name)
		method find_sym_name name =
			try Hashtbl.find sym_table name
			with Not_found -> new sym_detailed (new sym_unmarked Fun name)
		method get_sym : 'b. (#sym as 'b) -> sym_detailed =
			fun f ->
				if f#is_var then new sym_detailed (f:>sym) else
				try Hashtbl.find sym_table f#name with Not_found -> x#add_sym f
		method find_sym : 'b. (#sym as 'b) -> sym_detailed =
			fun f ->
				try Hashtbl.find sym_table f#name with Not_found -> new sym_detailed (f:>sym)
		method set_theory fname th =
			ths <- Ths.add th ths;
			(x#find_sym_name fname)#set_theory th;
		method iter_syms : (sym_detailed -> unit) -> unit =
			fun iterer -> Hashtbl.iter (fun _ f -> iterer f) sym_table
		method iter_funs : (sym_detailed -> unit) -> unit =
			fun iterer -> Hashtbl.iter (fun _ f -> if f#is_fun then iterer f) sym_table
		method fold_syms : 'b. (sym_detailed -> 'b -> 'b) -> 'b -> 'b =
			fun folder acc ->
				Hashtbl.fold (fun _ -> folder) sym_table acc
		method strictly_defines_name name =
			try not (Rules.is_empty (Hashtbl.find sym_table name)#defined_by)
			with Not_found -> false
		method strictly_defines : 'b. (#sym as 'b) -> bool =
			fun f -> f#is_fun && x#strictly_defines_name f#name
		method defines : 'b. (#sym as 'b) -> bool =
			fun f ->
				f#is_fun &&
				try let f = Hashtbl.find sym_table f#name in
					f#is_defined || f#is_weakly_defined
				with Not_found -> false
		method weakly_defines : 'b. (#sym as 'b) -> bool =
			fun f ->
				f#is_fun &&
				try let f = Hashtbl.find sym_table f#name in
				f#is_weakly_defined
				with Not_found -> false
(* test for constructor terms *)
		method const_term : 'b. (#sym as 'b) term -> bool =
			fun (Node(f,ss)) ->
				not (x#defines f) && List.for_all x#const_term ss
		method relative_const : 'b. (#sym as 'b) term -> bool =
			fun (Node(f,ss)) ->
				not (x#strictly_defines f) && List.for_all x#relative_const ss

(* methods for rules *)
		method find_rule = Hashtbl.find rule_table
		method iter_rules f = Hashtbl.iter f rule_table
		method for_all_rules f = hashtbl_for_all f rule_table
		method exists_rule f = hashtbl_exists f rule_table
		method fold_rules : 'b. (int -> rule -> 'b -> 'b) -> 'b -> 'b =
			fun f a -> Hashtbl.fold f rule_table a
		method private add_rule_i i rule =
			let f = x#get_sym (root rule#l) in
			Hashtbl.add rule_table i rule;
			if rule#is_weak then begin
				f#weakly_define_by i;
			end else begin
				f#define_by i;
				strict_rule_cnt <- strict_rule_cnt + 1;
			end;
		method add_rule rule =
			rule_cnt <- rule_cnt + 1;
			x#add_rule_i rule_cnt rule;
		method remove_rule i =
			let rule = x#find_rule i in
			let f = x#get_sym (root rule#l) in
			if rule#is_weak then begin
				f#weakly_undefine_by i;
			end else begin
				f#undefine_by i;
				strict_rule_cnt <- strict_rule_cnt - 1;
			end;
			Hashtbl.remove rule_table i;
		method replace_rule i rule =
			x#remove_rule i;
			x#add_rule_i i rule;

(* theory to rules *)
		method th_to_rules =
			let v1 = var "x" in
			let v2 = var "y" in
			let v3 = var "z" in
			let iterer (f:sym_detailed) =
				if f#is_associative then begin
					let l = app f [v1; app f [v2;v3]] in
					let r = app f [app f [v1;v2]; v3] in
					x#add_rule (weak_rule l r);
					if f#is_commutative then begin
						if Params.(params.naive_C) then begin
							x#add_rule (weak_rule (app f [v1;v2]) (app f [v2;v1]));
						end;
					end else begin
						x#add_rule (weak_rule r l);
					end;
				end else if Params.(params.naive_C) && f#is_commutative then begin
					x#add_rule (weak_rule (app f [v1;v2]) (app f [v2;v1]));
				end;
			in
			x#iter_syms iterer;

(* probabilistic rules *)
		method find_prule = Hashtbl.find prule_table
		method iter_prules f = Hashtbl.iter f prule_table
		method for_all_prules f = hashtbl_for_all f prule_table
		method exists_prule f = hashtbl_exists f prule_table
		method fold_prules : 'b. (int -> prule -> 'b -> 'b) -> 'b -> 'b =
			fun f a -> Hashtbl.fold f prule_table a
		method private add_prule_i i prule =
			let f = x#get_sym (root prule#l) in
			Hashtbl.add prule_table i prule;
			f#p_define_by i;
			prule_cnt <- prule_cnt + 1;
		method add_prule prule =
			x#add_prule_i prule_cnt prule;
		method remove_prule i =
			let prule = x#find_prule i in
			let f = x#get_sym (root prule#l) in
			f#p_undefine_by i;
			prule_cnt <- prule_cnt - 1;
			Hashtbl.remove prule_table i;
		method replace_prule i prule =
			x#remove_prule i;
			x#add_prule_i i prule;
		method modify_prule i l d =
			x#replace_prule i (new prule l d)



(* input *)

		method term_element xmls = (
			element "sym" (
				string >>= fun fname ->
				let f = x#get_sym_name fname Fun in
				if f#arity_is_unknown then f#set_arity 0
				else if f#arity <> 0 then
					raise (No_support (string_of_int f#arity ^ "-ary symbol " ^ fname ^ " appeared unapplied"));
				return (Node((f:>sym),[]))
			) <|>
			element "app" (
				element "sym" string >>= fun fname ->
				many x#term_element >>= fun ss ->
				let f = x#get_sym_name fname Fun in
				let n = List.length ss in
				if f#arity_is_unknown then f#set_arity n
				else if f#arity <> n then
					raise (No_support (string_of_int f#arity ^ "-ary symbol "^fname^" is applied to " ^ string_of_int n ^ " arguments"));
				return (Node((f:>sym),ss))
			)
		) xmls
		method input_sym_decl =
			element "fun" (
				attribute "theory" >>= fun th ->
				string >>= fun name ->
				if th = "AC" || th = "A" || th = "C" then
				(x#add_sym (new sym_unmarked (Th th) name))#set_arity 2 else raise (No_support ("unknown theory " ^ th));
				return ()
			) <|>
			element "var" (
				string >>= fun s ->
				ignore (x#add_sym (new sym_unmarked Var s));
				return ()
			)
		method input_rule =
			element "rule" (
				x#term_element >>= fun l -> (
					x#term_element >>= fun r ->
					many (
						element "cond" (
							x#term_element >>= fun s ->
							x#term_element >>= fun t ->
							return (s,t)
						)
					) >>= fun conds ->
					x#add_rule (crule l r conds);
					return ()
				) <|> (
					many (
						element "distrib" (
							default 1 (int_attribute "w") >>= fun w ->
							x#term_element >>= fun r ->
							return (w,r)
						)
					) >>= fun wrs ->
					x#add_prule (new prule l wrs);
					return ()
				)
			) <|>
			element "relative" (
				x#term_element >>= fun l ->
				x#term_element >>= fun r ->
				x#add_rule (weak_rule l r);
				return ()
			)

		method term_xtc xmls = (
			element "funapp" (
				element "name" string >>= fun fname ->
				many (element "arg" x#term_xtc) >>= fun ss ->
				let f = x#get_sym_name fname Fun in
				if f#arity_is_unknown then f#set_arity (List.length ss);
				return (Node((f:>sym),ss))
			) <|>
			element "var" (
				string >>= fun vname ->
				let v = x#get_sym_name vname Var in
				if not v#is_var then raise (No_support ("function " ^ vname ^ " occured as a variable"));
				return (Node((v :> sym), []))
			)
		) xmls
		method rule_xtc =
			element "rule" (
				element "lhs" x#term_xtc >>= fun l ->
				element "rhs" x#term_xtc >>= fun r ->
				return (l,r)
			)
		method input_rules_xtc =
			element "rules" (
				many (
					x#rule_xtc >>= fun (l,r) ->
					x#add_rule (rule l r);
					return ()
				) >>= fun _ ->
				optional (
					element "relrules" (
						many (
							x#rule_xtc >>= fun (l,r) ->
							x#add_rule (weak_rule l r);
							return ()
						)
					)
				)
			)
(* counting nests *)
		val mutable nest_map = Mset.empty
		method count_nest =
			let rec nest_term (Node(f,ss)) =
				if f#is_var then
					Mset.empty
				else
					Mset.union (Mset.singleton f#name)
						(List.fold_left Mset.join Mset.empty (List.map nest_term ss))
			in
			let nest_rule rule = Mset.join (nest_term rule#l) (nest_term rule#r) in
			nest_map <-
				x#fold_rules
					(fun i rule acc -> Mset.join (nest_rule rule) acc)
					Mset.empty
		method nest_of : string -> int
		= fun fname -> Mset.count fname nest_map

(* outputs *)
		method output_ths : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			let iterer_th th =
				pr#puts th;
				pr#puts " symbols:";
				let iterer_syms (f:#sym) =
					if f#ty = Th th then begin
						pr#putc ' ';
						f#output pr;
					end;
				in
				x#iter_syms iterer_syms;
				pr#endl;
			in
			Ths.iter iterer_th ths;
		method output_rules : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			print_tbl pr "" rule_table;
			print_tbl pr "p" prule_table;
		method output_last_rule : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			print_tbl_index pr "	 " (rule_cnt, Hashtbl.find rule_table rule_cnt);
		method output : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			x#output_ths pr;
			x#output_rules pr;
		method output_wst : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			pr#puts "(VAR";
			let iterer_var (v : #sym) =
				if v#is_var then begin
					pr#putc ' ';
					v#output pr;
				end
			in
			x#iter_syms iterer_var;
			pr#putc ')';
			pr#endl;
			pr#puts "(RULES";
			pr#enter 4;
			let iterer_rule _ (rule : #rule) =
				pr#endl;
				rule#output pr;
			in
			x#iter_rules iterer_rule;
			let iterer_prule _ (prule : #prule) =
				pr#endl;
				prule#print pr;
			in
			x#iter_prules iterer_prule;
			pr#putc ')';
			pr#leave 4;
			pr#endl;
		method output_xml_ths : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			let iterer_A (f:#sym) =
				match f#ty with
				| Th "AC" | Th "A" -> f#output_xml pr
				| _ -> ()
			in
			let iterer_C (f:#sym) =
				match f#ty with
				| Th "AC" | Th "C" -> f#output_xml pr
				| _ -> ()
			in
			if Ths.mem "AC" ths || Ths.mem "A" ths then begin
				MyXML.enclose "Asymbols" (fun _ -> x#iter_syms iterer_A) pr;
			end else begin
				MyXML.tag "Asymbols" pr; (* TODO refine CPF *)
			end;
			if Ths.mem "AC" ths || Ths.mem "C" ths then begin
				MyXML.enclose "Csymbols" (fun _ -> x#iter_syms iterer_C) pr;
			end else begin
				MyXML.tag "Csymbols" pr;
			end;
		method output_xml_rules : 'a. (#Io.printer as 'a) -> unit =
			MyXML.enclose "rules" (fun pr ->
(*				x#iter_rules (fun _ rule -> rule#output_xml pr)
*)				for i = 1 to rule_cnt do
					(x#find_rule i)#output_xml pr;
				done
			)
		method output_xml : 'a. (#Io.printer as 'a) -> unit =
			MyXML.enclose "trs" x#output_xml_rules << x#output_xml_ths

		method output_xml_ho_signature : 'a. (#Io.printer as 'a) -> unit = fun pr ->
			MyXML.enter "higherOrderSignature" pr;
			let first = ref true in
			let iterer_var (v:#sym) =
				if v#is_var then begin
					if !first then begin
						MyXML.enter "variableTypeInfo" pr;
						first := false;
					end;
					MyXML.enclose "varDeclaration" (
						v#output_xml <<
						MyXML.enclose "type" (MyXML.enclose "basic" (puts "o"))
					) pr;
				end;
			in
			x#iter_syms iterer_var;
			if not !first then
				MyXML.leave "variableTypeInfo" pr;
			first := true;
			let iterer_fun (f:#sym) =
				if f#is_fun then begin
					if !first then begin
						MyXML.enter "functionSymbolTypeInfo" pr;
						first := false;
					end;
					MyXML.enter "funcDeclaration" pr;
					f#output_xml pr;
					MyXML.enter "typeDeclaration" pr;
					for i = 0 to f#arity do
						MyXML.enclose "type" (MyXML.enclose "basic" (putc 'o')) pr;
					done;
					MyXML.leave "typeDeclaration" pr;
					MyXML.leave "funcDeclaration" pr;
				end;
			in
			x#iter_syms iterer_fun;
			if not !first then begin
				MyXML.leave "functionSymbolTypeInfo" pr;
			end;
			MyXML.leave "higherOrderSignature" pr;
		method output_xml_ho : 'a. (#Io.printer as 'a) -> unit =
			MyXML.enclose "trs" ( x#output_xml_rules << x#output_xml_ho_signature )
	end;;

type path = int * (int list)

let path_append (c1,is1) (c2,is2) = (c1 + c2, is1 @ is2)
let cu_append (c1,u1) (c2,u2) = (c1 + c2, u1#compose u2)


let problem_xml (trs : trs) =
	element "trs" (
		optional (attribute "condition-type") >>= fun cto ->
		(	match cto with
			| None | Some "ORIENTED" -> return ()
			| Some ct -> raise (No_support ("condition-type: " ^ ct))
		) >>= fun _ ->
		optional (attribute "problem") >>= fun pto ->
		many trs#input_sym_decl >>= fun _ ->
		many trs#input_rule >>= fun _ ->
		optional (
			element "infeasibility" (
				many trs#input_sym_decl >>= fun _ ->
				many (
					element "cond" (
						trs#term_element >>= fun l ->
						trs#term_element >>= fun r ->
						return (l,r)
					)
				) >>= fun conds ->
				return (MODE_infeasibility conds)
			)
		)
	) <|>
	element "problem" ((* XTC format *)
		element "trs" (
			trs#input_rules_xtc >>= fun _ ->
			element "signature" (
				many (
					element "funcsym" (
						element "name" string >>= fun fname ->
						element "arity" int >>= fun _ ->
						optional (element "theory" string >>= fun th ->
							if th = "A" || th = "C" || th = "AC" then
								return (trs#set_theory fname th)
							else raise (No_support ("theory " ^ th))
						) >>= fun _ ->
						return ()
					)
				)
			) >>= fun _ ->
			optional (element "comment" (many any)) >>= fun _ ->
			return ()
		) >>= fun _ ->
		return None
	)
