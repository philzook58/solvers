open Util
open Io
open Txtr

type ty = Nat | Int | Real | Bool | Prod of ty * ty

type name = string

type params = {
	cmd : string;
	args : string list;
	base_ty : ty;
	tmpvar : bool;
	linear : bool;
	quantified : bool;
	peek_in : bool;
	peek_out : bool;
	peek_to : out_channel;
}

let default_params cmd args = {
	cmd = cmd;
	args = args;
	base_ty = Real;
	tmpvar = true;
	linear = true;
	quantified = false;
	peek_in = false;
	peek_out = false;
	peek_to = stderr;
}

let params_of_xml default_params =
	element "smt" (
		default (false,stderr) (
			(bool_attribute "peek" >>= fun b -> return (b,stderr)) <|>
			(attribute "peekTo" >>= fun file -> return (true,open_out file))
		) >>= fun (peek,peek_to) ->
		default default_params.tmpvar (bool_attribute "tempvars") >>= fun tmpvar ->
		default default_params.linear (bool_attribute "linear") >>= fun linear ->
		default default_params.quantified (bool_attribute "quantified") >>= fun quantified ->
		default default_params.base_ty (validated_attribute "type" "int|real" >>=
			function "int" -> return Int | "real" -> return Real
		) >>= fun ty ->
		default (default_params.cmd, default_params.args) (
			(	element "command" string >>= fun cmd ->
				many (element "arg" string) >>= fun args ->
				return (cmd,args)
			) <|>
			element "z3" (
				return ("z3", ["-smt2";"-in"])
			) <|>
			element "cvc4" (
				return ("cvc4", ["--lang=smt2"; "--incremental"; "--produce-models"])
			)
		) >>= fun (cmd,args) ->
		return {
			cmd = cmd;
			args = args;
			base_ty = ty;
			tmpvar = tmpvar;
			linear = linear;
			quantified = quantified;
			peek_in = peek;
			peek_out = peek;
			peek_to = peek_to;
		}
	)

let z3_params = default_params "z3" ["-smt2";"-in"]
let cvc4_params = default_params "cvc4" ["--lang=smt2"; "--incremental"; "--produce-models"]

class virtual ['e,'d] base p =
	object (x:'b)
		val base_ty = p.base_ty
		method virtual add_assertion : 'e -> unit
		method virtual add_definition : name -> ty -> 'e -> unit
		method virtual add_declaration : 'd -> unit
		method virtual add_variable : name -> ty -> unit
		method virtual new_variable : name -> ty -> 'e
		method virtual temp_variable : ty -> 'e
		method virtual refer : ty -> 'e -> 'e
		method add_variable_base v = x#add_variable v base_ty
		method new_variable_base v = x#new_variable v base_ty
		method temp_variable_base = x#temp_variable base_ty
		method refer_base e = x#refer base_ty e
		method virtual force : (('e,'d) base -> 'e) -> 'e
		method virtual expand : 'e -> 'e
		method virtual expand_pair : 'e -> 'e * 'e
	end;;

type exp =
	| Dummy
	| EOF
	| Nil
	| EV of name
	| LI of int
	| LR of float
	| LB of bool
	| Not of exp
	| And of exp * exp
	| Or of exp * exp
	| Xor of exp * exp
	| Imp of exp * exp
	| Neg of exp
	| Add of exp * exp
	| Sub of exp * exp
	| Mul of exp * exp
	| Div of exp * exp
	| Mod of exp * exp
	| Max of exp list
	| Eq of exp * exp
	| Ge of exp * exp
	| Gt of exp * exp
	| Le of exp * exp
	| Lt of exp * exp
	| ForAll of dec list * exp
	| Exists of dec list * exp
	| ContextForAll of exp
	| ContextExists of exp
	| Delay of ( (exp,dec) base -> exp )
	| ZeroOne of exp list
	| ES1 of exp list
	| AtMost1 of exp list
	| OD of exp list
	| Cons of exp * exp
	| Dup of ty * exp
	| Car of exp
	| Cdr of exp
	| If of exp * exp * exp
	| App of exp list
and dec =
	| Dec of name * ty
	| Def of name * ty * exp
;;

let very_simple e =
	match e with
	| Nil | EV _ | Not (EV _) | LI _ | LB _ | LR _ -> true
	| _ -> false
let rec is_simple_conj e =
	very_simple e ||
	match e with
	| And(e1,e2) -> is_simple_conj e1 && is_simple_conj e2
	| _ -> false
let rec is_simple_disj e =
	very_simple e ||
	match e with
	| Or(e1,e2) -> is_simple_disj e1 && is_simple_disj e2
	| _ -> false
let rec is_simple_sum e =
	very_simple e ||
	match e with
	| Add(e1,e2) -> is_simple_sum e1 && is_simple_sum e2
	| _ -> false
let rec is_simple e =
	very_simple e ||
	match e with
	| Eq(e1,e2) -> very_simple e1 && very_simple e2
	| Gt(e1,e2) -> very_simple e1 && very_simple e2
	| Ge(e1,e2) -> very_simple e1 && very_simple e2
	| _		 -> false

exception Inconsistent
exception Internal of string
exception Invalid_formula of string * exp
exception Response of string * exp
exception Parse_error of string


class virtual sexp_printer =
	object (x)
		inherit printer
		method virtual pr_v : string -> unit
		method pr_ty =
			function
			| Int -> x#puts "Int";
			| Real	-> x#puts "Real";
			| Bool	-> x#puts "Bool";
			| _	 -> raise (Internal "type");
		method pr_ds =
			let pr_d =
				function
				| Dec(v,ty) -> x#pr_v v; x#puts " "; x#pr_ty ty;
				| _		 -> raise (Internal "dec");
			in
			function
			| []	-> ()
			| d::[] -> x#puts "("; pr_d d; x#puts ")";
			| d::ds -> x#puts "("; pr_d d; x#puts ") "; x#pr_ds ds;
		method pr_e e =
			let pr = x#puts in
			let pr_e = x#pr_e in
			let pr_i = x#put_int in
			let pr_f = x#put_float in
			let rec withpunc put punc =
				function
				| []	-> ();
				| [e] -> put e;
				| e::es -> put e; pr punc; withpunc put punc es
			in
			let rec pr_and =
				function
				| And(e1,e2) -> pr_and e1; x#endl; pr_and e2;
				| e -> pr_e e;
			in
			let rec pr_or =
				function
				| Or(e1,e2) -> pr_or e1; x#endl; pr_or e2;
				| e -> pr_e e;
			in
			let rec pr_xor =
				function
				| Xor(e1,e2) -> pr_xor e1; x#endl; pr_xor e2;
				| e -> pr_e e;
			in
			let rec pr_add =
				function
				| Add(e1,e2) -> pr_add e1; pr " "; pr_add e2;
				| e -> pr_e e;
			in
			let rec pr_mul =
				function
				| Mul(e1,e2) -> pr_mul e1; pr " "; pr_mul e2;
				| e -> pr_e e;
			in
			match e with
			| Dummy -> pr "<Dummy>"
			| EOF	 -> pr "<EOF>";
			| Nil	 -> pr "()";
			| EV v	-> x#pr_v v;
			| LI i	-> if i < 0 then (pr "(- "; pr_i (-i); pr ")";) else pr_i i;
			| LR r	-> if r < 0.0 then (pr "(- "; pr_f (-. r); pr ")";) else pr_f r;
			| LB b	-> pr (if b then "true" else "false");
			| Add(e1,e2) -> pr "(+ "; pr_add e1; pr " "; pr_add e2; pr ")";
			| Sub(e1,e2) -> pr "(- "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Neg e1		 -> pr "(- "; pr_e e1; pr ")";
			| Mul(e1,e2)	-> pr "(* "; pr_mul e1; pr " "; pr_mul e2; pr ")";
			| Div(e1,e2)	-> pr "(/ "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Mod(e1,e2)	-> pr "(mod "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Eq(e1,e2)	 ->
				let mid = if very_simple e1 && very_simple e2 then putc ' ' else endl in
				pr "(= "; x#enter 3; pr_e e1; mid x; pr_e e2; x#leave 3; pr ")"
			| Ge(e1,e2)	 ->
				let mid = if very_simple e1 && very_simple e2 then putc ' ' else endl in
				pr "(>= "; x#enter 4; pr_e e1; mid x; pr_e e2; x#leave 4; pr ")";
			| Gt(e1,e2)	 ->
				let mid = if very_simple e1 && very_simple e2 then putc ' ' else endl in
				pr "(> "; x#enter 3; pr_e e1; mid x; pr_e e2; x#leave 3; pr ")";
			| Le(e1,e2)	 -> pr "(<= "; pr_e e1; pr " "; pr_e e2; pr ")";
			| Lt(e1,e2)	 -> pr "(< "; pr_e e1; pr " "; pr_e e2; pr ")";
			| And(e1,e2)	->
				 pr "(and ";
				 x#enter 5;
				 pr_and e1; x#endl;
				 pr_and e2;
				 x#leave 5;
				 pr ")";
			| Or(e1,e2)	 ->
				pr "(or ";
				x#enter 4;
				pr_or e1; x#endl;
				pr_or e2;
				x#leave 4;
				pr ")";
			| Xor(e1,e2)	->
				pr "(xor ";
				x#enter 5;
				pr_xor e1; x#endl;
				pr_xor e2;
				x#leave 5;
				pr ")";
			| Not e1		->
				pr "(not ";
				x#enter 5;
				pr_e e1;
				x#leave 5;
				pr ")";
			| Imp(e1,e2)	->
				pr "(=> ";
				x#enter 4;
				pr_e e1; x#endl;
				pr_e e2;
				x#leave 4;
				pr ")";
			| ForAll(ds,e)	->
				pr "(forall (";
				x#enter 8;
				x#pr_ds ds; pr ")"; x#endl;
				pr_e e;
				pr ")";
				x#leave 8;
				x#endl;
			| Exists(ds,e)	->
				pr "(exists (";
				x#enter 8;
				x#pr_ds ds; pr ") ";
				x#leave 8;
				pr_e e; pr ")";
				x#endl;
			| Cons(e1,e2) -> x#enter 6; pr "(cons "; pr_e e1; x#endl; pr_e e2; pr ")"; x#leave 6;
			| Dup(_,e)		-> pr "(dup "; pr_e e; pr ")";
			| Car(e)		-> pr "(car "; pr_e e; pr ")";
			| Cdr(e)		-> pr "(cdr "; pr_e e; pr ")";
			| If(e1,e2,e3)	->
				let mid = if very_simple e1 && very_simple e2 && very_simple e3 then putc ' ' else endl in
				pr "(ite "; x#enter 4; pr_e e1; mid x; pr_e e2; mid x; pr_e e3; pr ")"; x#leave 4;
			| Max(es)	 -> pr "(max"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| ZeroOne(es) -> pr "(zeroone"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| ES1(es)	 -> pr "(es1"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| AtMost1(es) -> pr "(atmost1"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| OD(es)		-> pr "(od"; List.iter (fun e -> pr " "; pr_e e;) es; pr ")";
			| App(es)	 -> pr "("; withpunc pr_e " " es; pr ")";
			| Delay f	 -> pr "(delay...)";
			| ContextForAll f -> pr "(forall...)";
			| ContextExists f -> pr "(exists...)";
	end;;

class sexp_printer_wrap (base : #printer) = object
	inherit sexp_printer
	inherit printer
	(* Tedious! Can't be done elegantly? *)
	method puts = base#puts
	method putc = base#putc
	method put_int = base#put_int
	method flush = base#flush
	method close = base#close
	method endl = base#endl
	method enter = base#enter
	method leave = base#leave
	method pr_v = base#puts
end;;

let put_exp e (pr : #printer) = (new sexp_printer_wrap pr)#pr_e e

let prerr_exp e = put_exp e cerr


let is_zero =
	function
	| LI 0 -> true
	| LR 0.0 -> true
	| _ -> false

let is_one =
	function
	| LI 1 -> true
	| LR 1.0 -> true
	| _ -> false

let rec smt_not =
	function
	| LB b	-> LB (not b)
	| Not e -> e
	| Gt(e1,e2) -> Ge(e2,e1)
	| Ge(e1,e2) -> Gt(e2,e1)
	| Or(e1,e2) -> And(smt_not e1, smt_not e2)
	| And(e1,e2) -> Or(smt_not e1, smt_not e2)
	| If(c,t,e) -> If(c, smt_not t, smt_not e)
	| e	 -> Not(e)

let smt_delay e f =
	if is_simple e then f e else Delay(fun context -> f (context#expand e))

let smt_split e f =
	match e with
	| Cons(e1,e2) -> f e1 e2
	| _ -> Delay(fun context -> let (e1,e2) = context#expand_pair e in f e1 e2)

let smt_let ty e f =
	if is_simple e then f e else Delay(fun context -> f (context#refer ty e))

let smt_let_base e f =
	if is_simple e then f e else Delay(fun context -> f (context#refer_base e))

module StringPair = struct
	type t = string * string
	let compare (x0,y0) (x1,y1) =
		match Stdlib.compare x0 x1 with
			| 0 -> Stdlib.compare y0 y1
			| c -> c
	end

module BoolKnow = Map.Make(String)
module OrderKnow = Map.Make(StringPair)

let rec simplify_knowing kn e =
	match e with
	| LB _ | LI _ | LR _ -> e
	| EV v -> (try LB (BoolKnow.find v kn) with _ -> e)
	| Not e -> smt_not (simplify_knowing kn e)
	| And(e1,e2) -> (
		match simplify_knowing kn e1 with
		| LB b -> if b then simplify_knowing kn e2 else LB false
		| e1 -> (
			match simplify_knowing (assume_true e1 kn) e2 with
			| LB b -> if b then e1 else LB false
			| e2 -> And(e1,e2)
		)
	)
	| Or(e1,e2) -> (
		match simplify_knowing kn e1 with
		| LB b -> if b then LB true else simplify_knowing kn e2
		| e1 -> (
			match simplify_knowing (assume_false e1 kn) e2 with
			| LB b -> if b then LB true else e1
			| e2 -> Or(e1,e2)
		)
	)
	| Imp(e1,e2) -> (
		match simplify_knowing kn e1 with
		| LB b -> if b then simplify_knowing kn e2 else LB true 
		| e1 -> (
			match simplify_knowing (assume_true e1 kn) e2 with
			| LB b -> if b then LB true else smt_not e1
			| e2 -> Imp(e1,e2)
		)
	)
	| Add(e1,e2) -> simplify_knowing kn e1 +^ simplify_knowing kn e2
	| Mul(e1,e2) -> simplify_knowing kn e1 *^ simplify_knowing kn e2
	| If(c,t,e) -> (
		match simplify_knowing kn c with
		| LB b -> if b then simplify_knowing kn t else simplify_knowing kn e
		| c -> If(c, simplify_knowing (assume_true c kn) t, simplify_knowing (assume_false c kn) e)
	)
	| _ -> e
and assume_true e kn =
	match e with
	| EV v -> BoolKnow.add v true kn
	| Not e -> assume_false e kn
	| And(e1,e2) -> assume_true e2 (assume_true e1 kn)
	| _ -> kn
and assume_false e kn =
	match e with
	| EV v -> BoolKnow.add v false kn
	| Not e -> assume_true e kn
	| Or(e1,e2) -> assume_false e2 (assume_false e1 kn)
	| _ -> kn
and simplify_under e1 e2 =
	match e1, e2 with
	| LB _, _
	| _, LB _
	| _, LI _
	| _, LR _ -> e2
	| _ -> simplify_knowing (assume_true e1 BoolKnow.empty) e2
(*	| EV v1, Not(EV v2) -> if v1 = v2 then LB false else e2
	| Not(EV v1), EV v2 -> if v1 = v2 then LB false else e2
	| And(e3,e4), _ -> simplify_under e4 (simplify_under e3 e2)
	| Or _, _ -> e2
	| Not(EV v1), Not(EV v2) -> if v1 = v2 then LB true else e2
	| _, And(e3,e4) -> (
		let e3 = simplify_under e1 e3 in
		if e3 = LB false then e3
		else
			let e4 = simplify_under e1 e4 in
(*
			let e4 = simplify_under e3 e4 in
*)
			if e3 = LB true then e4
			else if e4 = LB false then e4
			else if e4 = LB true then e3
			else And(e3,e4)
	)
	| _, Or(e3,e4) -> (
		let e3 = simplify_under e1 e3 in
		if e3 = LB true then e3
		else
			let e4 = simplify_under e1 e4 in
(*
			let e4 = simplify_under (smt_not e3) e4 in
*)
			if e3 = LB false then e4
			else if e4 = LB false then e3
			else if e4 = LB true then e4
			else if simple_eq e3 e4 = Some true then e3
			else Or(e3,e4)
	)
	| _, If(c,t,e) -> (
		match simplify_under e1 c with
		| LB b -> if b then simplify_under e1 t else simplify_under e1 e
		| c ->
			(* t and e should be already simplified w.r.t. c *)
			If(c, simplify_under e1 t, simplify_under e1 e)
	)
	| Eq(l1,r1), Gt(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if (r2 >=^ l1) = LB true && (r1 >=^ l2) = LB true then LB false
		else l2 >^ r2
	| Eq(l1,r1), Ge(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
		else l2 >=^ r2
	| Gt(l1,r1), Eq(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true ||
			 r2 >=^ l1 = LB true && r1 >=^ l2 = LB true
		then LB false
		else l2 =^ r2
	| Gt(l1,r1), Gt(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
		else if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then LB false
		else l2 >^ r2
	| Gt(l1,r1), Ge(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
		else if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then LB false
		else l2 >=^ r2
	| Ge(l1,r1), Ge(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if l2 >=^ l1 = LB true && r1 >=^ r2 = LB true then LB true
		else if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then l2 =^ r2
		else l2 >=^ r2
	| Ge(l1,r1), Gt(l2,r2) ->
		let l2 = simplify_under e1 l2 in
		let r2 = simplify_under e1 r2 in
		if r2 >=^ l1 = LB true && r1 >=^ l2 = LB true then LB false
		else l2 >^ r2
	| _ -> e2
*)
and (&^) e1 e2 =
	match e1 with
	| LB b -> if b then e2 else e1
	| _ ->
		match simplify_under e1 e2 with
		| LB b -> if b then e1 else LB false
		| e2 -> And(e1,e2)
and (|^) e1 e2 =
	match e1 with
	| LB b -> if b then e1 else e2
	| _ ->
		match simplify_under (smt_not e1) e2 with
		| LB b -> if b then LB true else e1
		| e2 -> Or(e1,e2)
and (=>^) e1 e2 =
	match e1 with
	| LB b -> if b then e2 else LB true
	| _ -> match simplify_under e1 e2 with
		| LB b -> if b then LB true else smt_not e1
		| e2 -> Imp(e1,e2)
and simple_eq e1 e2 =
	match e1, e2 with
	| LB b1, LB b2 -> Some (b1 = b2)
	| LI i1, LI i2	-> Some (i1 = i2)
	| LR r1, LR r2	-> Some (r1 = r2)
	| Not e1, Not e2 -> simple_eq e1 e2
	| EV v1, EV v2 when v1 = v2 -> Some true
	| Not(EV v1), EV v2 when v1 = v2 -> Some false
	| EV v1, Not (EV v2) when v1 = v2 -> Some false
	| Nil, Nil
	| _ -> None
and (=^) e1 e2 =
	match simple_eq e1 e2 with Some b -> LB b
	| None -> (
		match e1, e2 with
		| LB b1, _ -> if b1 then e2 else smt_not e2
		| _, LB b2 -> if b2 then e1 else smt_not e1
		| Not e1, Not e2 -> e1 =^ e2
		| Ge(l1,r1),Ge(l2,r2) when simple_eq l1 l2 = Some true && simple_eq r1 r2 = Some true -> LB true
		| Gt(l1,r1),Gt(l2,r2) when simple_eq l1 l2 = Some true && simple_eq r1 r2 = Some true -> LB true
		| Eq(l1,r1),Eq(l2,r2)
		when simple_eq l1 l2 = Some true && simple_eq r1 r2 = Some true
			|| simple_eq l1 r2 = Some true && simple_eq r1 l2 = Some true
		-> LB true
(*		| If(c,t,e), e2 when very_simple e2 -> smt_if c (t =^ e2) (e =^ e2)
		| e1, If(c,t,e) when very_simple e1 -> smt_if c (e1 =^ t) (e1 =^ e)
*)		| _ -> Eq(e1,e2)
	)
and ( *^) e1 e2 =
	match e1, e2 with
	| LI 0, _
	| LR 0.0, _ -> e1
	| _, LI 0
	| _, LR 0.0 -> e2
	| LI 1, _
	| LR 1.0, _ -> e2
	| _, LI 1
	| _, LR 1.0 -> e1
	| LI i1, LI i2 -> LI(i1 * i2)
	| LR r1, LR r2 -> LR(r1 *. r2)
	| If(c,t,e), _ when is_zero t ->
		let nc = smt_not c in smt_pre_if c nc t (e *^ simplify_under nc e2)
	| If(c,t,e), _ when is_zero e ->
		smt_pre_if c (smt_not c) (t *^ simplify_under c e2) e
	| _, If(c,t,e) when is_zero t ->
		let nc = smt_not c in smt_pre_if c nc t (simplify_under nc e1 *^ e)
	| _, If(c,t,e) when is_zero e ->
		smt_pre_if c (smt_not c) (simplify_under c e1 *^ t) e
	| _ -> Mul(e1,e2)
and smt_pre_if c nc t e =
		if simple_eq t e = Some true then t
		else match t, e with
		| LB b, _ -> if b then c |^ e else nc &^ e
		| _, LB b -> if b then c =>^ t else c &^ t
		| _ when simple_eq t e = Some true -> t
		| If(c',t',e'), _ when simple_eq e' e = Some true -> If( c &^ c', t', e') (* c ? (c' ? t' : e) : e --> c && c' ? t' : e *)
		| If(c',t',e'), _ when simple_eq t' e = Some true -> If(nc |^ c', t', e') (* c ? (c' ? e : e') : e --> !c || c' ? e : e' *)
		| _, If(c',t',e') when simple_eq e' t = Some true -> If(nc &^ c', t', e') (* c ? t : (c' ? t' : t) --> !c && c' ? t' : t *)
		| _, If(c',t',e') when simple_eq t' t = Some true -> If( c |^ c', t', e') (* c ? t : (c' ? t : e') --> c || c' ? t : e' *)
		| _ -> If(c,t,e)
and smt_if c t e =
	match c with
	| LB b	-> if b then t else e
	| _	 -> let nc = smt_not c in smt_pre_if c nc (simplify_under c t) (simplify_under nc e)
and (+^) e1 e2 =
	match e1, e2 with
	| LI 0,	_		-> e2
	| LR 0.0, _	 -> e2
	| _, LI 0	 -> e1
	| _, LR 0.0	 -> e1
	| LI i1, LI i2	-> LI(i1 + i2)
	| LR r1, LR r2	-> LR(r1 +. r2)
	| Max es1, _	-> Max(List.map (fun e1 -> e1 +^ e2) es1)
	| _, Max es2	-> Max(List.map (fun e2 -> e1 +^ e2) es2)
	| _,Add(e3,e4)	-> Add(e1 +^ e3, e4)
	| Add(e3,e4),_	-> Add(e3, e4 +^ e2)
	| _			 -> Add(e1,e2)
and (>=^) e1 e2 =
	match e1, e2 with
	| EV v1, EV v2 when v1 = v2 -> LB true
	| LI i1, LI i2 -> LB(i1 >= i2)
	| LI i1, LR r2 -> LB(float_of_int i1 >= r2)
	| LR r1, LI i2 -> LB(r1 >= float_of_int i2)
	| LR r1, LR r2 -> LB(r1 >= r2)
	| If(c,t,e), e2 -> (
		match t >=^ simplify_under c e2, e >=^ simplify_under (smt_not c) e2 with
		| LB bt, e' -> if bt then c |^ e' else smt_not c &^ e'
		| t', LB be -> if be then c =>^ t' else c &^ t'
		| _ -> Ge(e1, e2)
		)
	| _, If(c,t,e) -> (
		match simplify_under c e1 >=^ t, simplify_under (smt_not c) e1 >=^ e with
		| LB bt, e' -> if bt then c |^ e' else smt_not c &^ e'
		| t', LB be -> if be then c =>^ t' else c &^ t'
		| _ -> Ge(e1, e2)
		)
	| _ -> Ge(e1, e2)
and (>^) e1 e2 =
	match e1, e2 with
	| EV v1, EV v2 when v1 = v2 -> LB false
	| LI i1, LI i2 -> LB(i1 > i2)
	| LI i1, LR r2 -> LB(float_of_int i1 > r2)
	| LR r1, LI i2 -> LB(r1 > float_of_int i2)
	| LR r1, LR r2 -> LB(r1 > r2)
	| If(c,t,e), e2 -> (
		match t >^ simplify_under c e2, e >^ simplify_under (smt_not c) e2 with
		| LB bt, e' -> if bt then c |^ e' else smt_not c &^ e'
		| t', LB be -> if be then c =>^ t' else c &^ t'
		| _ -> Gt(e1, e2)
		)
	| _, If(c,t,e) -> (
		match simplify_under c e1 >^ t, simplify_under (smt_not c) e1 >^ e with
		| LB bt, e' -> if bt then c |^ e' else smt_not c &^ e'
		| t', LB be -> if be then c =>^ t' else c &^ t'
		| _ -> Gt(e1, e2)
		)
	| _ -> Gt(e1,e2)

(*
let simplify_under e1 e2 = e2
let (&^) e1 e2 = And(e1,e2)
let (|^) e1 e2 = Or(e1,e2)
let (=>^) e1 e2 = Imp(e1,e2)
let (=^) e1 e2 = Eq(e1,e2)
let ( *^) e1 e2 =  Mul(e1,e2)
let smt_pre_if c nc t e = If(c,t,e)
let smt_if c t e = If(c,t,e)
let (+^) e1 e2 = Add(e1,e2)
let (>=^) e1 e2 = Ge(e1, e2)
let (>^) e1 e2 = Gt(e1,e2)
*)

let (<>^) e1 e2 = smt_not (e1 =^ e2)

let (<=^) e1 e2 = e2 >=^ e1
let (<^) e1 e2 = e2 >^ e1

let (-^) e1 e2 =
	if is_zero e2 then e1 else Sub(e1,e2)

let (/^) e1 e2 =
	if e1 = LI 0 || e2 = LI 1 then e1
	else Div(e1,e2)

let smt_xor e1 e2 =
	match e1, e2 with
	| LB b, _ -> if b then smt_not e2 else e2
	| _, LB b -> if b then smt_not e1 else e1
	| _ -> match e1 =^ e2 with LB b -> LB (not b) | _ -> Xor(e1,e2)

let smt_list_max = function
	| [e] -> e
	| es -> Max es

let smt_sum es = List.fold_left (+^) (LI 0) es

let smt_map_sum f xs = smt_sum (List.map f xs)

let smt_prod =
	let rec sub acc = function
	| [] -> acc
	| e::es -> let acc' = acc *^ e in if is_zero acc' then acc' else sub acc' es
	in
	sub (LI 1)

let smt_map_prod f =
	let rec sub acc = function
	| [] -> acc
	| x::xs -> let acc' = acc *^ f x in if is_zero acc' then acc' else sub acc' xs
	in
	sub (LI 1)

let smt_list_for_all f =
	let rec sub acc = function
		| [] -> acc
		| x::xs -> let acc' = acc &^ f x in if acc' = LB false then acc' else sub acc' xs
	in sub (LB true)

let smt_list_exists f =
	let rec sub acc = function
		| [] -> acc
		| x::xs -> let acc' = acc |^ f x in if acc' = LB true then acc' else sub acc' xs
	in sub (LB false)

let smt_conjunction = smt_list_for_all (fun x -> x)
let smt_disjunction = smt_list_exists (fun x -> x)

let smt_list_for_all2 f = List.fold_left2 (fun ret e1 e2 -> ret &^ f e1 e2) (LB true)
let smt_list_exists2 f = List.fold_left2 (fun ret e1 e2 -> ret |^ f e1 e2) (LB false)

let smt_mod e1 e2 = Mod(e1,e2)
let smt_max e1 e2 =
	match e1, e2 with
	| LI i1, LI i2 -> LI(if i1 > i2 then i1 else i2)
	| LR r1, LR r2 -> LR(if r1 > r2 then r1 else r2)
	| LI i1, LR r2 -> if float_of_int i1 > r2 then LI(i1) else LR(r2)
	| LR r1, LI i2 -> if r1 > float_of_int i2 then LR(r1) else LI(i2)
	| _, Max es2 -> Max(e1::es2)
	| Max es1,_	 -> Max(e2::es1)
	| _,_ -> Max[e1;e2]

let smt_car =
	function
	| Cons(e,_) -> e
	| Dup(_,e) -> e
	| e -> Car e

let smt_cdr =
	function
	| Cons(_,e) -> e
	| Dup(_,e) -> e
	| e -> Cdr e

;;

class virtual context ?(consistent=true) ?(temp_names=0) p =
	object (x:'t)
		inherit [exp,dec] base p
		val mutable consistent = consistent
		val mutable temp_names = temp_names

		method virtual private add_assertion_body : exp -> unit
		method virtual private add_declaration_body : dec -> unit

		method private branch = new subcontext consistent temp_names p

		method add_assertion =
			let rec sub e =
				x#add_assertion_body e;
				if e = LB false then begin
					debug (endl << puts "False assertion is made." << endl);
					consistent <- false;
					raise Inconsistent;
				end;
			in
			fun e -> if consistent then begin
				sub (x#expand e);
			end;
		method private add_declaration d =
			if consistent then begin
				let d =
					match d with
					| Def(v,ty,e) -> Def(v,ty,x#expand e)
					| _ -> d
				in
				x#add_declaration_body d;
			end
		method add_definition v ty e =
			x#add_declaration (Def(v,ty,e))

		method add_variable v ty = x#add_declaration (Dec(v,ty))

		method new_variable v ty = x#add_variable v ty; EV v

		method private temp_name =
			let v = "_" ^ string_of_int temp_names in
			temp_names <- temp_names + 1;
			v

		method temp_variable ty =
			x#new_variable x#temp_name ty

		method private refer_sub ty e =
			if not p.tmpvar || not consistent || is_simple e then e
			else
				match e with
					(* referring to IF expression can cause non-linearity *)
				| If(c,t,e) when ty <> Bool -> If(x#refer_sub Bool c, x#refer_sub ty t, x#refer_sub ty e)
				| Cons(e1,e2) ->
					(match ty with
					 | Prod(ty1,ty2) -> Cons(x#refer_sub ty1 e1, x#refer_sub ty2 e2)
					 | _ -> raise (Invalid_formula ("refer",e))
					)
				| _	 ->
					let v = x#temp_name in
					x#add_declaration_body (Def(v,ty,e));
					EV v

		method refer ty e = x#refer_sub ty (x#expand e)

		method force f = f (x:>(exp,dec) base)

		method private expand_and e1 e2 =
			match x#expand e1 with
			| LB false	-> LB false
			| e1		-> e1 &^ x#expand e2

		method private expand_or e1 e2 =
			match x#expand e1 with
			| LB true -> LB true
			| e1		-> e1 |^ x#expand e2

		method private expand_imp e1 e2 =
			match x#expand e1 with
			| LB false	-> LB true
			| e1		-> e1 =>^ x#expand e2

		method private linearize e = match e with
			| Add(e1,e2) -> x#linearize_add_sub (x#linearize e1) (x#linearize e2)
			| Mul(e1,e2) -> x#linearize_mul e1 e2
			| If(c,e1,e2) -> x#linearize_if_sub c (x#linearize e1) (x#linearize e2)
			| _ -> e

		method private linearize_add_sub e1 e2 =
			match e1, e2 with
			| If(c,t,e), _ ->
				let e2 = x#refer_base e2 in
				smt_if c (x#linearize_add_sub t e2) (x#linearize_add_sub e e2)
			| _, If(c,t,e) ->
				let e1 = x#refer_base e1 in
				smt_if c (x#linearize_add_sub e1 t) (x#linearize_add_sub e1 e)
			| _ -> Add(e1,e2)

		method private linearize_mul e1 e2 =
			x#linearize_mul_sub (x#linearize e1) (x#linearize e2)

		method private linearize_mul_sub e1 e2 =
			match e1, e2 with
			| LI 0, _ | LR 0.0, _ -> e1
			| _, LI 0 | _, LR 0.0 -> e2
			| LI 1, _ | LR 1.0, _ -> e2
			| _, LI 1 | _, LR 1.0 -> e1
			| If(c,t,e), _ ->
				let nc = smt_not c in
				if is_zero t then
					smt_pre_if c nc t (x#linearize_mul_sub e (simplify_under nc e2))
				else if is_zero e then
					smt_pre_if c nc (x#linearize_mul_sub t (simplify_under c e2)) e
				else
					let e2 = x#refer_sub base_ty e2 in
					smt_pre_if c nc (x#linearize_mul_sub t e2) (x#linearize_mul_sub e e2)
			| _, If(c,t,e) ->
				let nc = smt_not c in
				if is_zero t then
					smt_pre_if c nc t (x#linearize_mul_sub (simplify_under nc e1) e)
				else if is_zero e then
					smt_pre_if c nc (x#linearize_mul_sub (simplify_under nc e1) t) e
				else
					let e1 = x#refer_sub base_ty e1 in
					smt_pre_if c (smt_not c) (x#linearize_mul_sub e1 t) (x#linearize_mul_sub e1 e)
			| _ -> Mul(e1,e2)

		method private linearize_if_sub c t e =
			match c with
			| LB b -> if b then x#linearize t else x#linearize e
			| _ ->If(c, x#linearize t, x#linearize e)

		method private expand_mul e1 e2 =
			let e1 = x#expand e1 in
  			if is_zero e1 then e1 else
			let e2 = x#expand e2 in
			if is_zero e2 then e2 else
			if p.linear then x#linearize_mul e1 e2 else Mul(e1,e2)

		method private zero_one = (* returns (zero, one) *)
			function
			| []	->
				(LB true, LB false)
			| e::[] ->
				let e = x#refer Bool e in
				(smt_not e,e)
			| e::es ->
				let e = x#refer Bool e in
				let (zero,one) = x#zero_one es in
				let zero = x#refer Bool zero in
				let one = x#refer Bool one in
				(zero &^ smt_not e, (zero &^ e) |^ (one &^ smt_not e))
		method private expand_zero_one es =
			let (zero,one) = x#zero_one es in
			Cons(zero,one)
		method private expand_es1 es =
			let (zero,one) = x#zero_one es in
			one
		method private expand_atmost1 es =
			let (zero,one) = x#zero_one es in
			zero |^ one
		method private expand_od es =
			let (od,_) =
				List.fold_left (fun (od,e1) e2 -> (od &^ (e2 =>^ e1), e2)) (LB true, LB true) es
			in
			od
		method private expand_max =
			let rec distribute es0 =
				function
				| []	-> es0
				| e1::es1 ->
					match x#expand e1 with
					| Max es2 -> distribute (distribute es0 es2) es1
					| Add(e2, Max es2) ->
						let e2 = x#expand e2 in
						distribute (distribute es0 (List.map (fun e3 -> e2 +^ e3) es2)) es1
					| Add(Max es2, e2) ->
						let e2 = x#expand e2 in
						distribute (distribute es0 (List.map (fun e3 -> e3 +^ e2) es2)) es1
					| e2 -> distribute (x#expand e2::es0) es1
			in
			let rec sub eq max =
				function
				| []	-> x#add_assertion eq; max
				| e::es ->
					let e = x#refer base_ty e in
					x#add_assertion (max >=^ e);
					sub ((max =^ e) |^ eq) max es
			in
			fun es ->
				match distribute [] es with
				| []  -> raise (Invalid_formula ("empty max",Nil))
				| [e] -> x#expand e
				| es  -> (* Max (List.map x#expand es)*)
					sub (LB false) (x#temp_variable base_ty) es

		method private expand_car =
			function
			| Cons(e,_) -> x#expand e
			| Dup(_,e)	-> x#expand e
			| Delay(f)	-> x#expand_car (x#force f)
			| If(c,t,e) -> x#expand_if c (smt_car t) (smt_car e)
			| e				 -> raise (Invalid_formula ("expand_car", e))

		method private expand_cdr =
			function
			| Cons(_,e) -> x#expand e
			| Dup(_,e)	-> x#expand e
			| Delay(f)	-> x#expand_cdr (x#force f)
			| If(c,t,e) -> x#expand_if c (smt_cdr t) (smt_cdr e)
			| e		 -> raise (Invalid_formula ("expand_cdr", e))

		method private expand_if_sub e1 e2 e3 =
			match x#expand e2, x#expand e3 with
			| Cons(e4,e5), Cons(e6,e7) ->
				let e1 = x#refer_sub Bool e1 in
				Cons(x#expand_if_sub e1 e4 e6, x#expand_if_sub e1 e5 e7)
			| e2,e3 -> smt_if e1 e2 e3

		method private expand_if e1 e2 e3 =
			match x#expand e1 with
			| LB b	-> x#expand (if b then e2 else e3)
			| e1	-> x#expand_if_sub e1 e2 e3

		method expand e = 
			match e with
			| Nil	-> Nil
			| EV v -> EV v
			| LB b -> LB b
			| LI i -> LI i
			| LR r -> LR r
			| And(e1,e2) -> x#expand_and e1 e2
			| Or(e1,e2)  -> x#expand_or e1 e2
			| Xor(e1,e2) -> smt_xor (x#expand e1) (x#expand e2)
			| Imp(e1,e2) -> x#expand_imp e1 e2
			| Not(e)     -> smt_not (x#expand e)
			| Add(e1,e2) -> x#expand e1 +^ x#expand e2
			| Sub(e1,e2) -> x#expand e1 -^ x#expand e2
			| Mul(e1,e2) -> x#expand_mul e1 e2
			| Div(e1,e2) -> x#expand e1 /^ x#expand e2
			| Mod(e1,e2) -> smt_mod (x#expand e1) (x#expand e2)
			| Max es     -> x#expand_max es
			| Eq(e1,e2)  -> x#expand e1 =^ x#expand e2
			| Ge(e1,e2)  -> x#expand e1 >=^ x#expand e2
			| Gt(e1,e2)  -> x#expand e1 >^ x#expand e2
			| Le(e1,e2)  -> x#expand e1 <=^ x#expand e2
			| Lt(e1,e2)  -> x#expand e1 <^ x#expand e2
			| ForAll(ds,e) ->
				let branch = x#branch in
				List.iter branch#add_declaration ds;
				branch#close_for_all e
			| Exists(ds,e)	->
				let branch = x#branch in
				List.iter branch#add_declaration ds;
				branch#close_exists e
			| ContextForAll e -> x#branch#close_for_all e
			| ContextExists e -> x#branch#close_exists e
			| ZeroOne es -> x#expand_zero_one es
			| ES1 es     -> x#expand_es1 es
			| AtMost1 es -> x#expand_atmost1 es
			| OD es      -> x#expand_od es
			| Car e	     -> x#expand_car e
			| Cdr e	     -> x#expand_cdr e
			| Cons(e1,e2) -> Cons(e1,e2) (* do not expand at this point *)
			| Dup(ty,e)  -> let e = x#refer ty e in Cons(e,e)
			| If(c,t,e) -> x#expand_if c t e
			| App es  -> App(List.map x#expand es)
			| Delay f -> x#expand (f (x :> (exp,dec) base))
			| e	      -> raise (Invalid_formula ("expand",e))

		method expand_pair e =
			match x#expand e with Cons(e1,e2) -> (e1,e2) | _ -> raise (Invalid_formula ("smt_split", e))
	end
and subcontext consistent temp_names p =
	object (x)
		inherit context ~consistent ~temp_names p
		val mutable assertion = LB true
		val mutable declarations = []
		method private add_assertion_body e = assertion <- e &^ assertion
		method private add_declaration_body =
			function
			| Def(v,ty,e) ->
				declarations <- Dec(v,ty)::declarations;
				assertion <- EV v =^ e &^ assertion;
			| d ->
				declarations <- d::declarations;
		method close_exists e =
			let e = x#expand e in(* by this, declarations are made! *)
			if declarations = [] then e else Exists(declarations, assertion &^ e)
		method close_for_all e =
			let e = x#expand e in(* by this, declarations are made! *)
			if declarations = [] then e else ForAll(declarations, assertion =>^ e)
	end

let smt_context_for_all f = ContextForAll (Delay f)


class virtual solver p =
	object
		inherit context p
		method virtual init : unit
		method virtual check : unit
		method virtual get_bool : exp -> bool
		method virtual get_value : exp -> exp
		method virtual dump_value : string list -> out_channel -> unit
		method virtual push : unit
		method virtual pop : unit
		method virtual reset : unit
	end
;;

let smt_apply =
	function
	| [] -> Nil
	| [EV "not"; e] -> Not e
	| [EV "+"; e] -> e
	| [EV "+"; e1; e2] -> Add(e1,e2)
	| [EV "-"; e] -> (
		match e with LI i -> LI(-i) | LR r -> LR(-.r) | e -> Neg e
	)
	| [EV "-"; e1; e2] -> Sub(e1,e2)
	| [EV "/"; e1; e2] -> Div(e1,e2)
	| es -> App es

let (<<) s c = s ^ String.make 1 c

class virtual parser =
	let spaces = " \t\n\r" in
	let singles = "()\x00" in
	let breakers = spaces ^ singles in
	object (x)
		val mutable index = 1
		val mutable str = ""
		val mutable len = 0
		method virtual input_line : string
		method private peek_char =
			if index > len then
				try
					str <- x#input_line;
					len <- String.length str;
					index <- 0;
					str.[index]
			with End_of_file -> '\x00'
			else if index = len then
				'\n'
			else
				str.[index]
		method private proceed = index <- index + 1;
		method private trim =
			while String.contains spaces x#peek_char do x#proceed done;
		method get_token =
			x#trim;
			let c = x#peek_char in
			let s = String.make 1 c in
			x#proceed;
			if String.contains singles c then
				s
			else if c = '\"' then
				let rec sub s =
					let c = x#peek_char in
					let s = s << c in
					x#proceed;
					if c = '"' then s else sub s
				in
				sub s
			else
				let rec sub s =
					let c = x#peek_char in
					if String.contains breakers c then
						s
					else
						sub (x#proceed; s << c)
				in
				sub s
		method parse_app =
			let rec sub es =
				match x#peek_char with
				| ')' -> x#proceed; smt_apply es
				| '\x00' -> raise (Parse_error "unexpected EOF")
				| _ -> sub (es @ [x#get_exp])
			in
			sub []
		method get_exp =
			let token = x#get_token in
			match token with
			| "(" -> x#parse_app
			| "true" -> LB true
			| "false" -> LB false
			| "\x00" -> EOF
			| _ -> 
				if Str.string_match (Str.regexp "\\([0-9]+\\)") token 0 then
					let int_part = int_of_string (Str.matched_string token) in
					let next = Str.match_end () in
					if Str.string_match (Str.regexp "\\(\\.0\\)?$") token next then
						LI int_part
					else if Str.string_match (Str.regexp "\\.[0-9]+$") token next then
						LR(float_of_int int_part +. float_of_string (Str.matched_string token))
					else
						raise (Parse_error token)
				else
					EV token
	end

let rec smt_eval_float =
	function
	| LI i -> float_of_int i
	| LR r -> r
	| Neg e -> -.(smt_eval_float e)
	| Div(e1,e2) -> smt_eval_float e1 /. smt_eval_float e2
	| e -> raise (Invalid_formula ("eval_float",e))

let rec smt_eval_int e =
	match e with
	| LI i -> i
	| LR r -> raise (Invalid_formula ("real as int",e))
	| Neg e -> -(smt_eval_int e)
	| e -> raise (Invalid_formula ("eval_int",e))

let test_sat str = Str.string_match (Str.regexp "sat.*") str 0
let test_unsat str = Str.string_match (Str.regexp "un\\(sat\\|known\\).*") str 0

class virtual smt_lib_2_0 p =
	object (x)
		inherit Io.t
		inherit solver p
		inherit sexp_printer
		inherit parser

		val mutable initialized = false

		method init =
			if not initialized then begin
				initialized <- true;
				x#puts "(set-logic ";
				if not p.quantified then x#puts "QF_";
				x#puts (if p.linear then "L" else "N");
				x#puts (if base_ty = Int then "I" else "R");
				x#puts "A)";
				x#endl;
			end;

		method private add_declaration_body d =
			match d with
			| Dec(v,ty) ->
				x#puts "(declare-fun ";
				x#pr_v v;
				x#puts " () ";
				x#pr_ty ty;
				x#puts ")";
				x#endl;
			| Def(v,ty,e) ->
				x#puts "(define-fun ";
				x#pr_v v;
				x#puts " () ";
				x#pr_ty ty;
				x#puts " ";
				if ty = Bool then begin
					x#endl;
					x#enter 2;
					x#pr_e e;
					x#leave 2;
				end else begin
					x#enter_inline;
					x#pr_e e;
					x#leave_inline;
				end;
				x#puts ")";
				x#endl;
		method private add_assertion_body e =
			x#puts "(assert ";
			x#enter 8;
			x#pr_e e;
			x#leave 8;
			x#puts ")";
			x#endl;
		method check =
			x#puts "(check-sat)";
			x#endl;
			match x#get_exp with
			| EV "sat" -> ()
			| EV "unsat" | EV "unknown" -> raise Inconsistent
			| e -> raise (Response("check-sat",e))
		method get_bool e =
			match x#get_value e with
			| LB b -> b
			| v -> raise (Response("get_value (bool)",v))
		method get_value v =
			match v with
			| LB _
			| LI _
			| LR _ -> v
			| If(c,t,e) ->
				x#get_value (if x#get_bool c then t else e)
			| _ ->
				x#puts "(get-value (";
				x#pr_e (x#expand v);
				x#puts "))";
				x#endl;
				match x#get_exp with
				| App[App[e1;e2]] -> e2
				| e -> raise (Response("get-value",e))
		method dump_value vs os =
			if vs <> [] then
			(
				x#puts "(get-value (";
				List.iter (fun v -> x#pr_v v; x#puts " ") vs;
				x#puts "))";
				x#endl;
				let rec sub =
					function
					| [] -> ()
					| _::vs ->
						let s = x#input_line in
						output_string os (s^"\n");
						sub vs
				in
				sub vs
			)
		method push =
			x#puts "(push)";
			x#endl;
		method pop =
			x#puts "(pop)";
			x#endl;
		method reset =
			x#puts "(reset)"; x#endl; consistent <- true; temp_names <- 0;

		method pr_v v =
			let len = String.length v in
			let rec sub i =
				if i < len then begin
					begin
						match v.[i] with
						| 'a'..'z' | 'A'..'Z' | '0'..'9' |	'+' | '-' | '*' | '/'
						| '_' -> x#putc v.[i]
						| ' ' -> x#puts "<sp>"
						| '\''	-> x#puts "<q>"
						| '<' -> x#puts "<gt>"
						| '>' -> x#puts "<lt>"
						| '#' -> x#puts "<sh>"
						| ':' -> x#puts "<col>"
						| '\\'	-> x#puts "<bs>"
						| '.' -> x#puts "<dot>"
						| '{' -> x#puts "<bl>"
						| '}'	-> x#puts "<br>"
						| c	 -> x#putc '<'; x#put_hex (Char.code c); x#putc '>'
						end;
					sub (i+1);
				end
			in
			sub 0
	end

let create_solver p =
	object (x)
		inherit smt_lib_2_0 p as super
		inherit Proc.finalized (fun y -> y#close)
		val main = new Proc.t p.cmd p.args
		val dout = if p.peek_out then new pretty_wrap_out p.peek_to else (Io.null :> printer)
		val din = if p.peek_in then new pretty_wrap_out p.peek_to else (Io.null :> printer)
		method endl = main#endl; dout#endl;
		method putc c = main#putc c; dout#putc c;
		method puts s = main#puts s; dout#puts s;
		method enter n = dout#enter n;
		method leave n = dout#leave n;
		method enter_inline = dout#enter_inline;
		method leave_inline = dout#leave_inline;
		method ready = main#ready;
		method flush = main#flush; dout#flush;
		method init = main#init; super#init;
		method close = main#close; dout#close;

		method input_line =
			din#puts "; ";
			din#flush;
			let s = main#input_line in
			din#puts s;
			din#endl;
			s
	end

