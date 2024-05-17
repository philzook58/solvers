open Util
open Txtr
open Io

type range = Pos | Bool | Full | Neg

let put_range ty range =
	match ty, range with
	| Smt.Int, Pos -> puts "Nat"
	| Smt.Int, Full -> puts "Int"
	| Smt.Int, Neg -> puts "NegInt"
	| Smt.Real, Pos -> puts "PosReal"
	| Smt.Real, Neg -> puts "NegReal"
	| Smt.Real, Full -> puts "Real"
	| _, Bool -> puts "Bool"
	| _ -> assert false

type template =
| Const of int
| Prod of template list
| Sum of template list
| Max of template list
| Min of template list
| Var of range
| Choice of template list
| Arg of int * int
| ProdArgs of template
| SumArgs of template
| MaxArgs of template
| Heuristic1 of template * template
| ArityChoice of (int -> template) (* Arity -1,-2,-3 will encode A,C,AC *)

let ( *?) s t = Prod[s;t]
let (+?) s t = Sum[s;t]
let (|?) s t = Max[s;t]

type order_mode =
| O_strict
| O_weak
| O_equal

let put_order_mode = function
| O_strict -> puts ">"
| O_weak -> puts "≥"
| O_equal -> puts "="


let arg mono x = if mono then x else Var Bool *? x

let sum_ac_mono i = Arg(0,i) +? Arg(1,i) +? Var Pos
let sum_ac i ran = (Var Bool *? (Arg(0,i) +? Arg(1,i))) +? Var ran
let sum_a i ran = (Var Bool *? Arg(0,i)) +? (Var Bool *? Arg(1,i)) +? Var ran
let max_ac_simp i = Arg(0,i) |? Arg(1,i) |? Var Pos
let max_ac i = Var Bool *? (Arg(0,i) |? Arg(1,i)) |? Var Pos
let max_c_simp i = (Arg(0,i) |? Arg(1,i)) +? Var Pos
let max_c i = Var Bool *? (Arg(0,i) |? Arg(1,i)) +? Var Pos
let max_a i = (Var Bool *? Arg(0,i)) |? (Var Bool *? Arg(1,i)) |? Var Pos

let sum_weight ~mono =
	[Pos, O_strict, "Sum", ArityChoice(fun a ->
			if a >= 0 then SumArgs(arg mono (Arg(-1,0)) +? Var Pos)
			else if mono then sum_ac_mono 0
			else if a = -1 (* A *) then sum_a 0 Pos
			else sum_ac 0 Pos (* AC/C *)
		)
	]
let coeff12 = Choice[Const 2; Const 1]

let mono_bpoly_weight =
	[Pos, O_strict, "Poly", ArityChoice(fun a ->
			if a >= 0 then SumArgs((coeff12 *? Arg(-1,0)) +? Var Pos)
			else if a = -1 (* A *) then (coeff12 *? Arg(0,0)) +? (coeff12 *? Arg(1,0)) +? Var Pos
			else if a = -2 (* C *) then coeff12 *? (Arg(0,0) +? Arg(1,0)) +? Var Pos
			else (* AC *) sum_ac_mono 0
		)
	]
let max_weight ~simp =
	[Pos, O_strict, "Max", ArityChoice(function
			| -3 (* AC *) -> if simp then max_ac_simp 0 else max_ac 0
			| -2 (* C *)  -> if simp then max_c_simp 0 else max_c 0
			| -1 (* A *)  -> if simp then max_ac_simp 0 else max_a 0
			| 0 -> Var Pos
			| 1 -> arg simp (Arg (0,0)) +? Var Pos
			| _ -> MaxArgs(arg simp (Arg(-1,0) +? Var Pos))
		)
	]
let neg_sum_weight =
	[	Pos, O_strict, "Sum", ArityChoice(function
			| -3 | -2 (* AC/C *)  -> sum_ac 0 Pos
			| -1 (* A *)  -> sum_a 0 Pos
			| 0 -> Var Pos
			| _ -> (SumArgs(Var Bool *? Arg(-1,0)) +? Var Full) |? Const 0
		)
	]
let neg_max_weight =
	[	Pos, O_strict, "Max", ArityChoice(function
			| -3 (* AC *) -> max_ac 0
			| -2 (* C *)  -> max_c 0
			| -1 (* A *)  -> max_a 0
			| 0 -> Var Pos
			| _ -> (MaxArgs(Var Bool *? (Arg(-1,0) +? Var Full))) |? Const 0
		)
	]
let max_sum_weight ~maxarity ~simp =
	[	Pos, O_strict, "MaxSum", ArityChoice(function
			| -3 (* AC *) -> if simp then Heuristic1(sum_ac_mono 0, max_ac_simp 0) else Heuristic1(sum_ac 0 Pos, max_ac 0)
			| -2 (* C  *) -> if simp then Heuristic1(sum_ac_mono 0, max_c_simp 0) else Heuristic1(sum_ac 0 Pos, max_c 0)
			| -1 (* A  *) -> if simp then Heuristic1(sum_ac_mono 0, max_ac_simp 0) else Heuristic1(sum_a 0 Pos, max_a 0)
			| 0 -> Var Pos
			| 1 -> arg simp (Arg(-1,0)) +? Var Pos
			| _ -> Heuristic1(SumArgs(arg simp (Arg(-1,0))) +? Var Pos, MaxArgs(arg simp (Arg(-1,0) +? Var Pos)))
(*
			| i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
				MaxArgs(arg +? Var Pos)
			| _ -> Choice[SumArgs(arg) +? Var Pos; MaxArgs(arg +? Var Pos);]
*)
		)
	]
let neg_max_sum_weight ~maxarity =
	[	Pos, O_strict, "MaxSum", ArityChoice(function
			| -3 (* AC *) -> Heuristic1(sum_ac 0 Pos, max_ac 0)
			| -2 (* C  *) -> Heuristic1(sum_ac 0 Pos, max_c 0)
			| -1 (* A  *) -> Heuristic1(sum_a 0 Pos, max_a 0)
			| 0 -> Var Pos
			| 1 -> Max[(Var Bool *? Arg(0,0)) +? Var Full; Const 0]
			| _ -> Heuristic1(
				Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0],
				Max[MaxArgs(Var Bool *? (Arg(-1,0) +? Var Full)); Const 0]
			)
(*
			| i when maxarity <= i -> (* interpretting big-arity symbols as sum leads to huge formula. *)
				Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0]
			| _ -> Choice[
					Max[SumArgs(Var Bool *? Arg(-1,0)) +? Var Full; Const 0];
					Max[MaxArgs(Var Bool *? Arg(-1,0) +? Var Full); Const 0];
				]
*)
		)
	]

let bmat_weight ~mono ~simp ~dim =
	let entry j =
		(if simp || (mono && j = 0) then (Choice[Const 2; Const 1]) else Var Bool) *? Arg(-1,j)
	in
	List.init dim (fun j ->
		(Pos, (if j = 0 then O_strict else O_weak), "Sum-Sum", ArityChoice(function
				| -3 (* AC *) -> sum_ac j Pos
				| -2 (* C  *) -> sum_ac j Pos
				| -1 (* A  *) -> sum_a j Pos
				| _ -> SumArgs(Sum(List.init dim entry)) +? Var Pos
			)
		)
	)

let range_attribute =
	default Pos (
		validated_attribute "range" "pos|neg|bool|full" >>= fun s ->
		return (match s with "full" -> Full | "neg" -> Neg | "bool" -> Bool | _ -> Pos)
	)
let rec exp_element coord xmls = (
	element "const" (int >>= fun i -> return (Const i)) <|>
	element "sum" (many (exp_element coord) >>= fun ss -> return (Sum ss)) <|>
	element "prod" (many (exp_element coord) >>= fun ss -> return (Prod ss)) <|>
	element "max" (many ~minOccurs:1 (exp_element coord) >>= fun ss -> return (Max ss)) <|>
	element "bot" (return (Max [])) <|>
	element "min" (many ~minOccurs:1 (exp_element coord) >>= fun ss -> return (Min ss)) <|>
	element "var" (range_attribute >>= fun r -> return (Var r)) <|>
	element "choice" (many ~minOccurs:1 (exp_element coord) >>= fun ss -> return (Choice ss)) <|>
	element "heuristic" (validated_attribute "mode" "maxsum" >>= fun m ->
		exp_element coord >>= fun s ->
		exp_element coord >>= fun t ->
		return (Heuristic1(s,t))
	) <|>
	element "arg" (
		default (-1) (int_attribute "index") >>= fun i ->
		default coord (int_attribute "coord") >>= fun j ->
		return (Arg(i,j))
	) <|>
	element "args" (
		default "sum" (validated_attribute "mode" "sum|max|prod") >>= fun mode ->
		exp_element coord >>= fun s ->
		return (match mode with "max" -> MaxArgs s | "prod" -> ProdArgs s | _ -> SumArgs s)
	)
) xmls

let exp_seq coord =
	many (
		element "case" (
			mandatory (int_attribute "arity") >>= fun a ->
			exp_element coord >>= fun s ->
			return (a,s)
		)
	) >>= fun ass ->
	exp_element coord >>= fun d ->
	let f a = match List.assoc_opt a ass with Some s -> s | None -> d in
	return (ArityChoice f)

let template_entry_element i =
	element "entry" (
		attribute "name" >>= fun name ->
		range_attribute >>= fun r ->
		default (if i = 0 then O_strict else O_weak) (
			validated_attribute "order" "strict|weak|equal" >>= fun str ->
			return (match str with
				| "strict" -> O_strict
				| "weak" -> O_weak
				| _ -> O_equal
			)
		) >>= fun ord ->
		exp_seq i >>= fun t ->
		return (r,ord,name,t)
	)

let weight_element ~mono ~simp =
	element "poly" (return (mono_bpoly_weight)) <|>
	element "sum" (
		default false (bool_attribute "neg") >>= fun neg ->
		return (if neg then neg_sum_weight else sum_weight ~mono)
	) <|>
	element "max" (
		default false (bool_attribute "neg") >>= fun neg ->
		return (if neg then neg_max_weight else max_weight ~simp:mono)
	) <|>
	element "maxSum" (
		if mono && not simp then fatal (puts "not allowed in rule removal") else
		default false (bool_attribute "neg") >>= fun neg ->
		default 4 (int_attribute "maxArity") >>= fun m ->
		return (if neg then neg_max_sum_weight ~maxarity:m else max_sum_weight ~simp ~maxarity:m)) <|>
	element "matrix" (
		mandatory (int_attribute "dim") >>= fun dim ->
		return (bmat_weight ~mono ~simp ~dim)
	) <|>
		many_i template_entry_element


type prec_mode =
| PREC_none
| PREC_strict
| PREC_quasi
| PREC_equiv
type status_mode =
| S_none
| S_empty
| S_partial
| S_total

type order_params = {
	smt_params : Smt.params;
	dp : bool;
	quantify_unconditional : bool;
	wpo_quantify : bool;
	w_quantify : bool;
	w_templates : (range * order_mode * string * template) array;
	ext_mset : bool;
	ext_lex : bool;
	status_mode : status_mode;
	status_copy : bool;
	status_nest : int;
	prec_mode : prec_mode;
	prec_partial : bool;
	prec_quantify : bool;
	mincons : bool;
	maxcons : bool;
	ac_w : bool;
	strict_equal : bool;
	collapse : bool;
	mutable usable : bool;
	usable_w : bool;
	use_scope : bool;
	use_scope_ratio : int;
	negcoeff : bool;
}

(* checks monotonicity *)
let nonmonotone p =
  p.dp ||
  p.collapse ||
  p.status_mode = S_partial ||
  p.status_mode = S_empty && p.prec_mode <> PREC_none

let order_params
	?(dp=true) ?(prec_mode=PREC_none) ?(prec_partial=false) ?(prec_quantify=false) ?(status=S_empty) ?(collapse=status<>S_empty)
	?(wpo_quantify=false)
	?(quantify_unconditional=false)
	?(usable=true) ?(w_quantify=false) ?(negcoeff=false)
	(smt:Smt.params) w_templates = {
	smt_params = { smt with
		quantified = smt.quantified || w_quantify || prec_quantify;
	};
	dp = dp;
	wpo_quantify = wpo_quantify;
	quantify_unconditional = quantify_unconditional;
	w_quantify = w_quantify;
	w_templates = Array.of_list w_templates;
	prec_mode = prec_mode;
	prec_partial = prec_partial;
	prec_quantify = prec_quantify;
	status_mode = status;
	status_nest = 0;
	status_copy = false;
	ext_lex = (match status with S_partial | S_total -> true | _ -> false);
	ext_mset = false;
	collapse = collapse;
	usable = usable;
	usable_w = false;
	mincons = false;
	maxcons = false;
	ac_w = true;
	strict_equal = false;
	use_scope = true;
	use_scope_ratio = 0;
	negcoeff = negcoeff;
}

let put_templates_name ty templates pr =
	ignore (Array.fold_left (fun pre (range,order,name,template) ->
		pr#puts pre;
		put_range ty range pr;
		pr#putc ',';
		put_order_mode order pr;
		pr#putc ',';
		pr#puts name;
		"; "
	) "(" templates);
	pr#puts ")"

let put_order p =
	let weighted = Array.length p.w_templates > 0 in
	if p.status_mode = S_empty && p.prec_mode = PREC_none then
		puts "Order" << put_templates_name p.smt_params.base_ty p.w_templates
	else fun pr ->
		(	match p.prec_mode with
			| PREC_quasi -> pr#puts "Q"
			| PREC_equiv -> pr#puts "Equi"
			| _ -> ()
		);
		(	match p.ext_lex, p.ext_mset with
			| true, true -> if weighted then pr#putc 'W'; pr#puts "RPO"
			| true, false -> pr#puts (if weighted then "WPO" else "LPO")
			| false, true -> if weighted then pr#putc 'W'; pr#puts "MPO"
			| _ -> pr#puts "SimpleOrder"
		);
		( match p.status_mode with
			| S_partial -> pr#puts "pS"
			| S_total -> pr#puts "S"
			| S_empty -> pr#puts "eS"
			| _ -> ()
		);
		if weighted then put_templates_name p.smt_params.base_ty p.w_templates pr;;

let order_element default_smt ~mono =
	element "order" (
		default (PREC_none,false) (
			validated_attribute "precedence" "none|quasi|partial|linear|equiv" >>= fun str ->
			return (
				match str with
				| "quasi" -> (PREC_quasi,false)
				| "linear" -> (PREC_strict,false)
				| "partial" -> (PREC_quasi,true)
				| "equiv" -> (PREC_equiv,false)
				| _ -> (PREC_none,false)
			)
		) >>= fun (prec_mode,prec_partial) ->
		default S_empty (
			validated_attribute "status" "none|partial|total|empty" >>= fun str ->
			return (match str with "none" -> S_none | "partial" -> S_partial | "total" -> S_total | _ -> S_empty)
		) >>= fun status -> (
			if mono then return false
			else default (status <> S_empty) (bool_attribute "collapse")
		) >>= fun collapse -> (
			if mono then return false
			else default true (bool_attribute "usable")
		) >>= fun usable ->
		( default "" (validated_attribute "quantify" "|none|all|weight|wpo") >>= fun str ->
			return (
				match str with
				| "" | "none" ->  (false,false)
				| "all" -> (true,true)
				| "weight" -> (false,true)
				| "wpo" -> (true,false)
				| _ -> assert false
			)
		) >>= fun (quantify_wpo, quantify_weight) ->
		default true (bool_attribute "linear") >>= fun linear ->
		let smt = { default_smt with
			Smt.linear = linear;
			quantified = quantify_wpo || quantify_weight;
		} in
		default smt (Smt.params_of_xml smt) >>= fun smt ->
		weight_element ~mono:(mono && status = S_empty) ~simp:(status = S_none || status = S_total) >>= fun weight ->
		return (
			order_params smt ~dp:(not mono) ~prec_mode ~prec_partial ~prec_quantify:quantify_wpo ~status:status ~collapse:collapse ~usable:usable ~wpo_quantify:quantify_wpo ~w_quantify:quantify_weight
			weight)
	)

let strategy_element default_smt =
	element "strategy" (
		default default_smt (Smt.params_of_xml default_smt) >>= fun default_smt ->
		many (order_element default_smt ~mono:true) >>= fun pre ->
		default false (element "freezing" (return true)) >>= fun freezing ->
		optional (
			element "dp" (return ()) >>= fun _ ->
			many (order_element default_smt ~mono:false) >>= fun orders_dp ->
			default [] (
				element "edge" (return ()) >>= fun _ ->
				many (order_element default_smt ~mono:false)
			) >>= fun orders_egde ->
			default 0 (
				element "loop" (int_attribute "steps" >>= return)
			) >>= fun loop ->
			return (orders_dp,orders_egde,loop)
		) >>= fun rest ->
		return (pre,freezing,rest,[])
	) <|> element "non-reachability" (
		many (order_element default_smt ~mono:false) >>= fun non ->
		return ([],false,None,non)
	)

let of_string default_smt =
	Txtr.parse_string (strategy_element default_smt)
let of_file default_smt =
	Txtr.parse_file (strategy_element default_smt)

let default smt = (
	[order_params smt ~dp:false mono_bpoly_weight],
	true, Some ( [
		order_params smt (sum_weight ~mono:false);
		order_params smt (max_weight ~simp:false);
		order_params smt ~prec_mode:PREC_quasi ~prec_partial:true ~status:S_partial [];
		order_params smt (neg_max_sum_weight ~maxarity:0);
		order_params smt ~prec_mode:PREC_quasi ~prec_partial:true ~status:S_partial (max_sum_weight ~simp:false ~maxarity:0);
		order_params smt (bmat_weight ~mono:false ~simp:false ~dim:2);
		order_params smt [
			(Pos, O_strict, "Sum-Sum", ArityChoice(function
				| -3 | -2 (* A?C *) -> sum_ac 0 Pos
				| -1 (* A  *) -> sum_a 0 Pos
				| 0 -> Var Pos
				| _ -> Max[SumArgs((Var Bool *? Arg(-1,0)) +? (Var Bool *? Arg(-1,1))) +? Var Full; Const 0]
			) );
			(Neg, O_weak, "Sum", ArityChoice(function
				| -3 | -2 (* A?C *) -> sum_ac 0 Neg
				| -1 (* A  *) -> sum_a 0 Neg
				| 0 -> Var Neg
				| _ -> SumArgs(Var Bool *? Arg(-1,1)) +? Var Neg
			) );
		];
		order_params smt [
			(Pos, O_strict, "MaxSum-Sum", ArityChoice(function
				| -3 (* AC *) -> Heuristic1(sum_ac 0 Pos, max_ac 0)
				| -2 (* C  *) -> Heuristic1(sum_ac 0 Pos, max_c 0)
				| -1 (* A  *) -> Heuristic1(sum_a 0 Pos, max_a 0)
				| 0 -> Var Pos
				| 1 -> Max[(Var Bool *? Arg(0,0)) +? (Var Bool *? Arg(0,1)) +? Var Full; Const 0]
				| _ -> Heuristic1 (
					Max[
						SumArgs((Var Bool *? Arg(-1,0)) +? (Var Bool *? Arg(-1,1))) +? Var Full;
						Const 0
					],
					Max[
						MaxArgs(
							Max[
								Var Bool *? (Arg(-1,0) +? Var Full);
								Var Bool *? (Arg(-1,1) +? Var Full)
							]
						);
						Const 0
					]
			) ) );
			(Neg, O_weak, "Sum", ArityChoice(function
				| -3 | -2 (* A?C *) -> sum_ac 0 Neg
				| -1 (* A  *) -> sum_a 0 Neg
				| 0 -> Var Neg
				| _ -> SumArgs(Var Bool *? Arg(-1,1)) +? Var Neg
			) );
		];
	], [
	], 3),
	[
		order_params ~w_quantify:true smt [
			(Neg, O_weak, "Sum", SumArgs(Var Bool *? Arg(-1,0)) +? Var Neg);
		];
		order_params smt ~prec_mode:PREC_quasi ~prec_partial:true ~status:S_partial [];
		order_params ~w_quantify:true ~prec_mode:PREC_quasi ~prec_partial:true ~status:S_partial smt [
			(Pos, O_strict, "Sum", SumArgs(Var Bool *? Arg(-1,0)) +? Var Pos);
		];
		order_params ~w_quantify:true smt [
			(Pos, O_weak, "Sum-Sum",
				SumArgs((Var Bool *? Arg(-1,0)) +? (Var Bool *? Arg(-1,1))) +? Var Pos
			);
			(Pos, O_weak, "Sum-Sum",
				SumArgs((Var Bool *? Arg(-1,0)) +? (Var Bool *? Arg(-1,1))) +? Var Pos
			);
		];
	]
)