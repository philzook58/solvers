open Sym
open Term
open Smt
open Util
open Preorder
open Params
open Io
open Strategy

type 'a template =
| BVar of 'a * range
| Smt of exp
| Prod of 'a template list
| Sum of 'a template list
| Max of 'a template list
| Cond of exp * 'a template * 'a template

let zero_template = Smt (LI 0)

let one_template = Smt (LI 1)

let sum_template =
	let rec sub acc ws =
		match ws with
		| [] -> (match acc with [] -> zero_template | [w] -> w | _ -> Sum acc)
		| Smt e :: ws -> sub2 e acc ws
		| Sum ws1 :: ws -> sub acc (ws1 @ ws)
		| w :: ws -> sub (w::acc) ws
	and sub2 e acc ws =
		match ws with
		| [] -> (match acc with [] -> Smt e | _ -> Sum(Smt e :: acc))
		| Smt e1 :: ws -> sub2 (e +^ e1) acc ws
		| Sum ws1 :: ws -> sub2 e acc (ws1 @ ws)
		| w :: ws -> sub2 e (w::acc) ws
	in fun ws -> sub [] ws (* don't eta contract, otherwise type inference doesn't work *)

let prod_template =
	let rec sub acc ws =
		match ws with
		| [] -> (match acc with [] -> one_template | [w] -> w | _ -> Prod acc)
		| Smt e :: ws -> if is_zero e then zero_template else sub2 e acc ws
		| Prod ws1 :: ws -> sub acc (ws1 @ ws)
		| w :: ws -> sub (w::acc) ws
	and sub2 e acc ws =
		match ws with
		| [] -> (match acc with [] -> Smt e | _ -> Prod (Smt e::acc))
		| Smt e1 :: ws -> if is_zero e1 then zero_template else sub2 (e *^ e1) acc ws
		| Prod ws1 :: ws -> sub2 e acc (ws1 @ ws)
		| w :: ws -> sub2 e (w::acc) ws
	in fun ws -> sub [] ws (* don't eta contract, otherwise type inference doesn't work *)

let max_template =
	let rec sub2 e acc ws =
		match ws with
		| [] -> if acc = [] then Smt e else Max (Smt e :: acc)
		| Max ws' :: ws -> sub2 e acc (ws' @ ws)
		| Smt e2 :: ws -> sub2 (smt_max e e2) acc ws
		| w :: ws -> sub2 e (w :: acc) ws
	in
	let rec sub acc ws =
		match ws with
		| [] -> (match acc with [w] -> w | _ -> Max acc)
		| Max ws' :: ws -> sub acc (ws' @ ws)
		| Smt e :: ws -> sub2 e acc ws
		| w :: ws -> sub (w :: acc) ws
	in fun ws -> sub [] ws (* don't eta contract, otherwise type inference doesn't work *)

let eval_template solver =
	let rec sub w =
		match w with
		| BVar(_,_) -> w
		| Smt e -> Smt (solver#get_value e)
		| Prod ws -> prod_template (List.map sub ws)
		| Sum ws -> sum_template (List.map sub ws)
		| Max ws -> max_template (remdups (List.map sub ws))
		| Cond(e,w1,w2) -> (
				match solver#get_value e with
				| LB b -> sub (if b then w1 else w2)
				| e' -> Cond(e', sub w1, sub w2)
			)
	in
	fun w -> sub w

let eval_template_vec solver = Array.map (eval_template solver)

let eq_0_template =
	let rec sub w =
		match w with
		| BVar(_,_) -> LB false (* incomplete *)
		| Smt e -> e =^ LI 0
		| Prod ws -> smt_list_exists sub ws
		| Sum ws -> smt_list_for_all sub ws (* cancellation is not considered *)
		| Max ws -> smt_list_for_all sub ws (* incomplete *)
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	in sub

let eq_1_template =
	let rec sub w =
		match w with
		| BVar(_,_) -> LB false (* incomplete *)
		| Smt e -> e =^ LI 1
		| Prod ws -> smt_list_for_all sub ws (* division is not considered *)
		| Sum ws -> sub_sum ws
		| Max ws -> smt_list_for_all sub ws (* incomplete *)
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all eq_0_template ws) |^ (eq_0_template w &^ sub_sum ws)
	in sub

let ge_0_template =
	let rec sub w =
		match w with
		| BVar(_,ran) ->
			LB (match ran with
				| Pos | Bool -> true
				| Neg | Full -> false (* incomplete *)
			)
		| Smt e -> e >=^ LI 0
		| Prod ws -> LB true (* don't support negative in products *)
		| Sum ws -> smt_list_for_all sub ws (* cancellation is not considered *)
		| Max ws -> smt_list_exists sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	in sub

let ge_1_template =
	let rec sub w =
		match w with
		| BVar(_,_) -> LB false (* incomplete *)
		| Smt e -> e >=^ LI 1
		| Prod ws -> smt_list_for_all sub ws
		| Sum ws -> sub_sum ws
		| Max ws -> smt_list_exists sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all ge_0_template ws) |^ (ge_0_template w &^ sub_sum ws)
	in sub

let const_on_template x =
	let rec sub w =
		match w with
		| BVar(v,_) -> LB (x <> v)
		| Smt e -> LB true
		| Prod ws -> smt_list_for_all sub ws |^ smt_list_exists eq_0_template ws
		| Sum ws -> smt_list_for_all sub ws
		| Max ws -> smt_list_for_all sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	in sub

let is_var_template x =
	let rec sub w =
		match w with
		| BVar(v,_) -> LB(x = v)
		| Smt e -> LB false
		| Prod ws -> sub_prod ws
		| Sum ws -> sub_sum ws
		| Max ws -> sub_max ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_prod ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all eq_1_template ws) |^ (eq_1_template w &^ sub_prod ws)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all eq_0_template ws) |^ (eq_0_template w &^ sub_sum ws)
	and sub_max ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all eq_0_template ws) |^ (eq_0_template w &^ sub_max ws)
	in sub

let weak_simple_on_template x =
	let rec sub w =
		match w with
		| BVar(v,_) -> LB(x = v)
		| Smt e -> LB false
		| Prod ws -> sub_prod ws
		| Sum ws -> sub_sum ws
		| Max ws -> smt_list_exists sub ws
		| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
	and sub_prod ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all ge_1_template ws) |^ (ge_1_template w &^ sub_prod ws)
	and sub_sum ws =
		match ws with
		| [] -> LB false
		| w::ws -> (sub w &^ smt_list_for_all ge_0_template ws) |^ (ge_0_template w &^ sub_sum ws)
	in sub

let put_template var : 'a template -> #printer -> unit =
	let paren l l' m = if l <= l' then m else putc '(' << m << putc ')' in
	let rec sub l w =
		match w with
		| BVar(v,_) -> var v
		| Smt (LI i) -> put_int i
		| Smt e -> put_exp e
		| Prod ws ->
			if List.exists (fun w -> w = Smt (LI 0)) ws then putc '0'
			else (
				match List.filter (fun w -> w <> Smt (LI 1)) ws with
				| [w] -> sub l w
				| ws -> paren l 2 (put_list (sub 2) (puts " * ") (putc '1') ws)
			)
		| Sum ws -> (
			match List.filter (fun w -> w <> Smt (LI 0)) ws with
			| [w] -> sub l w
			| ws -> paren l 1 (put_list (sub 1) (puts " + ") (putc '0') ws)
		)
		| Max ws -> puts "max{" << put_list (sub 0) (puts ", ") (puts "-oo") ws << puts "}"
		| Cond(e,w1,w2) -> paren l 0 (put_exp e << puts " ? " << sub 1 w1 << puts " : " << sub 0 w2)
	in
	fun w os -> (sub 0 w) os

let put_template_vec var wa =
	put_list (put_template var) (puts "; ") (puts "-") (Array.to_list wa)

let put_range s = puts (
	match s with Full -> "full" | Pos -> "pos" | Neg -> "neg" | Bool -> "bool"
)

let string_of_var (v,i) = v ^ "_" ^ string_of_int (i+1)

let exp_of_var vis = EV (string_of_var vis)

let put_var vi = putc '<' << puts (string_of_var vi) << putc '>'

let put_svar (v,i,s) = putc '<' << puts (string_of_var (v,i)) << putc ':' << put_range s << putc '>'

(* A polynomial is represented by a map. *)
module Poly = Map.Make(LexList(Hashed (struct type t = string * int * range end)))

let zero_poly = Poly.empty

let poly_coeff vs p =
	match Poly.find_opt vs p with
	| Some e -> e
	| _ -> LI 0

let put_monom vs e os = put_exp e os; List.iter (fun v -> puts "*" os; put_svar v os) vs

let put_poly p os = puts "SUM {" os; Poly.iter (fun vs e -> put_monom vs e os; os#puts ", ") p; putc '}' os

let refer_poly solver = Poly.map solver#refer_base

let var_poly v i r = Poly.singleton [(v,i,r)] (LI 1)

let const_poly = Poly.singleton []

let add_poly = Poly.union (fun vs e1 e2 -> Some (e1 +^ e2))

let sum_poly = List.fold_left add_poly Poly.empty

(* Product of sorted variable lists. Boolean variables are idempotent. *)
let mul_vars =
	let rec sub ret vs1 vs2 =
		match vs1,vs2 with
		| [], _ -> ret @ vs2
		| _, [] -> ret @ vs1
		| (_,_,r1 as v1)::vs1', v2::vs2' ->
			let c = compare v1 v2 in
			if c = 0 then sub (v1::(if r1 = Bool then ret else v2::ret)) vs1' vs2'
			else if c < 0 then sub (v1::ret) vs1' vs2
			else sub (v2::ret) vs1 vs2'
	in sub []

let add_monom_poly vs1 e1 = Poly.update vs1 (function None -> Some e1 | Some e2 -> Some (e1 +^ e2))

let mul_poly p1 p2 =
	let folder1 vs1 e1 acc =
		let folder2 vs2 e2 acc = add_monom_poly (mul_vars vs1 vs2) (e1 *^ e2) acc in
		Poly.fold folder2 p2 acc
	in
	Poly.fold folder1 p1 Poly.empty

let prod_poly = List.fold_left mul_poly (Poly.singleton [] (LI 1))

(* Max Polynomials *)
type mpoly = exp Poly.t list

let bottom_mpoly = []

let zero_mpoly = [zero_poly]

let put_mpoly mp = puts "max {" << put_list put_poly (puts ", ") nop mp << puts "}"

let refer_mpoly solver = List.map (refer_poly solver)

let var_mpoly v i r = [var_poly v i r]

let const_mpoly e = [const_poly e]

let max_mpoly = List.concat

let sum_mpoly mps : mpoly = List.map sum_poly (list_product mps)

let prod_mpoly mps = List.map prod_poly (list_product mps)

(* Conditioned Max Polynomials *)
type cmpoly = (exp * mpoly) list

let bottom_cmpoly = [(LB true, bottom_mpoly)]

let zero_cmpoly = [(LB true, zero_mpoly)]

let refer_cmpoly solver =
 	List.map (fun (c,mp) -> (
(* not sure why this explodes: solver#refer Smt.Bool *)
 c, refer_mpoly solver mp))

let var_cmpoly v i r = [(LB true, var_mpoly v i r)]

let const_cmpoly e = [(LB true, const_mpoly e)]

let cmps_op =
	let sub (c1,mp1) (c2,mps) = match c1 &^ c2 with LB false -> None | c -> Some (c, mp1 :: mps) in
	fun f cmps -> List.map (fun (c,mps) -> (c, f mps)) (list_product_fold_filter sub cmps [(LB true,[])])

let sum_cmpoly = cmps_op sum_mpoly

let prod_cmpoly = cmps_op prod_mpoly

let max_cmpoly = cmps_op max_mpoly

let cond_cmpoly c cmp1 cmp2 =
	let sub1 (d,mp) = match c &^ d with LB false -> None | d -> Some (d,mp) in
	let nc = smt_not c in
	let sub2 (d,mp) = match nc &^ d with LB false -> None | d -> Some (d,mp) in
	List.filter_map sub1 cmp1 @ List.filter_map sub2 cmp2

(* Vectors *)
let zero_vec dim = Array.make dim (zero_cmpoly)

let smult e = Array.map (fun cmp -> prod_cmpoly [const_cmpoly e; cmp])

let add_vec v1 v2 = Array.mapi (fun i w1 -> sum_cmpoly [w1; v2.(i)]) v1

(** Ordering **)

let rel_mpoly inner =
	fun mp1 mp2 -> smt_list_for_all (fun p2 -> smt_list_exists (fun p1 -> inner p1 p2) mp1) mp2

let rel_cmpoly inner =
	fun cmp1 cmp2 -> smt_conjunction (list_prod (fun(c1,mp1) (c2,mp2) -> (c1 &^ c2) =>^ inner mp1 mp2) cmp1 cmp2)

let relpair_mpoly inner context mp1 mp2 =
	let (ge,gt) =
		List.fold_left (fun (all_ge,all_gt) p2 ->
			let (ge,gt) =
				List.fold_left (fun (ex_ge,ex_gt) p1 ->
					let (ge,gt) = inner context p1 p2 in
					(ex_ge |^ ge, ex_gt |^ gt)
				)
				(LB false, LB false)
				mp1
			in
			(all_ge &^ ge, all_gt &^ gt)
		)
		(LB true, LB true)
		mp2
	in
	(ge,gt)

let relpair_cmpoly inner context cmp1 cmp2 =
	let ords = list_prod_filter (fun (c1,mp1) (c2,mp2) ->
			match c1 &^ c2 with
			| LB false -> None
			| c ->
				let (ge,gt) = inner context mp1 mp2 in Some (c =>^ ge, c =>^ gt)
		) cmp1 cmp2
	in
	let folder (ge,gt) (all_ge,all_gt) = (ge &^ all_ge, gt &^ all_gt) in
	let (ge,gt) = List.fold_left folder (LB true, LB true) ords in
	(ge,gt)

let ge_poly_coeffs =
	let ge_monom =
		let rec sub flag vs = 
			match vs with
			| [] -> if flag then (>=^) else (<=^)
			| (v,i,s) :: vs ->
				match s with
				| Full -> (=^)
				| Pos | Bool -> sub flag vs
				| Neg -> sub (not flag) vs
		in sub true
	in
	let merger vs e1opt e2opt = Some(
		match e1opt, e2opt with
		| Some e1, Some e2 -> ge_monom vs e1 e2
		| Some e1, None    -> ge_monom vs e1 (LI 0)
		| None   , Some e2 -> ge_monom vs (LI 0) e2
		| _ -> assert false
		)
	in
	fun p1 p2 -> Poly.(bindings (merge merger p1 p2))

let ge_poly p1 p2 = smt_list_for_all (fun (vs,e) -> e) (ge_poly_coeffs p1 p2)
let ge_mpoly = rel_mpoly ge_poly
let ge_cmpoly = rel_cmpoly ge_mpoly

let pre_ge_poly p1 p2 =
		smt_list_for_all (fun (vs,e) -> if vs = [] then LB true else e) (ge_poly_coeffs p1 p2)

let gt_poly p1 p2 = pre_ge_poly p1 p2 &^ (poly_coeff [] p1 >^ poly_coeff [] p2)
let gt_mpoly = rel_mpoly gt_poly
let gt_cmpoly = rel_cmpoly gt_mpoly

let order_poly context p1 p2 =
	let pre = context#refer Smt.Bool (pre_ge_poly p1 p2) in
	let e1 = poly_coeff [] p1 in
	let e2 = poly_coeff [] p2 in
	((e1 >=^ e2) &^ pre, (e1 >^ e2) &^ pre)
let order_mpoly = relpair_mpoly order_poly
let order_cmpoly = relpair_cmpoly order_mpoly

let order_open solver e1 e2 =
	(e1 >=^ e2, e1 >^ e2)

(** Equality **)
let eq_0_poly p =
	let folder vs1 e1 acc = acc &^ (e1 =^ LI 0) in
	Poly.fold folder p (LB true)

let eq_0_mpoly = smt_list_for_all eq_0_poly

let eq_0_cmpoly = smt_list_for_all (fun (c,mp) -> c =>^ eq_0_mpoly mp) 

let eq_poly =
	let merger vs e1opt e2opt = Some(
		match e1opt, e2opt with
		| Some e1, Some e2 -> e1 =^ e2
		| Some e1, None    -> e1 =^ (LI 0)
		| None   , Some e2 -> (LI 0) =^ e2
		| _ -> assert false
		)
	in
	fun p1 p2 -> smt_list_for_all (fun (vs,e) -> e) Poly.(bindings (merge merger p1 p2))
let eq_mpoly mp1 mp2 = rel_mpoly eq_poly mp1 mp2 &^ rel_mpoly eq_poly mp2 mp1
let eq_cmpoly = rel_cmpoly eq_mpoly

let co_eq_cmpoly cmp1 cmp2 = gt_cmpoly cmp1 cmp2 |^ gt_cmpoly cmp2 cmp1

type pos_info = {
	const : exp;
	just : exp;
	weak_simple : exp;
}
type sym_info = {
	encodings : (int * int) template array;
	pos_info : pos_info array;
}

let add_svar context (v,i,s) =
	let ev = context#new_variable_base (string_of_var (v,i)) in
	match s with
	| Pos -> context#add_assertion (ev >=^ LI 0)
	| Neg -> context#add_assertion (ev <=^ LI 0)
	| _ -> ()


exception Continue

let maxsum_heuristic (trs:Trs.trs) (dg:Dp.dg) =
object (x)
	val sym_table : (string, bool) Hashtbl.t = Hashtbl.create 64
	val mutable initialized = false
	method sym_mode f = if not initialized then x#init; x#get_max f
	method private set_max f =
		Hashtbl.replace sym_table f true
	method private get_max f =
		try Hashtbl.find sym_table f
		with Not_found -> false

	method private init =
		let rec annotate_vs (Node(f,ss)) =
			let args = List.map annotate_vs ss in
			let argvss = List.map get_weight args in
			let vs =
				if f#is_var then [Mset.singleton f#name]
				else if x#get_max f#name then
					List.concat argvss
				else
					List.map (List.fold_left Mset.union Mset.empty) (list_product argvss)
			in
			WT(f,args,vs)
		in
		let vcond svss tvss =
			List.for_all (fun tvs -> List.exists (Mset.subseteq tvs) svss) tvss
		in
		let rec sub (WT(f,ss,svss) as s) (WT(g,ts,tvss)) =
			List.iter (sub s) ts;
			if not (vcond svss tvss) && (not (x#get_max g#name) || (debug (puts "ok it happens..." << endl); false))
			then (x#set_max g#name; raise Continue);
		in
		let annotate_sub i lr =
			sub (annotate_vs lr#l) (annotate_vs lr#r);
		in
		let rec loop () =
			try
				trs#iter_rules annotate_sub;
				dg#iter_dps annotate_sub;
			with Continue -> loop ()
		in
		loop ();
		initialized <- true;
end;;

let transpose_array_list vs =
	match vs with
	| [] -> raise (Invalid_argument "transpose_array_list")
	| v::vs ->
		let rec sub acc vs =
			match vs with
			| [] -> acc
			| v::vs -> sub (Array.mapi (fun i xs -> v.(i)::xs) acc) vs
		in
		sub (Array.map (fun x -> [x]) v) vs

let order_main w_templates order_w ge_w eq_w v1 v2 =
	Delay (fun solver ->
		let (_,ge,gt_pre,gt) =
			Array.fold_left (
				fun (i,ge_rest,gt_pre,gt_rest) (_,mode,_,_) ->
				let w1 = v1.(i) in
				let w2 = v2.(i) in
				match mode with
				| O_strict ->
					let (ge,gt) = order_w solver w1 w2 in
					(i+1, ge_rest &^ ge, gt_pre, gt_rest |^ gt)
				| O_weak ->
					let ge = solver#refer Bool (ge_w w1 w2) in
					(i+1, ge_rest &^ ge, gt_pre &^ ge, gt_rest)
				| O_equal ->
					let eq = solver#refer Bool (eq_w w1 w2) in
					(i+1, ge_rest &^ eq, gt_pre &^ eq, gt_rest)
			) (0, LB true, LB true, LB false) w_templates
		in
		Cons(ge, gt &^ gt_pre)
	)

let co_order_main w_templates order_w gt_w co_eq_w v2 v1 =
	Delay (fun solver ->
		let (_,co_ge,co_gt_pre,co_gt) =
			Array.fold_left (
				fun (i,co_ge_rest,co_gt_pre,co_gt_rest) (_,mode,_,_) ->
				let w2 = v2.(i) in
				let w1 = v1.(i) in
				match mode with
				| O_strict ->
					let (ge,gt) = order_w solver w2 w1 in
					(i+1, co_ge_rest &^ ge, co_gt_pre, co_gt_rest |^ gt)
				| O_weak ->
					(i+1, co_ge_rest, co_gt_pre, co_gt_rest |^ gt_w w2 w1)
				| O_equal ->
					(i+1, co_ge_rest, co_gt_pre, co_gt_rest |^ co_eq_w w2 w1)
			) (0, LB true, LB true, LB false) w_templates
		in
		Cons(co_ge, co_gt &^ co_gt_pre)
	)

class interpreter p =
	let dim = Array.length p.w_templates in
	let range_of_coord i = let (r,_,_,_) = p.w_templates.(i) in r in
	let to_dim = int_list 0 (dim-1) in
	let put_arg =
		if dim = 1 then fun (k,_) -> puts "x" << put_int (k+1)
		else fun (k,i) -> puts "x" << put_int (k+1) << putc '_' << put_int (i+1)
	in
	object (x)
		val table = Hashtbl.create 64
		method init : 't. (#context as 't) -> Trs.trs -> Dp.dg -> unit = fun solver trs dg ->
			let heu = maxsum_heuristic trs dg in
			let iterer f =
				let mkvar = object
					val mutable cnt = 0
					method make =
						cnt <- cnt + 1;
						"w_" ^ f#name ^ "_" ^ string_of_int cnt
				end in
				let n = f#arity in
				let thy_n = match f#ty with
					| Th th -> (match th with "A" -> -1 | "C" -> -2 | "AC" -> -3 | _ -> assert false)
					| _ -> n
				in
				let to_n = int_list 0 (n-1) in
				let rec sub k t =
					match t with
					| Strategy.Var Bool ->
						let v = solver#new_variable mkvar#make Smt.Bool in
						Smt(smt_if v (LI 1) (LI 0))
					| Strategy.Var r ->
						let v = solver#new_variable_base mkvar#make in
						if r = Pos then solver#add_assertion (v >=^ LI 0)
						else if r = Neg then solver#add_assertion (v <=^ LI 0);
						Smt v
					| Strategy.Choice (t::ts) ->
						let rec sub2 acc ts = match ts with
							| [] -> acc
							| t::ts ->
								let w = sub k t in
								let c = solver#new_variable mkvar#make Smt.Bool in
								match acc, w with
								| Smt e1, Smt e2 -> sub2 (Smt (smt_if c e1 e2)) ts
								| _ -> sub2 (Cond(c,w,acc)) ts
						in
						sub2 (sub k t) ts
					| Strategy.Arg(i,j) -> BVar(((if i >= 0 then i else k), j), range_of_coord j)
					| Strategy.Const n -> Smt(LI n)
					| Strategy.Prod ts -> prod_template (List.map (sub k) ts)
					| Strategy.Sum ts -> sum_template (List.map (sub k) ts)
					| Strategy.Max ts -> max_template (List.map (sub k) ts)
					| Strategy.ProdArgs t -> prod_template (List.map (fun l -> sub l t) to_n)
					| Strategy.SumArgs t -> sum_template (List.map (fun l -> sub l t) to_n)
					| Strategy.MaxArgs t -> max_template (List.map (fun l -> sub l t) to_n)
					| Strategy.Heuristic1(t1,t2) -> sub k (if heu#sym_mode f#name then t2 else t1)
					| Strategy.ArityChoice fn -> sub k (fn thy_n)
					| _ -> assert false
				in
				let vec = Array.map (fun (range,order,n,t) -> sub 0 t) p.w_templates in
				Hashtbl.add table f#name {
					encodings = vec;
					pos_info = Array.of_list (
						List.map (fun k ->
							{
								const = smt_list_for_all (fun i ->
									smt_list_for_all (fun j -> const_on_template (k,i) vec.(j)) to_dim
								) to_dim;
								just = smt_list_for_all (fun i -> is_var_template (k,i) vec.(i)) to_dim;
								weak_simple = smt_list_for_all (fun i ->
									match p.w_templates.(i) with
									| (Pos,O_weak,_,_) | (Pos,O_strict,_,_) ->
										weak_simple_on_template (k,i) vec.(i)
									| _ -> is_var_template (k,i) vec.(i)
								) to_dim;
							}
						) (int_list 0 (f#arity - 1))
					);
				}
			in
			trs#iter_funs iterer;
			debug2 (fun os ->
				os#endl; os#puts "Weight template:"; os#endl;
				trs#iter_funs (fun f ->
					x#output_sym_template f os;
					endl os
				)
			)

		method private find : 'f. (#sym as 'f) -> _ =
			fun f -> Hashtbl.find table f#name

		method constant_at : 'f. (#sym as 'f) -> int -> exp =
			(* <--> [f](..x_k..) is constant *)
			fun f k -> (x#find f).pos_info.(k-1).const

		method collapses_at : 'f. (#sym as 'f) -> int -> exp =
			(* <--> [f](..x_k..) = x_k *)
			fun f k -> (x#find f).pos_info.(k-1).just

		method weak_simple_at : 'f. (#sym as 'f) -> int -> exp =
			(* <--> [f](..x_k..) >= x_k *)
			fun f k -> (x#find f).pos_info.(k-1).weak_simple

		method private encode_sym : 'f. (#sym as 'f) -> _ =
			fun f -> (x#find f).encodings

		method private interpret : 'f. (#sym as 'f) -> cmpoly array list -> cmpoly array =
			fun f vs ->
			let subst = Array.of_list vs in
			let rec sub w =
				match w with
				| Smt e -> const_cmpoly e
				| BVar((k,i),s) -> subst.(k).(i)
				| Max ws -> max_cmpoly (List.map sub ws)
				| Sum ws -> sum_cmpoly (List.map sub ws)
				| Prod ws -> prod_cmpoly (List.map sub ws)
				| Cond(e,w1,w2) -> cond_cmpoly e (sub w1) (sub w2)
			in
			if f#is_var then Array.init dim (fun i -> var_cmpoly f#name i (range_of_coord i))
			else Array.map sub (x#encode_sym f)

		method private interpret_open : 'f. (#sym as 'f) -> exp array list -> exp array =
			fun f vs ->
			let subst = Array.of_list vs in
			let rec sub w =
				match w with
				| Smt e -> e
				| BVar((k,i),s) -> subst.(k).(i)
				| Max ws -> smt_list_max (List.map sub ws)
				| Sum ws -> smt_sum (List.map sub ws)
				| Prod ws -> smt_prod (List.map sub ws)
				| Cond(e,w1,w2) -> smt_if e (sub w1) (sub w2)
			in
			if f#is_var then Array.init dim (fun i -> exp_of_var (f#name,i))
			else Array.map sub (x#encode_sym f)

		method eval : 'f. (#sym as 'f) term -> cmpoly array =
			fun (Node(f,ss)) -> x#interpret f (List.map x#eval ss)

		method eval_open : 'f. (#sym as 'f) term -> exp array =
			fun (Node(f,ss)) -> x#interpret_open f (List.map x#eval_open ss)

		method annotate : 't 'f. (#context as 't) -> (#sym as 'f) term -> ('f, cmpoly array) wterm =
			fun solver (Node(f,ss)) ->
			let ts = List.map (x#annotate solver) ss in
			let vec = x#interpret f (List.map get_weight ts) in
			WT(f, ts, Array.map (refer_cmpoly solver) vec)

		method annotate_open : 't 'f. (#context as 't) -> (#sym as 'f) term -> ('f, exp array) wterm =
			fun solver (Node(f,ss)) ->
			let ts = List.map (x#annotate_open solver) ss in
			let vec = x#interpret_open f (List.map get_weight ts) in
			WT(f, ts, Array.map solver#refer_base vec)

		method output_sym : 't 'f 'o. (#solver as 't) -> (#Trs.sym_detailed as 'f) -> (#printer as 'o) -> unit =
			fun solver f os -> put_template_vec put_arg (eval_template_vec solver (x#encode_sym f)) os;

		method output_sym_template : 'o 'f. (#sym as 'f) -> (#printer as 'o) -> unit =
			fun f -> f#output << puts ": " << put_template_vec put_arg (x#encode_sym f)

		method order = order_main p.w_templates order_cmpoly ge_cmpoly eq_cmpoly

		method order_open = order_main p.w_templates order_open (>=^) (=^)

		method co_order = co_order_main p.w_templates order_cmpoly gt_cmpoly co_eq_cmpoly

		method co_order_open = co_order_main p.w_templates order_open (>^) (<>^)

		method quantify : 'f. (#Sym.named as 'f) list -> exp -> exp =
			if dim = 0 then
				fun vs e -> e
			else
				fun vs e ->
				if vs = [] then e
				else smt_context_for_all (
					fun context ->
					List.iter (fun v ->
						for i = 0 to dim-1 do
							add_svar context (v#name, i, range_of_coord i)
						done
					) vs;
					e
				)
	end



