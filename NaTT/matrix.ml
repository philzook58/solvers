open Util

let trans =
	let rec sub ret =
		function
		| [] -> ret
		| row::mat -> sub (List.map2 (fun x xs -> x::xs) row ret) mat
	in
	function
	| [] -> []
	| row::_ as mat -> sub (List.map (fun _ -> []) row) (List.rev mat)

let inner_prod add mul zero =
	List.fold_left2 (fun ret e1 e2 -> add ret (mul e1 e2)) zero

let prod_vec add mul zero m v =
	List.map (inner_prod add mul zero v) m

let prod add mul zero m n =
	List.map (prod_vec add mul zero (trans n)) m

let sum_vec adder = List.map2 adder
let sum adder = List.map2 (sum_vec adder)

let diag_elems m =
	let rec sub i =
		function
		| [] -> []
		| m_i::m -> List.nth m_i i :: sub (i+1) m
	in
	sub 0 m

let foldij =
	let rec subj i j f ret =
		function
		| [] -> ret
		| m_ij::m_i -> subj i (j+1) f (f ret i j m_ij) m_i
	in
	let rec subi i f ret =
		function
		| [] -> ret
		| m_i::m -> subi (i+1) f (subj i 0 f ret m_i) m
	in
	fun f ret m -> subi 0 f ret m
let fold f = foldij (fun ret _ _ -> f ret)

let foldij2 =
	let rec subj i j f ret m n =
		match m, n with
		| [],[] -> ret
		| (m_ij::m_i), (n_ij::n_i) -> subj i (j+1) f (f ret i j m_ij n_ij) m_i n_i
		| _ -> raise (Internal "Matrix.foldij2")
	in
	let rec subi i f ret m n =
		match m, n with
		| [],[] -> ret
		| (m_i::m), (n_i::n) -> subi (i+1) f (subj i 0 f ret m_i n_i) m n
		| _ -> raise (Internal "Matrix.foldij2")
	in
	fun f ret m -> subi 0 f ret m
let fold2 f = foldij2 (fun ret _ _ -> f ret)

let is_zero zero =
	foldij (fun ret _ _ m_ij -> ret && m_ij = zero) true
let is_unit zero unit =
	foldij (fun ret i j m_ij -> ret && m_ij = (if i = j then unit else zero)) true
let is_zero_vec zero =
	List.for_all (fun v_i -> v_i = zero)

let mapij f =
	let rec subi i =
		function
		| [] -> []
		| m_i::m -> subj i 0 m_i :: subi (i+1) m
	and subj i j =
		function
		| [] -> []
		| m_ij::m_i -> f i j m_ij :: subj i (j+1) m_i
	in
	subi 0
