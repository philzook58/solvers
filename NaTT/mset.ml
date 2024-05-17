
module M = Map.Make(String)

let empty = M.empty

let count x m = try M.find x m with Not_found -> 0

let add_many x n m = M.add x (count x m + n) m

let add x = add_many x 1

let of_list = List.fold_left (fun m x -> add x m) empty

let union =
	M.merge
	(	fun k xopt yopt ->
			match xopt, yopt with
			| None, None -> None
			| Some n, None -> Some n
			| None, Some m -> Some m
			| Some n, Some m -> Some (n+m)
	)

let singleton x = M.singleton x 1

(* multi-subseteq relation *)
let subseteq m1 m2 = M.for_all (fun x n -> n <= count x m2) m1

let supseteq m1 m2 = subseteq m2 m1

let join =
	M.merge
	(	fun k (xopt:int option) yopt ->
			match xopt, yopt with
			| None, None -> None
			| Some n, None -> Some n
			| None, Some m -> Some m
			| Some n, Some m -> Some (if n > m then n else m)
	)

let iter = M.iter

let output_mset os m =
	let iterer x n =
		output_string os x;
		output_string os "=";
		output_string os (string_of_int n);
		output_string os "; ";
	in
	output_string os "{ ";
	iter iterer m;
	output_string os "}";;
let prerr_mset = output_mset stderr
