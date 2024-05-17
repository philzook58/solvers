open Error
open Term
open Big_int

exception UninterpretedName of string * stp

let models_sofar = ref []

type frame_2 = string -> big_int
type interp_2_names = string -> stp -> big_int
type interp_2 = frame_2 * interp_2_names

let current_interp_2s_1 = ref []
let current_interp_2s_2 = ref []
let current_interp_2s_4 = ref []
let current_interp_2s () = !current_interp_2s_1 @ !current_interp_2s_2 @ !current_interp_2s_4
    
let rec frame_2_dom_logsize fr a =
  match a with
  | Ar(a1,a2) -> mult_big_int (frame_2_dom_logsize fr a2) (frame_2_dom_size fr a1)
  | Prop -> unit_big_int
  | Base(a) -> fr a
and frame_2_dom_size fr a = shift_left_big_int unit_big_int (int_of_big_int (frame_2_dom_logsize fr a))

let interp_2_ap c f a =
  let ci = int_of_big_int c in
  let ai = int_of_big_int a in
  mod_big_int (shift_right_towards_zero_big_int f (ci * ai)) (shift_left_big_int unit_big_int ci)

let interp_2_forall d p =
  try
    let di = int_of_big_int d in
    let n = shift_left_big_int unit_big_int di in
    let x = ref zero_big_int in
    while lt_big_int !x n do
      if eq_big_int zero_big_int (interp_2_ap d p !x) then raise Exit;
      x := succ_big_int !x
    done;
    true
  with Exit -> false

let rec eval_interp_2 (fr,inter) phi s =
  match s with
  | Name(x,a) -> inter x a
  | DB(i,a) -> List.nth phi i
  | Ap(Ap(Eq(a),s1),s2) -> if eq_big_int (eval_interp_2 (fr,inter) phi s1) (eval_interp_2 (fr,inter) phi s2) then unit_big_int else zero_big_int
  | Ap(Ap(Imp,s1),s2) -> if eq_big_int (eval_interp_2 (fr,inter) phi s1) zero_big_int then unit_big_int else eval_interp_2 (fr,inter) phi s2
  | Ap(Forall(a),Lam(_,s1)) -> interp_2_all (fr,inter) phi a s1
  | Ap(Choice(a),Lam(_,s1)) -> interp_2_choose (fr,inter) phi a s1
  | Lam(a,s1) -> interp_2_lam (fr,inter) phi a s1
  | Ap(s1,s2) ->
    begin
      match tpof s1 with
      | Ar(a,b) -> interp_2_ap (frame_2_dom_logsize fr b) (eval_interp_2 (fr,inter) phi s1) (eval_interp_2 (fr,inter) phi s2)
      | _ -> raise (Failure "Ill-typed term in eval_interp_2, non function applied to argument")
    end
  | False -> zero_big_int
  | Imp -> big_int_of_int 11
  | Forall(a) -> eval_interp_2 (fr,inter) phi (Lam(Ar(a,Prop),Ap(Forall(a),Lam(a,Ap(DB(1,Ar(a,Prop)),DB(0,a))))))
  | Eq(a) -> eval_interp_2 (fr,inter) phi (Lam(a,Lam(a,Ap(Ap(Eq(a),DB(1,a)),DB(0,a)))))
  | Choice(a) -> eval_interp_2 (fr,inter) phi (Lam(Ar(a,Prop),Ap(Choice(a),Lam(a,Ap(DB(1,Ar(a,Prop)),DB(0,a))))))
	(*** the remaining constructors should have been normalized away; do it now ***)
  | _ -> eval_interp_2 (fr,inter) phi (logicnorm s)
and interp_2_lam (fr,inter) phi a s =
  let an = int_of_big_int (frame_2_dom_size fr a) in
  let c = frame_2_dom_logsize fr (tpof s) in
  let ci = int_of_big_int c in
  let f = ref zero_big_int in
  let i = ref 0 in
  while !i < an do
    f := or_big_int !f (shift_left_big_int (eval_interp_2 (fr,inter) (big_int_of_int !i::phi) s) (!i * ci));
    incr i
  done;
  !f
and interp_2_all (fr,inter) phi a s =
  let an = int_of_big_int (frame_2_dom_size fr a) in
  let i = ref 0 in
  try
    while !i < an do
      if eq_big_int (eval_interp_2 (fr,inter) (big_int_of_int !i::phi) s) zero_big_int then raise Exit;
      incr i
    done;
    unit_big_int
  with Exit -> zero_big_int
and interp_2_choose (fr,inter) phi a s =
  let an = int_of_big_int (frame_2_dom_size fr a) in
  let i = ref 0 in
  try
    while !i < an do
      if eq_big_int (eval_interp_2 (fr,inter) (big_int_of_int !i::phi) s) unit_big_int then raise Exit;
      incr i
    done;
    zero_big_int
  with Exit -> big_int_of_int !i

let interp_2_search (fr,inter) phi a s =
  let an = int_of_big_int (frame_2_dom_size fr a) in
  let i = ref 0 in
  while !i < an do
    if !Log.verbosity > 39 then Printf.printf "%d |-> %s\n" !i (string_of_big_int (eval_interp_2 (fr,inter) (big_int_of_int !i::phi) s));
    incr i
  done

let print_semantic_value mn a v =
  Printf.printf "%s: %s\n" mn (string_of_big_int v)

let fr1 a = zero_big_int
let fr2 a = unit_big_int
let fr4 a = big_int_of_int 2

let empty_name_interp x a = raise (UninterpretedName(x,a))

let default_to_zero inter x a = try inter x a with UninterpretedName(_,_) -> zero_big_int

let print_interp_name_info cl inter =
  List.iter
    (fun (x,a) ->
      try
	let v = inter x a in
	Printf.printf "%s : %s |-> %s\n" x (stp_str a) (string_of_big_int v)
      with UninterpretedName(_,_) ->
	Printf.printf "%s : %s uninterpreted.\n" x (stp_str a))
    cl

let print_interp_trm_info p (fr,inter) =
  let cl = consts_of_trm [] p in
  Printf.printf "%s evaluates to %s with\n" (trm_str p)
    begin
      try
	string_of_big_int (eval_interp_2 (fr,inter) [] p)
      with UninterpretedName(_,_) -> "uninterpreted"
    end;
  List.iter
    (fun (x,a) ->
      try
	let v = inter x a in
	Printf.printf "%s : %s |-> %s\n" x (stp_str a) (string_of_big_int v)
      with UninterpretedName(_,_) ->
	Printf.printf "%s : %s uninterpreted.\n" x (stp_str a))
    cl

let rec search_interp_extensions_val_1 m v (fr,inter) n =
  if n > List.length !models_sofar then
    try
      if eq_big_int (eval_interp_2 (fr,inter) [] m) v then
	begin
	  if !Log.verbosity > 29 then (Printf.printf "Found interp with eval %s\n" (string_of_big_int v); flush stdout);
	  models_sofar := (fr,inter)::!models_sofar
	end
      else
	()
    with UninterpretedName(x,a) ->
      try
	if !Log.verbosity > 39 then (Printf.printf "Need interp of %s (up to %d of them)\n" x n; flush stdout);
	let z = int_of_big_int (frame_2_dom_size fr a) in
	if !Log.verbosity > 39 then (Printf.printf "considering %d possibilities\n" z; flush stdout);
	search_interp_extensions_val_2 m v (fr,inter) n x a z 0
      with Failure "int_of_big_int" -> ()
  else
    ()
and search_interp_extensions_val_2 m v (fr,inter) n x a z i =
  if n > List.length !models_sofar && i < z then
    let ii = big_int_of_int i in
    let interi = fun y b -> if y = x && b = a then ii else inter y b in
    if !Log.verbosity > 39 then (Printf.printf "Trying %s |-> %d\n" x i; flush stdout);
    search_interp_extensions_val_1 m v (fr,interi) n;
    search_interp_extensions_val_2 m v (fr,inter) n x a z (i+1)
  else
    ()

let search_interp_extensions_val m v (fr,inter) n =
  models_sofar := [];
  let (_,f) = set_sub_timer (Flags.get_float_flag "MODEL_SEARCH_TIMEOUT") in
  try
    search_interp_extensions_val_1 m v (fr,inter) n;
    f();
    !models_sofar
  with
  | Timeout -> !models_sofar
  | _ -> f(); !models_sofar (*** I'm primarily interested in catching Failure("int_of_big_int"), but catch all just in case. Call f() to pop out of the sub_timer ***)

let count_true_false_interps p interpl =
  List.fold_left
    (fun (nt,nf) m ->
      try
	if eq_big_int (eval_interp_2 m [] p) unit_big_int then (nt+1,nf) else (nt,nf+1)
      with _ -> (nt,nf))
    (0,0)
    interpl
