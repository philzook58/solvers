open State
open Term
open Log
open Flags

(*
let sine_tolerance_vary = ref true
let sine_generality_threshold_vary = ref true
let sine_tolerance = ref 1.2 (*** can be set by command line --sine_tolerance t where t should >= 1.0; if none is set then slice over different values. ***)
let sine_depth = ref None (*** can be set by command line --sine_depth d where d should be an >= 0.0; if none is set then slice over different depths (more or less) ***)
let sine_generality_threshold = ref 0 (*** can be set by command line --sine_generality_threshold g; where g should be an integer >= 0 ***)
*)

(*
let set_sine_tolerance t =
  if t >= 1.0
  then begin
    sine_tolerance := t;
    sine_tolerance_vary := false
  end
  else
    raise (Failure "sine tolerance must be >= 1.0")

let set_sine_generality_threshold g =
  if g >= 0
  then begin
    sine_generality_threshold := g;
    sine_generality_threshold_vary := false
  end
  else
    raise (Failure "sine generality threshold must be >= 0")
*)

let add_occurrence c occ =
  try Hashtbl.replace occ c (1 + (Hashtbl.find occ c))
  with Not_found -> Hashtbl.add occ c 1

let make_triggerreln occ axs =
  let triggerreln : (string,string) Hashtbl.t = Hashtbl.create 200 in (*** const names map to axiom names they trigger ***)
  let update_triggerreln c ax =
    if !verbosity > 4 then Printf.printf "%s triggers axiom %s\n" c ax;
    Hashtbl.add triggerreln c ax in
  let sine_tolerance = get_float_flag "SINE_TOLERANCE" in
  let sine_generality_threshold = get_int_flag "SINE_GENERALITY_THRESHOLD" in
  if !verbosity > 4 then
    Printf.printf "Sine t = %f, g = %d\n" sine_tolerance sine_generality_threshold;
  let update_occurrence_bound (col, bd) c =
    try
      let oi = Hashtbl.find occ c in
      let o = float_of_int oi in
      (* the final bd will have the form: !sine_tolerance**n *. o, where
       * n is a natural > 0 and o is the occurrence of some constant *)
      let bd' = match bd with
      | None -> sine_tolerance *. o
      | Some bd -> min (sine_tolerance *. o) (sine_tolerance *. bd) in
      ((c,oi,o)::col, Some bd')
    with Not_found -> (col, bd) in
  let treat_axiom ax cl =
    match List.fold_left update_occurrence_bound ([], None) cl with
    | (col, Some bd) ->
        List.iter
          (fun (c,oi,o) ->
            if oi <= sine_generality_threshold || o <= bd
            then update_triggerreln c ax) col
    | _ -> () in
  Hashtbl.iter treat_axiom axs;
  triggerreln

let sine_loop triggerreln (defs, axs, conjs) =
  let nametriggered : (string,int) Hashtbl.t = Hashtbl.create 200 in
  let itemtriggered : (string,int) Hashtbl.t = Hashtbl.create 200 in
  let triggername k ((defnxt, axnxt) as nxt) c =
    if Hashtbl.mem nametriggered c then nxt
    else begin
      Hashtbl.add nametriggered c k;
      let defnxt' = if Hashtbl.mem defs c then c::defnxt else defnxt in
      let axnxt' = List.fold_left (fun acc ax -> ax :: acc) axnxt (Hashtbl.find_all triggerreln c) in
      (defnxt', axnxt')
    end in
  let triggeritem tbl k nxt x =
    if Hashtbl.mem itemtriggered x then nxt
    else begin
      Hashtbl.add itemtriggered x k;
      List.fold_left (triggername k) nxt (Hashtbl.find tbl x)
    end in
  let sine_depth = get_int_flag "SINE_DEPTH" in
  let rec iteration k = function
  | ([], []) -> itemtriggered
  | defax ->
      let (def, ax) =
        match sine_depth with
        | 0 -> defax
        | d -> if d < k then ([], []) else defax in (*** stop computation prematurely because of explicit depth restriction ***)
      let defaxnxt1 = List.fold_left (triggeritem defs k) ([],  []) def in
      let defaxnxt2 = List.fold_left (triggeritem  axs k) defaxnxt1  ax in
      iteration (k+1) defaxnxt2 in

  let defax0 =
    List.fold_left (fun acc (x,m,cl) ->
      List.fold_left (triggername 0) acc cl) ([], []) conjs in
  iteration 1 defax0

let sinelike_premsel ps = (*** based on Hoder Voronkov CADE-23 2011 ***)
  let occ : (string,int) Hashtbl.t = Hashtbl.create 200 in (*** number of occurrences of symbols in defs/axioms/conjecture ***)
  let register_consts m =
    List.map (fun (c, _) -> add_occurrence c occ; c) (consts_of_trm [] m) in
  let defs = Hashtbl.create 100 in
  let axs = Hashtbl.create 100 in
  let conjs = ref [] in
  List.iter
    (fun z ->
      match z with
      (*** Note: consts_of_trm does not contain duplicates, which is important for counting here ***)
      | ProbDef(x,_,m,_,_) ->
	  Hashtbl.add defs x (register_consts m)
      | ProbAx(x,_,m,_,_) ->
	  Hashtbl.add axs x (register_consts m)
      | ProbConj(x,m,_,_) ->
	  conjs := (x,m,(register_consts m))::!conjs)
    ps;
  let triggerreln = make_triggerreln occ axs in
  (*** The trigger relation on axioms is now defined. We will treat defns as follows: Defn of x is k+1 triggered if name x is k triggered. ***)
  (*
  let nametriggered : (string,int) Hashtbl.t = Hashtbl.create 200 in
  let itemtriggered : (string,int) Hashtbl.t = Hashtbl.create 200 in
  let defnxt = ref [] in
  let axnxt = ref [] in
  let triggername c k =
    if not (Hashtbl.mem nametriggered c) then
      begin
	Hashtbl.add nametriggered c k;
	if Hashtbl.mem defs c then defnxt := c::!defnxt;
	List.iter
	  (fun ax -> axnxt := ax::!axnxt)
	  (Hashtbl.find_all triggerreln c)
      end
  in
  List.iter
    (fun (x,m,cl) -> List.iter (fun c -> triggername c 0) cl)
    !conjs;
  let k = ref 0 in
  let sine_depth = get_int_flag "SINE_DEPTH" in
  while not (!defnxt = [] && !axnxt = []) do
    incr k;
    begin
      match sine_depth with
      | 0 -> ()
      | d -> if d < !k then (defnxt := []; axnxt := []) (*** stop computation prematurely because of explicit depth restriction ***)
    end;
    let defnxt2 = !defnxt in
    let axnxt2 = !axnxt in
    defnxt := [];
    axnxt := [];
    List.iter
      (fun x ->
	if not (Hashtbl.mem itemtriggered x) then
	  begin
	    Hashtbl.add itemtriggered x !k;
	    List.iter (fun c -> triggername c !k) (Hashtbl.find defs x)
	  end)
      defnxt2;
    List.iter
      (fun x ->
	if not (Hashtbl.mem itemtriggered x) then
	  begin
	    Hashtbl.add itemtriggered x !k;
	    List.iter (fun c -> triggername c !k) (Hashtbl.find axs x)
	  end)
      axnxt2;
  done;
  *)
  let itemtriggered = sine_loop triggerreln (defs, axs, !conjs) in
  let l = List.length ps in
  let wl = Array.make l 0.0 in
  let f x i w =
    if !verbosity > 4 then (Printf.printf "Sinelike rank of %s: %f\n" x w; flush stdout);
    wl.(i) <- w;
    w
  in
  List.mapi
    (fun i z ->
      match z with
      | ProbDef(x,a,m,al,w) -> ProbDef(x,a,m,al,f x i (try float_of_int (Hashtbl.find itemtriggered x) with Not_found -> 1000000.0))
      | ProbAx(x,r,m,al,w) -> ProbAx(x,r,m,al,f x i (try float_of_int (Hashtbl.find itemtriggered x) with Not_found -> 1000000.0))
      | ProbConj(x,m,al,w) -> ProbConj(x,m,al,f x i 0.0))
    ps

(*
let with_sine_params t g f =
  let fullprobsig = !probsig in
  if !sine_tolerance_vary then sine_tolerance := t;
  if !sine_generality_threshold_vary then sine_generality_threshold := g;
  try
    f();
    probsig := fullprobsig
  with e ->
    probsig := fullprobsig;
    raise e

*)
