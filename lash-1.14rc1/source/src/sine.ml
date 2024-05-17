(* Lash *)
(* ported from Satallax file: sine.ml *)

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

let sine_loop_ratiolimit ratiolimit ratiolimitfactor occratio triggerreln (defs, axs, conjs) =
  let ratiolimit = ref (ratiolimit *. ratiolimitfactor) in
  let nametriggered : (string,int) Hashtbl.t = Hashtbl.create 200 in
  let itemtriggered : (string,int) Hashtbl.t = Hashtbl.create 200 in
  let triggername k ((defnxt, axnxt) as nxt) c =
    if Hashtbl.mem nametriggered c then
      nxt
    else
      begin
        try
          if k = 0 || Hashtbl.find occratio c < !ratiolimit then
            begin
              Hashtbl.add nametriggered c k;
              let defnxt' = if Hashtbl.mem defs c then c::defnxt else defnxt in
              let axnxt' = List.fold_left (fun acc ax -> ax :: acc) axnxt (Hashtbl.find_all triggerreln c) in
              (defnxt', axnxt')
            end
          else
            begin
              nxt
            end
        with Not_found ->
          nxt
      end
  in
  let triggeritem tbl k nxt x =
    if Hashtbl.mem itemtriggered x then
      nxt
    else
      begin
        Hashtbl.add itemtriggered x k;
        List.fold_left (triggername k) nxt (Hashtbl.find tbl x)
      end
  in
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
      ratiolimit := !ratiolimit *. ratiolimitfactor;
      iteration (k+1) defaxnxt2 in

  let defax0 =
    List.fold_left (fun acc (x,m,cl) ->
      List.fold_left (triggername 0) acc cl) ([], []) conjs in
  iteration 1 defax0

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
  let occratio : (string,float) Hashtbl.t = Hashtbl.create 200 in (*** ratio of occurrences of symbols over number of defs/axioms/conjecture **)
  let occ : (string,int) Hashtbl.t = Hashtbl.create 200 in (*** number of occurrences of symbols in defs/axioms/conjecture ***)
  let ignore_consts : (string,unit) Hashtbl.t = Hashtbl.create 200 in
  let register_consts m =
    List.map
      (fun (c, _) -> if not (Hashtbl.mem ignore_consts c) then add_occurrence c occ; c)
      (consts_of_trm [] m)
  in
  let defs = Hashtbl.create 100 in
  let axs = Hashtbl.create 100 in
  let conjs = ref [] in
  let ratiolimit = get_float_flag "SINE_RATIO_LIMIT" in
  let ratiodeflimit = get_float_flag "SINE_RATIO_DEF_LIMIT" in
  begin
    if ratiolimit > 0.0 then
      let dcnt = ref 0 in
      List.iter
        (fun z ->
          incr dcnt;
          match z with
          (*** Note: consts_of_trm does not contain duplicates, which is important for counting here ***)
          | ProbDef(x,_,m,_,_) ->
             Hashtbl.add defs x (register_consts m);
          | ProbAx(_,_,m,_,_) ->
	     ignore (register_consts m)
          | ProbConj(_,m,_,_) ->
	     ignore (register_consts m))
        ps;
      let dcntf = float_of_int !dcnt in
      Hashtbl.iter
        (fun c n ->
          let r = float_of_int n /. dcntf in
          if !verbosity > 20 then (Printf.printf "sine ratio %s: %f\n" c r);
          Hashtbl.add occratio c r;
          if r > (if Hashtbl.mem defs c then ratiodeflimit else ratiolimit) then
            (if !verbosity > 20 then (Printf.printf "so ignoring %s\n" c);
             Hashtbl.add ignore_consts c ()))
        occ;
      Hashtbl.clear occ;
  end;
  List.iter
    (fun z ->
      match z with
      (*** Note: consts_of_trm does not contain duplicates, which is important for counting here ***)
      | ProbDef(x,_,m,_,_) ->
	  Hashtbl.replace defs x (register_consts m)
      | ProbAx(x,_,m,_,_) ->
	  Hashtbl.add axs x (register_consts m)
      | ProbConj(x,m,_,_) ->
	  conjs := (x,m,(register_consts m))::!conjs)
    ps;
  let triggerreln = make_triggerreln occ axs in
  (*** The trigger relation on axioms is now defined. We will treat defns as follows: Defn of x is k+1 triggered if name x is k triggered. ***)
  let itemtriggered =
    if ratiolimit > 0.0 then
      let ratiolimitfactor = get_float_flag "SINE_RATIO_LIMIT_FACTOR" in
      if ratiolimitfactor = 1.0 then
        sine_loop triggerreln (defs, axs, !conjs)
      else
        sine_loop_ratiolimit ratiolimit ratiolimitfactor occratio triggerreln (defs, axs, !conjs)
    else
      sine_loop triggerreln (defs, axs, !conjs)
  in
  let l = List.length ps in
  let wl = Array.make l 0.0 in
  let f x i w =
    if !verbosity > 4 then (Printf.printf "Sinelike rank of %s: %f\n" x w; flush stdout);
    wl.(i) <- w;
    w
  in
  if get_bool_flag "SINE_RATIO_TRIGGER_EXP" then
    begin
      let e x m k =
        let mx = ref 10.0 in
        List.iter
          (fun (c, _) ->
            try
              let r = Hashtbl.find occratio c in
              mx := min !mx r
            with Not_found -> ())
          (consts_of_trm [] m);
        if !mx > 0.0 then
          exp (log !mx *. (float_of_int k))
        else
          0.0
      in
      if get_bool_flag "SINE_RATIO_TRIGGER_EXP_MIN" then
        List.mapi
          (fun i z ->
            match z with
            | ProbDef(x,a,m1,al,w) -> ProbDef(x,a,m1,al,f x i (try let k = Hashtbl.find itemtriggered x in try min (e x m1 k) (float_of_int k) with Not_found -> float_of_int k with Not_found -> 1000000.0))
            | ProbAx(x,r,m1,al,w) -> ProbAx(x,r,m1,al,f x i (try let k = Hashtbl.find itemtriggered x in try min (e x m1 k) (float_of_int k) with Not_found -> float_of_int k with Not_found -> 1000000.0))
            | ProbConj(x,m1,al,w) -> ProbConj(x,m1,al,f x i 0.0))
          ps
      else
        List.mapi
          (fun i z ->
            match z with
            | ProbDef(x,a,m1,al,w) -> ProbDef(x,a,m1,al,f x i (try e x m1 (Hashtbl.find itemtriggered x)  with Not_found -> 1000000.0))
            | ProbAx(x,r,m1,al,w) -> ProbAx(x,r,m1,al,f x i (try e x m1 (Hashtbl.find itemtriggered x) with Not_found -> 1000000.0))
            | ProbConj(x,m1,al,w) -> ProbConj(x,m1,al,f x i 0.0))
          ps
    end
  else
    List.mapi
      (fun i z ->
        match z with
        | ProbDef(x,a,m1,al,w) -> ProbDef(x,a,m1,al,f x i (try float_of_int (Hashtbl.find itemtriggered x)  with Not_found -> 1000000.0))
        | ProbAx(x,r,m1,al,w) -> ProbAx(x,r,m1,al,f x i (try float_of_int (Hashtbl.find itemtriggered x) with Not_found -> 1000000.0))
        | ProbConj(x,m1,al,w) -> ProbConj(x,m1,al,f x i 0.0))
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
