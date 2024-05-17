(* Lash *)
(* ported from Satallax file: searchoption.ml *)

open Flags
open Error
open Syntax
open Log

type searchoption =
 (*** ProcessProp1(m) might make pattern clauses and otherwise expands any remaining translucent defns leaving ProcessProp2 to apply the real rule ***)
    ProcessProp1 of ftm
 (*** ProcessProp2(m) For rules requiring one formula in the head (most rules) ***)
  | ProcessProp2 of ftm
 (*** Mating(plit,nlit,pl,nl) where pl,nl and plit = lit (h pl) and nlit = lit ~(h nl) ***)
  | Mating of int * int * stp * ftm list * ftm list
  | MatingList of int * ftm list * stp * (int * ftm list) list * bool
 (*** Confront(nplit,nnlit,a,u,v,l,r) where u,v,l,r:a and nplit = lit (u = v) and nnlit is lit (l != r) ***)
  | Confront of int * int * int * ftm * ftm * ftm * ftm
  | ConfrontList of int * int * ftm * ftm * (int * ftm * ftm) list * bool
 (*** DefaultElt(a) - create a default element of type a ***)
  | DefaultElt of int
 (*** DefaultEltInst(a) - create a default element of type a ***)
  | DefaultEltInst of int
 (*** NewInst(a,m) - put m:a in the set of instantiations ***)
  | NewInst of int * ftm
  (*** EnumInst enumerate the nth term to use as instantiation ***)
  | EnumInst of stp * int
 (*** Filter - use Minisat to filter usable sets ***)
  | Filter of int

let max_searchoptions = ref None
let searchoptions_retrieved = ref 0

(*** For printing a searchoption - helpful for debugging. - Chad, Oct 2010 ***)
let searchoption_str s =
  match s with
  | ProcessProp1(m) -> ("ProcessProp1(" ^ (ftm_str m) ^ ")")
  | ProcessProp2(m) -> ("ProcessProp2(" ^ (ftm_str m) ^ ")")
  | Mating(plit,nlit,_,pl,nl) -> "Mating(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ " -- " ^ (String.concat "," (List.map ftm_str pl)) ^ " -- " ^ (String.concat "," (List.map ftm_str nl)) ^  ")"
  | MatingList(plit,nlit,_,pl,nl) -> "MatingList..."
  | Confront(plit,nlit,a,s,t,u,v) -> "Confront(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | ConfrontList(ty,lit,t1,t2,l,listpos) -> "ConfrontList..."
  | DefaultElt(a) -> "DefaultElt(" ^ Term.no_basename a ^ ")"
  | DefaultEltInst(a) -> "DefaultEltInst(" ^ Term.no_basename a ^ ")"
  | EnumInst(a,n) -> "EnumInst(" ^ (stp_str a) ^ "," ^ (string_of_int n) ^ ")"
  | NewInst(_,m) -> "NewInst(" ^ (ftm_str m) ^ ")"
  | Filter(d) -> "Filter(" ^ (string_of_int d) ^ ")"

let ftm_list_size = List.fold_left (fun s e -> s + Ftm.size e) 0;;
let ftm_list_max = List.fold_left (fun s e -> max s (Ftm.size e)) 0;;
let ilog i = int_of_float (log (float_of_int (1 + i)))

let searchoption_priority oldp = function
  | ProcessProp1(m) | ProcessProp2(m) -> ilog (Ftm.size m)
  | _ -> 5 + oldp;;

                (*
let adaptPriorityModels n dt df du o =
  match o with
  | ProcessProp1 p ->
      let (mt,mf) = Models.count_true_false_interps p (List.map (fun (frint,_) -> frint) (Models.current_interp_2s())) in
      if !verbosity > 5 then Printf.printf "Proposition %s true in %d models and false in %d models.\n" (trm_str p) mt mf;
      n + dt * mt + df * mf + if mt = 0 || mf = 0 then du else 0
  | _ -> n
                 *)

(* Priority Queues *)
type pq;;
external pq_make : unit -> pq = "c_pq_make";;
external pq_push : pq -> int -> unit = "c_pq_push" [@@noalloc];;
external pq_top : pq -> int  = "c_pq_top"  [@@noalloc];;
external pq_pop : pq -> unit = "c_pq_pop"  [@@noalloc];;

let pq = pq_make ();;

(*** Version 0: Same priorities treated as stacks. Fairness ensured with an offset incremented every 2^logomodulus inserts. ***)
let pqueue_offset = ref 0;;

let (stack_data : (searchoption list) Vector.t) = Vector.make 256 [];;
let rec stack_reset () =
  let p = pq_top pq in
  if p >= 0 then begin
      pq_pop pq;
      Vector.set stack_data p [];
      stack_reset ()
    end

let stack_insert logmodulus p o =
  let p = p + ((!pqueue_offset) asr logmodulus) in
  incr pqueue_offset;
  let upd_fun_s = function
    | [] -> pq_push pq p; [o]
    | v -> o :: v
  in
  Vector.update stack_data p upd_fun_s

let stack_pop () =
  let p = pq_top pq in
  if p = -1 then raise Not_found;
  p, match Vector.get stack_data p with
     | [h] -> pq_pop pq; Vector.set stack_data p []; h
     | h :: t -> Vector.set stack_data p t; h
     | [] -> assert false

let stack_peek () =
  let p = pq_top pq in
  if p = -1 then raise Not_found else p

(*** Version 1: Same priorities treated as queues. Fairness ensured with an offset incremented every 2^logmodulus inserts. ***)
type l2 = L2 of searchoption list * searchoption list
let (queue_data : l2 Vector.t) = Vector.make 256 (L2 ([], []))

let rec queue_reset () =
  let p = pq_top pq in
  if p >= 0 then begin
    pq_pop pq;
    Vector.set queue_data p (L2 ([], []));
    queue_reset ()
  end

let queue_insert logmodulus p o =
  let p = p + ((!pqueue_offset) asr logmodulus) in
  incr pqueue_offset;
  let upd_fun_q = function
    | L2 ([], []) -> pq_push pq p; L2 ([o], [])
    | L2 (l, r) -> L2 (l, o :: r)
  in
  Vector.update queue_data p upd_fun_q

let queue_get () =
  let p = pq_top pq in
  if p = -1 then raise Not_found;
  p, match Vector.get queue_data p with
  | L2 ([h], []) | L2 ([], [h]) ->
     pq_pop pq; Vector.set queue_data p (L2 ([], [])); h
  | L2 (h :: t, r) ->
     Vector.set queue_data p (L2 (t, r)); h
  | L2 ([], l) ->
     match List.rev l with
     | h :: t -> Vector.set queue_data p (L2 (t, [])); h
     | _ -> assert false

let queue_peek () =
  let p = pq_top pq in
  if p = -1 then raise Not_found else p;;

(* FIFO *)

let l1 = ref [] and l2 = ref [];;
let fifo_insert o = l2 := o :: !l2;;
let rec fifo_get () =
  match !l1 with
  | h :: t ->
     l1 := t; 0, h
  | [] ->
     match !l2 with
     | [] -> raise Not_found
     | _ -> l1 := List.rev !l2; l2 := []; fifo_get ();;
let fifo_peek () = match !l1, !l2 with [], [] -> raise Not_found | _ -> 0;;
let fifo_reset () = l1 := []; l2 := [];;

(* Dual-Queue *)
type l2r = L2r of (searchoption option ref) list * (searchoption option ref) list
let (queue_data : l2r Vector.t) = Vector.make 256 (L2r ([], []))
let l1 = ref [] and l2 = ref [];;

let dualq_reset () =
  l1:=[]; l2:=[];
  let rec qreset () =
    let p = pq_top pq in
    if p >= 0 then begin
      pq_pop pq;
      Vector.set queue_data p (L2r ([], []));
      qreset ()
    end
  in qreset ();;

let dualqpush p o =
  let item = ref (Some o) in
  l2 := item :: !l2;
  let upd_fun_q = function
    | L2r ([], []) -> pq_push pq p; L2r ([item], [])
    | L2r (l, r) -> L2r (l, item :: r)
  in
  Vector.update queue_data p upd_fun_q;;

let counter = ref 0;;

let rec dualq_fifopop () =
  match !l1 with
  | item :: t ->
     begin match !item with
     | None -> l1 := t; dualq_fifopop ()
     | Some h -> item := None; l1 := t; 0, h
     end
  | [] ->
     match !l2 with
     | [] -> raise Not_found
     | _ -> l1 := List.rev !l2; l2 := []; dualq_fifopop ();;


let rec dualq_queuepop () =
  let give_option p r =
    match !r with
    | Some h -> r := None; p, h
    | None -> dualq_queuepop ()
  in
  let p = pq_top pq in
  if p = -1 then raise Not_found;
  match Vector.get queue_data p with
  | L2r ([h], []) | L2r ([], [h]) ->
     pq_pop pq; Vector.set queue_data p (L2r ([], [])); give_option p h
  | L2r (h :: t, r) ->
     Vector.set queue_data p (L2r (t, r)); give_option p h
  | L2r ([], l) ->
     match List.rev l with
     | h :: t -> Vector.set queue_data p (L2r (t, [])); give_option p h
     | _ -> assert false;;

let dualq_pop () =
  let ret =
    if !fiDUALQUEUE_MOD > 0 then (* Mostly by priority, rarely oldest *)
      if (!counter mod !fiDUALQUEUE_MOD) = 0 then dualq_fifopop () else dualq_queuepop ()
    else
      if (!counter mod -(!fiDUALQUEUE_MOD)) = 0 then dualq_queuepop () else dualq_fifopop ()
  in
  incr counter; ret;;


(* Dual-Stack *)
let (stack_data : (searchoption option ref list) Vector.t) = Vector.make 256 [];;
let l1 = ref [] and l2 = ref [];;

let duals_reset () =
  l1:=[]; l2:=[];
  let rec sreset () =
    let p = pq_top pq in
    if p >= 0 then begin
      pq_pop pq;
      Vector.set stack_data p [];
      sreset ()
    end
  in sreset ();;

let duals_push p o =
  let item = ref (Some o) in
  l2 := item :: !l2;
  let upd_fun_s = function
    | [] -> pq_push pq p; [item]
    | v -> item :: v
  in
  Vector.update stack_data p upd_fun_s;;

let counter = ref 0;;

let rec duals_fifopop () =  (* Identical code to dualq_fifopop, but refers to other datastrucutes *)
  match !l1 with
  | item :: t ->
     begin match !item with
     | None -> l1 := t; duals_fifopop ()
     | Some h -> item := None; l1 := t; 0, h
     end
  | [] ->
     match !l2 with
     | [] -> raise Not_found
     | _ -> l1 := List.rev !l2; l2 := []; duals_fifopop ();;

let rec duals_stackpop () =
  let give_option p r =
    match !r with
    | Some h -> r := None; p, h
    | None -> duals_stackpop ()
  in
  let p = pq_top pq in
  if p = -1 then raise Not_found;
  match Vector.get stack_data p with
  | [h] -> pq_pop pq; Vector.set stack_data p []; give_option p h
  | h :: t -> Vector.set stack_data p t; give_option p h
  | [] -> assert false;;

let duals_pop () =
  let ret =
    if !fiDUALQUEUE_MOD > 0 then (* Mostly by priority, rarely oldest *)
      if (!counter mod !fiDUALQUEUE_MOD) = 0 then duals_fifopop () else duals_stackpop ()
    else
      if (!counter mod -(!fiDUALQUEUE_MOD)) = 0 then duals_stackpop () else duals_fifopop ()
  in
  incr counter; ret;;

(* - *)

let insertWithPriority n o =
  match o with
  | ProcessProp1(m) when Ftm.processed_mem m -> ()
  | _ ->
     let n = if n < 0 then 0 else n in
     if (!verbosity > 8) then Printf.printf "Inserting option with priority %d: %s\n" n (searchoption_str o);
     match !fiPRIORITY_QUEUE_IMPL with
     | 0 -> stack_insert 10 n o
     | 1 -> queue_insert 10 n o
     | 2 -> dualqpush (searchoption_priority n o) o
     | 3 -> fifo_insert o
     | 10 -> dualqpush n o
     | 11 -> queue_insert 10 (searchoption_priority n o) o
     | 4 -> stack_insert  9 n o
     | 5 -> stack_insert  8 n o
     | 6 -> stack_insert  7 n o
     | 7 -> stack_insert  6 n o
     | 8 -> queue_insert  5 n o
     | 9 -> queue_insert 20 (searchoption_priority n o) o
     | 12 -> duals_push (searchoption_priority n o) o
     | _ -> assert false

let getNext () =
  let ret =
    match !fiPRIORITY_QUEUE_IMPL with
    | 1 | 11 | 8 | 9 -> queue_get ()
    | 2 | 10 -> dualq_pop ()
    | 3 -> fifo_get ()
    | 0 | 4 | 5 | 6 | 7 -> stack_pop ()
    | 12 -> duals_pop ()
    | n -> raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n)))
  in
  if (!verbosity > 49) then (Printf.printf "Got next option: %s\n" (searchoption_str (snd ret)));
  incr searchoptions_retrieved;
  (match !max_searchoptions with Some m when !searchoptions_retrieved >= m -> raise Timeout
  | _ -> ());
  ret

let peekAtNext () =
  match !fiPRIORITY_QUEUE_IMPL with
  | 1 | 11 | 8 | 9 -> queue_peek ()
  | 2 | 10 | 12 -> failwith "unimplemented"
  | 3 -> fifo_peek ()
  | 0 | 4 | 5 | 6 | 7 -> stack_peek ()
  | n -> raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n)))

let reset_pqueues () =
  match !fiPRIORITY_QUEUE_IMPL with
  | 1 | 8 | 9 | 11 -> queue_reset ()
  | 2 | 10 -> dualq_reset ()
  | 3 -> fifo_reset ()
  | 0 | 4 | 5 | 6 | 7 -> stack_reset ()
  | 12 -> duals_reset ()
  | _ -> assert false
