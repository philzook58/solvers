open Flags
open Priorityqueue
open Error
open Syntax
open Log

type searchoption =
 (*** ProcessProp1(m) might make pattern clauses and otherwise expands any remaining translucent defns leaving ProcessProp2 to apply the real rule ***)
    ProcessProp1 of trm
 (*** ProcessProp2(m) For rules requiring one formula in the head (most rules) ***)
  | ProcessProp2 of trm
 (*** Mating(plit,nlit,pl,nl) where pl,nl and plit = lit (h pl) and nlit = lit ~(h nl) ***)
  | Mating of int * int * trm list * trm list
 (*** Confront(nplit,nnlit,a,s,t,u,v) where s,t,u,v:a and nplit = lit (s = t) and nnlit is lit (u != v) ***)
  | Confront of int * int * stp * trm * trm * trm * trm
 (*** DefaultElt(a) - create a default element of type a ***)
  | DefaultElt of string
 (*** DefaultEltInst(a) - create a default element of type a ***)
  | DefaultEltInst of string
 (*** NewInst(a,m) - put m:a in the set of instantiations ***)
  | NewInst of stp * trm
 (*** EnumIterDeep(d,a) - Enumerate all terms (using the current constants) of depth d ***)
  | EnumIterDeep of int * stp
 (*** EnumTp(d,ar,a) - work on enumerating types that can be used to choose a polymorphic head (Eq, Forall, Choice) ***)
  | EnumTp of int * stp * stp
 (*** EnumAp(d,Gamma,sigmal,h,c) - ***)
  | EnumAp of (int * stp list * stp list * trm * (trm -> unit))
 (*** Enum(d,Gamma,sigma,c) ***)
  | Enum of (int * stp list * stp * (trm -> unit))
 (*** Filter - use Minisat to filter usable sets ***)
  | Filter of int

let max_searchoptions = ref None
let searchoptions_retrieved = Queue.create ()

(*** For printing a searchoption - helpful for debugging. - Chad, Oct 2010 ***)
let searchoption_str s =
  match s with
  | ProcessProp1(m) -> ("ProcessProp1(" ^ (trm_str m) ^ ")")
  | ProcessProp2(m) -> ("ProcessProp2(" ^ (trm_str m) ^ ")")
  | Mating(plit,nlit,pl,nl) -> "Mating(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ " -- " ^ (String.concat "," (List.map trm_str pl)) ^ " -- " ^ (String.concat "," (List.map trm_str nl)) ^  ")"
  | Confront(plit,nlit,a,s,t,u,v) -> "Confront(" ^ (string_of_int plit) ^ "," ^ (string_of_int nlit) ^ ")"
  | DefaultElt(a) -> "DefaultElt(" ^ a ^ ")"
  | DefaultEltInst(a) -> "DefaultEltInst(" ^ a ^ ")"
  | EnumIterDeep(d,a) -> "EnumIterDeep(" ^ (string_of_int d) ^ "," ^ (stp_str a) ^ ")"
  | EnumTp(d,_,a) -> "EnumTp(" ^ (string_of_int d) ^ "," ^ (stp_str a) ^ ")"
  | EnumAp(d,gamma,sigmal,h,_) -> "EnumAp(" ^ (string_of_int d) ^ "," ^ (String.concat ";" (List.map stp_str gamma)) ^ "," ^ (String.concat ";" (List.map stp_str sigmal)) ^ "," ^ (trm_str h) ^ ")"
  | Enum(d,gamma,sigma,_) -> "Enum(" ^ (string_of_int d) ^ "," ^ (String.concat ";" (List.map stp_str gamma)) ^ "," ^ (stp_str sigma) ^ ")"
  | NewInst(_,m) -> "NewInst(" ^ (trm_str m) ^ ")"
  | Filter(d) -> "Filter(" ^ (string_of_int d) ^ ")"
(***  | _ -> "OtherSearchOption" (*** to do: the rest if we need them ***) ***)


(*** Different Implementations of Fair Priority Queues ***)
module PQueue0 = PriorityQueue0 (struct type t = searchoption end)
module PQueue1 = PriorityQueue1 (struct type t = searchoption end)
(*** PriorityQueue2 deleted due to unfairness bug ***)
module PQueue3 = PriorityQueue3 (struct type t = searchoption end)
module PQueue4 = PriorityQueue4 (struct type t = searchoption end)
module PQueue5 = PriorityQueue5 (struct type t = searchoption end)
module PQueue6 = PriorityQueue6 (struct type t = searchoption end)
module PQueue7 = PriorityQueue7 (struct type t = searchoption end)
module PQueue8 = PriorityQueue8 (struct type t = searchoption end)
module PQueue9 = PriorityQueue9 (struct type t = searchoption end)
module PQueue10 = PriorityQueue10 (struct type t = searchoption end)

let adaptPriorityModels n dt df du o =
  match o with
  | ProcessProp1 p ->
      let (mt,mf) = Models.count_true_false_interps p (List.map (fun (frint,_) -> frint) (Models.current_interp_2s())) in
      if !verbosity > 5 then Printf.printf "Proposition %s true in %d models and false in %d models.\n" (trm_str p) mt mf;
      n + dt * mt + df * mf + if mt = 0 || mf = 0 then du else 0
  | _ -> n

let insertWithPriority n o =
  let (ins,dp) =
    begin
      match !fiPRIORITY_QUEUE_IMPL with
      | 0 -> (PQueue0.insertWithPriority,PQueue0.debug_print)
      | 1 -> (PQueue1.insertWithPriority,PQueue1.debug_print)
      |	3 -> (PQueue3.insertWithPriority,PQueue3.debug_print)
      |	4 -> (PQueue4.insertWithPriority,PQueue4.debug_print)
      |	5 -> (PQueue5.insertWithPriority,PQueue5.debug_print)
      |	6 -> (PQueue6.insertWithPriority,PQueue6.debug_print)
      |	7 -> (PQueue7.insertWithPriority,PQueue7.debug_print)
      |	8 -> (PQueue8.insertWithPriority,PQueue8.debug_print)
      |	9 -> (PQueue9.insertWithPriority,PQueue9.debug_print)
      |	10 -> (PQueue10.insertWithPriority,PQueue10.debug_print)
      | n -> (raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n))))
    end
  in
  begin
    let dtim = !fiDELAY_TRUE_IN_MODELS in
    let dfim = !fiDELAY_FALSE_IN_MODELS in
    let duim = !fiDELAY_UNINFORMATIVE_IN_MODELS in
    let prio = if dtim > 0 || dfim > 0 then adaptPriorityModels n dtim dfim duim o else n in
    if (!verbosity > 8) then Printf.printf "Inserting option with priority %d: %s\n" prio (searchoption_str o);
    ins prio o;
    if (!verbosity > 49) then dp searchoption_str
  end

let getNext () =
  let (gn,dp) =
    begin
      match !fiPRIORITY_QUEUE_IMPL with
      | 0 -> (PQueue0.getNext,PQueue0.debug_print)
      | 1 -> (PQueue1.getNext,PQueue1.debug_print)
      |	3 -> (PQueue3.getNext,PQueue3.debug_print)
      |	4 -> (PQueue4.getNext,PQueue4.debug_print)
      |	5 -> (PQueue5.getNext,PQueue5.debug_print)
      |	6 -> (PQueue6.getNext,PQueue6.debug_print)
      |	7 -> (PQueue7.getNext,PQueue7.debug_print)
      |	8 -> (PQueue8.getNext,PQueue8.debug_print)
      |	9 -> (PQueue9.getNext,PQueue9.debug_print)
      |	10 -> (PQueue10.getNext,PQueue10.debug_print)
      | n -> (raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n))))
    end
  in
  if (!verbosity > 49) then (Printf.printf "About to get next option:\n"; dp searchoption_str);
  let o = gn()
  in
  if (!verbosity > 49) then (Printf.printf "After removing option:\n"; dp searchoption_str);
  Queue.add o searchoptions_retrieved;
  (match !max_searchoptions with Some m ->
    if Queue.length searchoptions_retrieved >= m then raise Timeout
  | None -> ());
  o

let peekAtNext() =
  begin
    match !fiPRIORITY_QUEUE_IMPL with
    | 0 -> PQueue0.peekAtNext()
    | 1 -> PQueue1.peekAtNext()
    | 3 -> PQueue3.peekAtNext()
    | 4 -> PQueue4.peekAtNext()
    | 5 -> PQueue5.peekAtNext()
    | 6 -> PQueue6.peekAtNext()
    | 7 -> PQueue7.peekAtNext()
    | 8 -> PQueue8.peekAtNext()
    | 9 -> PQueue9.peekAtNext()
    | 10 -> PQueue10.peekAtNext()
    | n -> (raise (GenericError("Invalid value of PRIORITY_QUEUE_IMPL: " ^ (string_of_int n))))
  end

let testPriorityQueue() =
  let v = (!verbosity) in
(***  verbosity := 50; ***)
  for i = 0 to 2000
  do
    let p = (Random.int 10) in
    Printf.printf "Inserting %d with priority %d\n" i p;
    Printf.printf "(ins %d %d)\n" i p;
    insertWithPriority p (Filter i);
    if ((Random.int 3) = 0) then
      begin
	let (q,o1) = peekAtNext() in
	Printf.printf "Peeking at %s of priority %d\n" (searchoption_str o1) q;
	Printf.printf "(unless (equal (getnext) (list %d %d)) (error \"\"))\n" (match o1 with (Filter z) -> z | _ -> 0) q;
	let o2 = getNext() in
	if (not (o1 = o2)) then
	  Printf.printf "Got something different: %s\n" (searchoption_str o2);
      end;
  done;
  verbosity := v

let reset_pqueues () =
  PQueue0.reset();
  PQueue1.reset();
  PQueue3.reset();
  PQueue4.reset();
  PQueue5.reset();
  PQueue6.reset();
  PQueue7.reset();
  PQueue8.reset()
