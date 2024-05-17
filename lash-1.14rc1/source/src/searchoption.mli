open Syntax

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

val max_searchoptions : int option ref
val searchoptions_retrieved : int ref

val searchoption_str : searchoption -> string


(*** Interface to priority queue of search options ***)
val insertWithPriority : int -> searchoption -> unit
val getNext : unit -> int * searchoption
val peekAtNext : unit -> int

val reset_pqueues : unit -> unit
