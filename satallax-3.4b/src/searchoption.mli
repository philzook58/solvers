open Syntax

type searchoption =
 (*** ProcessProp1(m) might make pattern clauses and otherwise expands any remaining translucent defns leaving ProcessProp2 to apply the real rule ***)
    ProcessProp1 of trm
 (*** ProcessProp2(m) For rules requiring one formula in the head (most rules) ***)
  | ProcessProp2 of trm
 (*** Mating(plit,nlit,pl,nl) where pl,nl and plit = lit (h pl) and nlit = lit ~(h nl) ***)
  | Mating of int * int * trm list * trm list
 (*** Confront(nplit,nnlit,a,u,v,l,r) where u,v,l,r:a and nplit = lit (u = v) and nnlit is lit (l != r) ***)
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

val max_searchoptions : int option ref
val searchoptions_retrieved : searchoption Queue.t

val searchoption_str : searchoption -> string


(*** Interface to priority queue of search options ***)
val insertWithPriority : int -> searchoption -> unit
val getNext : unit -> searchoption
val peekAtNext : unit -> int * searchoption

val reset_pqueues : unit -> unit
