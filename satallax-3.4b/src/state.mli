(* File: state.mli *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open String
open Syntax
open Config
open Refut

exception CoqProofTooBig of int

val select_axioms_list : int list ref
val select_axioms : unit -> unit
val num_axioms : unit -> int

val slaveargs : string list ref
val mode : string list ref
val timeout : float option ref
val hardtimeout : float option ref
val nontheorem : bool ref
val coq : bool ref
val coq2 : bool ref
val problemfile : string ref
val coqlocalfile : bool ref
val coqglobalfile : bool ref
val coqinchannel : in_channel ref
val coqoutchannel : out_channel ref
val coqinticks : ((out_channel -> unit) option * int) list ref
val coqoutfn1 : (out_channel -> unit) ref
val coqctx : prectx ref
val coqglobalsectionstack : (string * (out_channel -> unit) * prectx) list ref
val updatecoqglobalsectionstack : prectx -> (string * (out_channel -> unit) * prectx) list -> (prectx -> (out_channel -> unit) -> (out_channel -> unit)) -> (string * (out_channel -> unit) * prectx) list

type probitem =
  | ProbDef of string * stp * trm * (string * string) list * float
  | ProbAx of string * string * trm * (string * string) list * float
  | ProbConj of string * trm * (string * string) list * float
val probitem_weight : probitem -> float
val probsig : probitem list ref
val init_probitem : probitem -> unit

val conjecturename : string ref
val conjecture : (trm * trm) option ref
type proofkind = TSTP | CoqScript | CoqSPfTerm | HOCore | Model | ModelTrue | IsarScript | PfInfo | PfUseful | PfFormdeps
val mkproofterm : proofkind option ref
val mkprooftermp : unit -> bool
val pfusefulout : string option ref
val pfformdepsout : string option ref
val slave : bool ref
val coqsig_base : string list ref
val coqsig_const : (string * stp) list ref
val coqsig_def : (string * pretrm) list ref
val coqsig_hyp : (string * pretrm) list ref
val coqsig_def_trm : (string * trm) list ref
val coqsig_hyp_trm : (string * trm) list ref
val name_base : (string,unit) Hashtbl.t
val name_base_list : string list ref
val name_tp : (string,stp) Hashtbl.t
val name_trm : (string,(trm * stp) * bool ref) Hashtbl.t
val name_trm_list : (string * trm * stp) list ref
val translucent_defns : bool ref
val name_def : (string,trm) Hashtbl.t
val name_def_all : (string,trm) Hashtbl.t
val name_def_prenorm : (string,trm) Hashtbl.t
val name_hyp : (string,trm) Hashtbl.t
val name_hyp_inv : (trm,string * trm) Hashtbl.t
val assumption_lit : (int,trm * trm) Hashtbl.t
val coqknown : string * string -> string
val completep : bool ref
    
val mult_timeout : float -> unit

val required : string ref
val require : string -> unit

val get_fresh_name : stp -> string * trm

val initial_branch : trm list ref
val initial_branch_prenorm : trm list ref

val clauses : clause list ref

val processed : (trm,int) Hashtbl.t
val clause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref

val allclauses : clause list ref (* allclauses is only used if formdeps is activated, in which case someone wants useless information. it contains all the clauses that were used in all searches across different subgoals. Aug 2016 *)
val allclause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref

exception DuplicateClause

val new_assumption_lit : int -> unit
val new_search_clause : clause -> ruleinfo option -> unit


(*** Positive and negative atoms, indexed by the name at the head ***)
val patoms : (string,int * (trm list)) Hashtbl.t
val natoms : (string,int * (trm list)) Hashtbl.t

(*** Positive and negative atoms with Choice(a) at the head, indexed by the type a ***)
val pchoiceatoms : (stp,int * (trm list)) Hashtbl.t
val nchoiceatoms : (stp,int * (trm list)) Hashtbl.t

(*** Positive and negative equations, indexed by the base type at the head ***)
val peqns : (string,int * trm * trm) Hashtbl.t
val neqns : (string,int * trm * trm) Hashtbl.t

val univpreds : (stp,(int * trm)) Hashtbl.t

val filtered : (int,unit) Hashtbl.t

val part_of_conjecture : (trm,unit) Hashtbl.t

val set_default_elt : string -> trm -> unit
val default_elt : string -> trm
val default_elt_p : string -> bool

val get_instantiations : stp -> trm list
val known_instantiation : stp -> trm -> bool
val add_instantiation : stp -> trm -> unit

(*** Hash table associating names of epsilon operators with (a,m) where a is the type and m is the formula giving the choice axiom ***)
val choiceopnames : (string,(stp * trm * trm)) Hashtbl.t

(*** Check if a formula says that a name is a choice operator at some type ***)
val choiceop_axiom : trm -> (string * stp) option

(*** Declare a name to be a choice operator at some type ***)
val declare_choiceop : string -> stp -> trm * trm -> unit

(*** If trm is a choice operator at some type, return the type, otherwise None ***)
val choiceop : trm -> stp option

type namecategory =
    ChoiceOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary choice operator (in particular, tl[i] is this one) ***)
   | DescrOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary description operator (in particular, tl[i] is this one) ***)
   | IfThenElse of int * int * stp list (*** (i,n,sigmal) where length of sigmal is n, 0 <= i < n, Name has type o -> sigmal -> sigmal -> sigmal[i] ***)
   | ReflexiveBinary
   | IrreflexiveBinary
   | SymmetricBinary
   | ReflexiveSymmetricBinary
   | IrreflexiveSymmetricBinary

val constrainedName : (string,namecategory) Hashtbl.t

val decomposable : string -> bool

val get_timeout_default : float -> float

val st_include_fun : (string -> unit) ref
val st_find_read_thf_fun : (string -> string -> unit) ref

val print_coqsig : out_channel -> unit

val declare_base_type : string -> unit

val declare_name_type : string -> stp -> unit

val declare_typed_constant : string -> string -> pretrm -> (string * string) list -> unit
    
val declare_definition : string -> string -> pretrm -> (string * string) list -> unit

val declare_thf_logic_formula : string -> string -> pretrm -> (string * string) list -> unit

(*** Code for enumeration of types and terms ***)
val enum_started : bool ref
val enum_of_started : stp -> bool
val enum_of_start : stp -> unit
val new_type_continuation_rtp : stp -> (stp -> int -> unit) -> unit
val new_type_continuation : (stp -> int -> unit) -> unit
val iter_type_continuations_rtp : stp -> stp -> int -> unit
val iter_type_continuations : stp -> int -> unit
val new_term_continuation_rtp : stp -> (stp list * trm * int -> unit) -> unit
val iter_term_continuations_rtp : stp -> stp list -> trm -> int -> unit
val new_usable_type_rtp : stp -> stp -> int -> unit
val usable_types_rtp : stp -> (stp * int) list
val usable_types : unit -> (stp * stp * int) list
val new_usable_head_rtp : stp -> stp list -> trm -> int -> unit
val usable_heads_rtp : stp -> (stp list * trm * int) list

(*** Search Init ***)
val search_init : unit -> unit

(*** Reset Search ***)
val reset_search : unit -> unit

val coqnorm : trm -> trm
val normalize : trm -> trm
val partialnormalize : trm -> trm
