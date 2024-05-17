(* Lash *)
(* ported from Satallax file: *)
(* File: state.mli *)
(* Author: Chad E Brown *)
(* Created: October 2010 *)

open String
open Syntax
open Config
open Refut

val minisat_tm : float ref

val coqknown : string * string -> string

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

val conjecturenames : string list ref
val conjecture : (ftm * ftm) list ref
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
val name_base_list : int list ref
val name_tp : stp Vector.t
val name_tp_f : (int,int) Hashtbl.t
val name_trm : (string,(trm * stp) * bool ref) Hashtbl.t
val name_trm_list : (int * ftm * stp) list ref
val translucent_defns : bool ref
val name_def : (string,trm) Hashtbl.t
val name_def_f : (int,ftm) Hashtbl.t
val name_def_prenorm : (string,trm) Hashtbl.t
val name_def_all : (int,trm) Hashtbl.t
val name_hyp : (string,trm) Hashtbl.t
val name_hyp_f : (string,ftm) Hashtbl.t
val name_hyp_inv : (ftm,string) Hashtbl.t
val assumption_lit : (int,ftm * ftm) Hashtbl.t
val preprocess_ftm : (ftm,ftm) Hashtbl.t
val completep : bool ref
    
val mult_timeout : float -> unit

val required : string ref
val require : string -> unit

val get_fresh_name : stp -> string * ftm

val initial_branch : ftm list ref
val initial_branch_prenorm : trm list ref

val clauses : clause list ref

val clause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref

val allclauses : clause list ref (* allclauses is only used if formdeps is activated, in which case someone wants useless information. it contains all the clauses that were used in all searches across different subgoals. Aug 2016 *)
val allclause_ruleinfo : (clause,ruleinfo) Hashtbl.t ref

exception DuplicateClause

val new_assumption_lit : int -> unit
val new_search_clause : clause -> ruleinfo option -> unit


(*** Positive and negative atoms, indexed by the name at the head ***)
val patoms : ((int * (ftm list)) list) Vector.t
val natoms : ((int * (ftm list)) list) Vector.t

(*** Positive and negative atoms with Choice(a) at the head, indexed by the type a ***)
val pchoiceatoms : ((int * (ftm list)) list) Vector.t
val nchoiceatoms : ((int * (ftm list)) list) Vector.t

(*** Positive and negative equations, indexed by the base type at the head ***)
val peqns : ((int * ftm * ftm) list) Vector.t
val neqns : ((int * ftm * ftm) list) Vector.t

val univpreds : ((int * ftm) list) Vector.t

val filtered : bool Vector.t

val part_of_conjecture : (ftm,unit) Hashtbl.t

val set_default_elt : int -> ftm -> unit
val default_elt : int -> ftm
val default_elt_p : int -> bool

val get_instantiations : int -> ftm list
val known_instantiation : int -> ftm -> bool
val add_instantiation : int -> ftm -> unit

(*** Hash table associating names of epsilon operators with (a,m) where a is the type and m is the formula giving the choice axiom ***)
val choiceopnames : (int,(stp * trm * trm)) Hashtbl.t
val choiceopnames_f : (int,(stp * int)) Hashtbl.t

(*** Check if a formula says that a name is a choice operator at some type ***)
val choiceop_axiom : trm -> (string * stp) option
val fchoiceop_axiom : ftm -> (int * stp) option

val firrefbreln_axiom : ftm -> (int * stp) option
val fsymbreln_axiom : ftm -> (int * stp) option
val fcov1breln_axiom : ftm -> (int * int * int) option
val fnocl1breln_axiom : ftm -> (int * int * (int * int) list * (int * int) list) option

val minbrelnnames_f : (int,unit) Hashtbl.t
val maxbrelnnames_f : (int,unit) Hashtbl.t

(*** Declare a name to be a choice operator at some type ***)
val declare_choiceop : int -> stp -> trm * trm -> unit
val declare_fchoiceop : int -> int -> ftm -> unit

val declare_firrefbreln : int -> int -> ftm -> unit
val declare_fsymbreln : int -> int -> ftm -> unit
val declare_fcov1breln : int -> int -> int -> ftm -> unit
val declare_fnocl1breln : int -> int -> (int * int) list -> (int * int) list -> unit

(*** If trm is a choice operator at some type, return the type, otherwise None ***)
val choiceop : trm -> stp option
val fchoiceop : ftm -> int option
val firrefbreln : ftm -> int option
val fsymbreln : ftm -> int option
val fcov1breln : ftm -> (int * int) option
val fnocl1breln : ftm -> (int * (int * int) list * (int * int) list) option

type namecategory =
    ChoiceOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary choice operator (in particular, tl[i] is this one) ***)
   | DescrOp of int * int * stp list * trm list (*** (i,n,sigmal,tl) where length of sigmal and tl are n, 0 <= i < n, Name has type (sigmal -> o) -> sigmal[i], and for each j:{0,...,n-1} tl[j] is the jth component of the n-ary description operator (in particular, tl[i] is this one) ***)
   | IfThenElse of int * int * stp list (*** (i,n,sigmal) where length of sigmal is n, 0 <= i < n, Name has type o -> sigmal -> sigmal -> sigmal[i] ***)
   | ReflexiveBinary
   | IrreflexiveBinary
   | SymmetricBinary
   | ReflexiveSymmetricBinary
   | IrreflexiveSymmetricBinary

val constrainedName : (int,namecategory) Hashtbl.t

val decomposable : int -> bool

val get_timeout_default : float -> float

val st_include_fun : (string -> unit) ref
val st_find_read_thf_fun : (string -> string -> unit) ref

val declare_base_type : string -> unit

val declare_name_type : string -> stp -> unit

val declare_typed_constant : string -> string -> pretrm -> (string * string) list -> unit
    
val declare_definition : string -> string -> pretrm -> (string * string) list -> unit

val declare_thf_logic_formula : string -> string -> pretrm -> (string * string) list -> unit

(*** Code for enumeration of types and terms ***)
val enum_of_started : int -> bool
val enum_of_start : int -> unit
val new_usable_type_rtp : stp -> stp -> int -> unit
val usable_types_rtp : stp -> (stp * int) list
val new_usable_head_rtp : stp -> stp list -> ftm -> int -> unit
val usable_heads_rtp : stp -> (stp list * ftm * int) list

(*** Search Init ***)
val search_init : unit -> unit

(*** Reset Search ***)
val reset_search : unit -> unit

