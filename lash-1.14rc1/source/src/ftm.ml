type ftm = int;;

external init_tm_tables : unit -> unit = "c_init_tm_tables";;
init_tm_tables ();;

external mk_db : int -> ftm = "c_mk_db" [@@noalloc];;
external mk_name : int -> ftm = "c_mk_name" [@@noalloc];;
external mk_norm_ap : ftm -> ftm -> ftm = "c_mk_norm_ap" [@@noalloc];;
external mk_norm_lam : int -> ftm -> ftm = "c_mk_norm_lam" [@@noalloc];;
external mk_false : unit -> ftm = "c_mk_false" [@@noalloc];;
let mk_false = mk_false ();;   (* The unique copy *)

external mk_norm_imp : ftm -> ftm -> ftm = "c_mk_norm_imp" [@@noalloc];;
external mk_all : int -> ftm -> ftm = "c_mk_all" [@@noalloc];;
external mk_choice : int -> ftm = "c_mk_choice" [@@noalloc];;
external mk_norm_eq : int -> ftm -> ftm -> ftm = "c_mk_norm_eq" [@@noalloc];;

(* These 4 do not beta-eta-false-normalize. Use only is sure.
   Otherwise they are stored in caches and will cause problems! *)
external mk_unsafe_ap : ftm -> ftm -> ftm = "c_mk_ap" [@@noalloc];;
external mk_unsafe_lam : int -> ftm -> ftm = "c_mk_lam" [@@noalloc];;
external mk_unsafe_imp : ftm -> ftm -> ftm = "c_mk_imp" [@@noalloc];;
external mk_unsafe_eq : int -> ftm -> ftm -> ftm = "c_mk_eq" [@@noalloc];;

(* Explicit requests for substitutions *)
external uptrm : ftm -> int -> int -> ftm = "c_uptrm" [@@noalloc];;
external subst : ftm -> int -> ftm -> ftm = "c_subst" [@@noalloc];;

type ftm_tag =
| FT_None
| FT_DB
| FT_Name
| FT_Ap
| FT_Lam
| FT_False
| FT_Imp
| FT_All
| FT_Choice
| FT_Eq;;
external get_tag : ftm -> ftm_tag = "c_get_tag" [@@noalloc];;

(* get_no lets you get the number of the type or of the name stored under the tag *)
external get_no : ftm -> int = "c_get_no" [@@noalloc];;
external get_l : ftm -> ftm = "c_get_l" [@@noalloc];;
external get_r : ftm -> ftm = "c_get_r" [@@noalloc];;
external get_head : ftm -> ftm = "c_get_head" [@@noalloc];;
external get_head_spine : ftm -> (ftm * ftm list) = "c_get_head_spine";;

external get_isneg : ftm -> bool = "c_get_isneg" [@@noalloc];;
external get_nonnegated : ftm -> ftm = "c_get_nonnegated" [@@noalloc];;

external get_maxv : ftm -> int = "c_get_maxv" [@@noalloc];;
external get_fv0 : ftm -> int -> bool = "c_get_fv0" [@@noalloc];;
external get_fv0_0 : ftm -> bool = "c_get_fv0_0" [@@noalloc];;

external set_incomplete : bool -> unit = "c_set_incomplete" [@@noalloc];;

external print : ftm -> unit = "c_print" [@@noalloc];;
external size : ftm -> int = "c_tm_size" [@@noalloc];;
external unique_subterm_bottom_up_iter : (ftm -> unit) -> ftm -> unit = "c_unique_subterm_bottom_up_iter";;
let unique_size t =
  let i = ref 0 in
  unique_subterm_bottom_up_iter (fun _ -> incr i) t; !i

external unique_subterm_bottom_up_replace : (ftm -> ftm) -> ftm -> ftm = "c_unique_subterm_bottom_up_replace";;

external processed_make : int -> unit = "c_processed_make" [@@noalloc];;
external processed_add : ftm -> unit = "c_processed_add" [@@noalloc];;
external processed_mem : ftm -> bool = "c_processed_mem" [@@noalloc];;
external processed_clear : unit -> unit = "c_processed_clear" [@@noalloc];;

(*
external clausetable_make : int -> unit = "c_clausetable_make" [@@noalloc];;
external clausetable_add_wasthere : int -> int list -> bool = "c_clausetable_add_wasthere" [@@noalloc];;
external clausetable_clear : unit -> unit = "c_clausetable_clear" [@@noalloc];;
*)

(*
val hashtbli1_find : hashtbli1 -> ftm -> int
external hashtbli2_find : hashtbli2 -> ftm -> ftm -> int = "c_hashtbli2_find" [@@noalloc];;




type vectori
external vectori_make : int -> vectori = "c_vectori_make";;
external vectori_add : vectori -> int -> ftm -> unit = "c_vectori_add" [@@noalloc];;
external vectori_find : vectori -> int -> ftm = "c_vectori_find" [@@noalloc];;
*)
