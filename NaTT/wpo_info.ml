open Util
open Smt


class wpo_sym (sym:#Trs.sym_detailed) = object
  val base : Trs.sym_detailed = sym
  method base = base
  val mutable status_mode = Strategy.S_none
  val mutable collapse = LB false
  val mutable is_const = LB(sym#arity = 0)
  val mutable is_quasi_const = LB(sym#arity = 0)
  val mutable perm : int -> int -> exp = k_comb (k_comb (LB false))
  val mutable permed : int -> exp = k_comb (LB false)
  val mutable mapped : int -> exp = k_comb (LB false)
  val mutable mset_status = LB false
  val mutable prec = Nil
  val mutable prec_ge : string -> exp = k_comb (LB false)
  val mutable prec_gt : string -> exp = k_comb (LB false)
  method status_mode = status_mode
  method collapse = collapse
  method is_const = is_const
  method is_quasi_const = is_quasi_const
  method perm = perm
  method permed = permed
  method mapped = mapped
  method mset_status = mset_status
  method lex_status = smt_not mset_status
  method prec = prec
  method prec_ge = prec_ge
  method prec_gt = prec_gt
  method set_status_mode x = status_mode <- x
  method set_collapse x = collapse <- x
  method set_is_const x = is_const <- x
  method set_is_quasi_const x = is_quasi_const <- x
  method set_perm x = perm <- x
  method set_permed x = permed <- x
  method set_mapped x = mapped <- x
  method set_mset_status x = mset_status <- x
  method set_prec x = prec <- x
  method set_prec_ge x = prec_ge <- x
  method set_prec_gt x = prec_gt <- x
end
