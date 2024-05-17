open Refutation

val print_stp_tstp : out_channel -> Term.stp -> bool -> unit
val trm_to_tstp : out_channel -> Term.trm -> TermP.Variables.t -> unit

val ref_coq : out_channel -> refutation -> unit

val ref_tstp : out_channel -> refutation -> unit
val refut_tstp : out_channel -> Refut.refut -> unit

val ref_coq_spfterm : out_channel -> refutation -> unit

val ref_isabellehol : out_channel -> refutation -> unit
