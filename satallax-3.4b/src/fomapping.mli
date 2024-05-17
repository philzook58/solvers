val new_possible_fo_formula_1 : Syntax.trm -> Atom.atom -> (Syntax.stp -> 'a) -> Foform.foform
val printf_fof_pol_ax : out_channel -> int -> Syntax.trm -> unit
val printf_fof_file_propmatrix : out_channel -> unit
val printf_fof_file : out_channel -> Syntax.stp -> unit
val printf_fs_file : out_channel -> Syntax.stp -> unit
val printf_fof_question : out_channel -> Atom.atom -> Syntax.trm -> unit

val force_into_propmatrix : Atom.literal -> unit
val filter_unnec_from_propmatrix : int list -> unit
val propmatrixh : (int, Atom.literal list) Hashtbl.t

val setup_fomapping : unit -> unit
