val apply_pattern_clauses : int -> Syntax.trm -> unit
val new_pattern_clauses : int -> Syntax.trm -> unit

val pattern_clauses_forall_as_lit : bool ref
val pattern_clauses_onlyallstrict : bool ref
val pattern_clauses_eqnlits : bool ref
