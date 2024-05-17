open Term

val recognize_hashroots : bool ref

val is_of_names : string list ref
val all_of_names : string list ref
val is_of_name : (string,unit) Hashtbl.t
val all_of_name : (string,unit) Hashtbl.t

val add_ontology_type : string -> stp -> (string * string) list -> unit
val add_ontology_term : string -> trm -> unit

val translucent_defn_p : trm -> bool
val ontology_prop_p : trm -> bool
