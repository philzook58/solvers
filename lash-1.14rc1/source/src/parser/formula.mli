type formula =
  (* Appl function argument_list: *)
    Appl of formula * formula list
  (* Symbol name: *)
  | Symbol of string
  | SymbolAt of formula * formula

val to_string : formula -> string

val set_format : string -> unit
