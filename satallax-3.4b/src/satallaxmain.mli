(* File: satallaxmain.mli *)
(* Author: Chad E Brown *)
(* Created: September 2011 *)

exception InputHelpError of string
exception InputError of string

val help_lines : string list
val inferences_str : unit -> string
val load_mode : string -> unit
val read_coq_file : string -> unit
val read_thf_file : string -> (string -> unit) -> unit
val process_command_line_args : string list -> unit
val search_main : unit -> unit
