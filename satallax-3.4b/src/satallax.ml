(* File: satallax.ml *)
(* Author: Chad E Brown *)
(* Created: September 2010 - most code moved to satallaxmain in September 2011 *)

open Satallaxmain
open Flags
open Syntax
open State
open Log
open Printf
open Error

let status_str s = "% SZS status " ^ s
let error_str = status_str "Error"

let error_reaction = function
| InputHelpError(x) -> 1, error_str :: sprintf "Input Error: %s" x :: help_lines
| InputError(x) -> 1, [error_str; sprintf "Input Error: %s" x]
| FileNotFound(x) -> 1, [error_str; sprintf "File Not Found: %s" x]
| NotFlag(x) -> 2, [error_str; sprintf "%s is not a flag" x]
| Parsing.Parse_error -> 2, [error_str; "Syntax Error"]
| ParsingError(l1,i1,l2,i2,x) -> 2, [error_str; sprintf "Parsing Error: %s from line %d char %d to line %d char %d\n" x l1 i1 l2 i2]
| ExpectedTypeError(m,a,b) -> 2, [error_str; sprintf "%s\nhas type\n%s\nexpected type\n%s\n" (pretrm_str m) (stp_str b) (stp_str a)]
| GenericError(x) -> 2, [error_str; x]
| GenericSyntaxError(x) -> 2, [error_str; x]
| Redeclaration(x) -> 2, [error_str; sprintf "%s cannot be redeclared" x]
| Polymorphism -> 2, [status_str "Inappropriate"; "Polymorphic type detected"; "Satallax supports only simple type theory"]
| IncompleteSatisfiable -> 6, []
| Timeout -> 5, if (!verbosity > 0) then [status_str ("Timeout"); inferences_str ()] else []
| e -> 3, if (!verbosity > 0) then [error_str; sprintf "Exception: %s" (Printexc.to_string e)] else []

let _ =
  try
    init_flags ();
    process_command_line_args (List.tl (Array.to_list Sys.argv));
    if (!coqglobalfile) then
      read_coq_file !problemfile
    else
      search_main ()
  with e ->
    let (code, msg) = error_reaction e in
    if (not !slave) then List.iter print_endline msg;
    exit code
