(* Lash *)
(* ported from Satallax file: atom.ml *)

open Ftm

type atom = int
type literal = int

external max_atom : unit -> int = "c_max_atom" [@@noalloc]
external get_literal : ftm -> int = "c_get_literal" [@@noalloc]
external literal_to_trm : int -> ftm = "c_literal_to_trm" [@@noalloc]
let atom_to_trm i = literal_to_trm i;;

let print_minisat eval b i m =
  let pol v = if v = 0 then "+" else "-"
  and v = eval i in
  match b with
    (*** 0 means true ***)
    true  -> if (v = 0) then Printf.printf "%d %s\n" i (Term.ftm_str m)
  | false -> if (v < 2) then Printf.printf "%d%s %s\n" i (pol v) (Term.ftm_str m)

let print_model eval b =
  for i = 1 to max_atom () do
    print_minisat eval b i (literal_to_trm i)
  done
