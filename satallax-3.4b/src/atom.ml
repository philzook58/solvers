open Syntax
open Log

type atom = int
type literal = int

let next_atom = ref 1
let atom_hash : (trm,int) Hashtbl.t = Hashtbl.create 1000
let atom_hash_rev : (int,trm) Hashtbl.t = Hashtbl.create 1000

let new_atom_actions = ref []

let max_atom () = (!next_atom) - 1


let new_atom m =
  let a = (!next_atom) in
  incr next_atom;
  Hashtbl.add atom_hash m a;
  Hashtbl.add atom_hash_rev a m;
  if (!verbosity > 4) then
    if (!verbosity > 8) then Printf.printf "Atom %d: %s\n" a (trm_str m)
    else (Printf.printf "Atom %d\n" a);
  List.iter (fun f -> f m a) !new_atom_actions;
  a

let get_atom m =
  try Hashtbl.find atom_hash m
  with Not_found -> new_atom m

let assignedp m =
  match (neg_body m) with
    Some n -> Hashtbl.mem atom_hash n
  | None -> Hashtbl.mem atom_hash m

let atom_to_trm = Hashtbl.find atom_hash_rev

let get_literal m =
  match (neg_body m) with
    Some n -> - (get_atom n)
  | None -> get_atom m

let literal_to_trm l =
  if (l < 0)
  then neg (Hashtbl.find atom_hash_rev (- l))
  else Hashtbl.find atom_hash_rev l


let print_minisat eval b m i =
  let pol v = if v = 0 then "+" else "-"
  and v = eval i in
  match b with
    (*** 0 means true ***)
    true  -> if (v = 0) then Printf.printf "%d %s\n" i (trm_str m)
  | false -> if (v < 2) then Printf.printf "%d%s %s\n" i (pol v) (trm_str m)

let print_model eval b = Hashtbl.iter (print_minisat eval b) atom_hash

