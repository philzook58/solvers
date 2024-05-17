open Log

let picomus_prelude myin clauses =
  Printf.fprintf myin "p cnf %d %d\n" (Atom.max_atom ()) (List.length clauses)

let picomus_clauses myin =
  List.iter (fun c -> Printf.fprintf myin "%s 0\n" (String.concat " " (List.map string_of_int c)))

let print_clause_set =
  List.iter (fun cl -> List.iter (fun l -> Printf.printf "%d " l) cl; print_newline ())

let read_picomus_char (pol, num_acc, cl_acc) c =
  (* number 0 *)
  if c = 48 then (pol, 10 * num_acc, cl_acc)
  (* number between 1 and 9 *)
  else if (48 < c && c <= 57) then (pol, 10 * num_acc + (c - 48), cl_acc)
  (* minus, i.e. negative literal *)
  else if c = 45 then ((-1), num_acc, cl_acc)
 (* otherwise assume this is a blank space *)
  else if c = 32 then (1, 0, pol * num_acc :: cl_acc)
  else raise (Error.GenericError "Picomus character read failed")

let rec read_picomus_clause_line chan (_, _, cl as state) c =
  if c <> 10 then
    let state' = read_picomus_char state c in
    let c' = input_byte chan in
    read_picomus_clause_line chan state' c'
  else
    List.rev cl

let read_picomus_line chan cls =
  match input_byte chan with
     99 (* 'c' *)
  | 112 (* 'p' *)
  | 118 (* 'v' *) -> ignore (input_line chan); cls
  | c -> read_picomus_clause_line chan (1, 0, []) c :: cls

let read_picomus_unsat chan =
  let cls = ref [] in
  try
    while true
    do
      cls := read_picomus_line chan !cls
    done;
    raise End_of_file (* unreachable *)
  with End_of_file -> List.rev !cls


let minimal_unsatisfiable_core clauses =
  if (!verbosity > 4) then Printf.printf "About to call picomus %s\n%!" (!Config.picomus);
  let (myout,myin,myerr) = Unix.open_process_full ((!Config.picomus) ^ " - -") [| |] in
  picomus_prelude myin clauses;
  if (!verbosity > 4) then Printf.printf "About to send clauses to picomus\n%!";
  picomus_clauses myin clauses;
  close_out myin;
  if (!verbosity > 4) then (Printf.printf "About to read result from picomus\n"; flush stdout);
  match (input_line myout) with
  | "s UNSATISFIABLE" ->
    let cls = read_picomus_unsat myout in
    ignore (Unix.close_process_full (myout,myin,myerr));
    if (!verbosity > 4) then
      (print_endline "Minimized Clause Set"; print_clause_set cls);
    cls
  | _ -> raise (Error.GenericError "strange return from picomus") (*** In case this happens, maybe I should just return all the clauses ***)
