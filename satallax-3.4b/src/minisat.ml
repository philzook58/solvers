open Log
open Minisatinterface
open Refut

let minisatsearchcounter = ref 0;;
let minisatsearchperiod = ref 1;;

let minisat_search_period () =
  incr minisatsearchcounter;
  if (!minisatsearchcounter >= !minisatsearchperiod) then
    begin
      minisatsearchcounter := 0;
      if !verbosity > 3 then Printf.printf "About to call minisat_search\n%!";
      let r = minisat_search () in
      if !verbosity > 3 && r then Printf.printf "still satisfiable\n%!";
      r
    end
  else
    true


let minisat_result () =
  if (!minisatsearchperiod > 1) then
    begin
      let r = minisat_search () in
      if (not r) then raise (Unsatisfiable None)
    end;
  raise Satisfiable

let add_clauses c =
  if (!verbosity > 3) then
    Printf.printf "About to add minisat clause (%s)\n%!" (String.concat " " (List.map string_of_int c));
  match c with
    [] -> raise (Unsatisfiable None)
  | [l1] -> minisat_addClause1 l1
  | [l1;l2] -> minisat_addClause2 l1 l2
  | [l1;l2;l3] -> minisat_addClause3 l1 l2 l3
  | _ -> List.iter minisat_addLit c; minisat_addClause ()
