open Log
open Minisatinterface
open Refut

let minisatsearchcounter = ref 0;;
let minisatsearchdelay = ref 1;;
let minisatsearchperiod = ref 1;;
let minisatsearchperiodfactor = ref 2;;

let minisat_search_period () =
  incr minisatsearchcounter;
  if (!minisatsearchcounter >= !minisatsearchdelay) then
    begin
      minisatsearchcounter := 0;
      minisatsearchdelay := !minisatsearchperiod;
      minisatsearchperiod := !minisatsearchperiod * !minisatsearchperiodfactor;
      if !verbosity > 3 then Printf.printf "About to call minisat_search\n%!";
      let r = minisat_search () in
      if !verbosity > 3 && r then Printf.printf "still satisfiable\n%!";
      r
    end
  else
    true


let minisat_result () =
  if (!minisatsearchcounter > 0) then
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
  | _ -> minisat_addClause c
