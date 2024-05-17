(* File: satallaxmain.ml *)
(* Author: Chad E Brown *)
(* Created: September 2010 - moved most of this from satallax.ml to satallaxmain.ml in September 2011 *)

open Flags
open Syntax
open State
open Log
open Search
open Error
open Sine
open Ontology

exception InputHelpError of string
exception InputError of string

let coqfile = ref ""
let flag_overrides = ref []
let schedule_files : string list ref = ref []
let preparsed = ref false
let starttime = ref 0.0
let endtime = ref 0.0

let printnumaxiomsflag : bool ref = ref false
let selectaxiomsflag : bool ref = ref false

let help_lines =
[ "Usage: satallax [-[VvNhi]] [-verb <int>] [-P <PicoMus>] [-M <modedir>] [-s <schedule>] [-m <mode>] [-flag <name> <value>] [-t <timeout in seconds>] [-inferences <int>] [-p <pfformat>] <problemfile>"
; "-M <dir> : Set the directory in which the mode/schedule files are stored."
; "       The default mode directory is the 'modes' subdirectory of the Satallax directory."
; "-s : Schedule of modes to try (previously called the 'strategy schedule')"
; "-m : Mode"
; "-P <file> : PicoMus executable file"
; "-E <file> : E prover executable file"
; "-V : Print version number and quit"
; "-v : Verbose"
; "-h : recognize hashroots for special treatment"
; "-i : given problem is incomplete version of the real problem, so do not report Satisfiable or CounterSatisfiable"
; "-N : Try to determine if the problem is a non-theorem (Satisfiable or CounterSatisfiable)"
; "-verb <int> : Verbosity of given level, -verb 0 means silent"
; "-c [<file>|-] : Create a Coq version of problem, with a proof script if -p is included and proof search succeeds"
; "-C : The problem is given as a Coq file instead of as a THF file."
; "-G : A Coq file containing multiple conjectures is given. Try to prove each of them independently."
; "-p [tstp|coqscript|coqspfterm|hocore|modeltrue|model|isar|info|useful|formdeps]: Output proof/proof object/proof info"
; "-pfusefulout <file>: File in which to save info about what was useful in the proof"
; "-pfformdepsout <file>: File in which to save info about what formulas and dependencies were in the proof"
]

let comment_line_p l =
  if String.length l = 0 then true
  else l.[0] = ';'

let rec get_input_lines c =
  try 
    let line = input_line c in
    line :: get_input_lines c
  with End_of_file -> []

let get_content_lines c =
  List.filter (fun line -> not (comment_line_p line)) (get_input_lines c)

let rec set_flags = function
  flag :: value :: rest -> set_flag flag value; set_flags rest
| flag :: [] -> raise (InputError ("Value after flag " ^ flag ^ " expected"))
| [] -> ()

let read_mode_file c = set_flags (get_content_lines c)

let read_schedule_line l =
  Scanf.sscanf l "%s %f" (fun mode time -> (mode, time))

let read_schedule_file c =
  List.map read_schedule_line (get_content_lines c)

let load_schedule s =
  let schedfile = !Config.modedir ^ "/" ^ s in
  if not (Sys.file_exists schedfile) then
    raise (InputError ("Could not find schedule " ^ schedfile));
  FileE.with_in schedfile read_schedule_file

let load_mode m =
  let modefile = (!Config.modedir ^ "/" ^ m) in
  if (not (Sys.file_exists modefile)) then
    raise (InputError ("Could not find mode " ^ modefile));
  FileE.with_in modefile read_mode_file

let parse_override s =
  match Str.split (Str.regexp "=") s with
  | [key;value] -> (key, value)
  | _ -> raise (InputError ("Could not parse flag/value pair " ^ s))

let parse_mode_overrides m =
  match Str.split (Str.regexp ":") m with
  | [] -> raise (InputError "Can not parse empty mode")
  | mode::overrides -> (mode, List.map parse_override overrides)

let load_mode_overrides (mode, overrides) =
  load_mode mode;
  List.iter (fun (k, v) -> set_flag k v) overrides

let read_coq_file (f:string) =
  if (!verbosity > 20) then Printf.printf "Starting to read Coq file %s\n" f;
  coqinchannel := if (f = "") then stdin else (open_in f);
  let ch = Lexing.from_channel !coqinchannel in
  try
    while true do
      Coqparser.documentitem Coqlexer.token ch
    done
  with
    Coqlexer.Eof ->
      begin
	if (!verbosity > 20) then Printf.printf "End of Coq file\n";
	if ((!coqglobalfile) && (not ((!coqinchannel) = stdin))) then
	  let p = pos_in !coqinchannel in
	  let j = ref 0 in
	  begin
	    seek_in !coqinchannel 0;
	    List.iter
	      (fun (x,i) ->
		if (!verbosity > 20) then Printf.printf "End of Coq file %d %d\n" i (!j);
		match x with
		| Some g -> if (!verbosity > 20) then g stdout; g !coqoutchannel; seek_in !coqinchannel i; j := i
		| None -> while (!j < i) do (incr j; let z = input_char !coqinchannel in output_char !coqoutchannel z) done
		      )
	      (List.rev (!State.coqinticks));
	    while (!j < p) do (incr j; let z = input_char !coqinchannel in output_char !coqoutchannel z) done;
	  end;
	  close_in !coqinchannel;
	  close_out !coqoutchannel
      end

let read_thf_file (f:string) (include_fun : string -> unit) =
  let ch = Lexing.from_channel (if (f = "") then stdin else (open_in f)) in
  let old_include_fun = !st_include_fun in
  st_include_fun := include_fun;
(***  List.iter Tptp_config.process_thf (Tptp_parser.tptp_file Tptp_lexer.token ch); ***)
  ignore (Tptp_parser.tptp_file Tptp_lexer.token ch);
  if (!verbosity > 4) then Printf.printf "Finished reading thf file %s\n" f;
  st_include_fun := old_include_fun

let rec find_read_thf_file_r odir dir f =
  let ff = (dir ^ "/" ^ f) in
  if (Sys.file_exists ff) then
    read_thf_file ff (find_read_thf_file odir)
  else if (String.length dir > 1) then
    find_read_thf_file_r odir (Filename.dirname dir) f
  else
    raise (FileNotFound f)
and find_read_thf_file dir f =
  let ff = (dir ^ "/" ^ f) in
  if (Sys.file_exists ff) then
    read_thf_file ff (find_read_thf_file dir)
  else
    begin
      try
	let tptpdir = Sys.getenv "TPTP" in
	let tff = (tptpdir ^ "/" ^ f) in
	if (Sys.file_exists tff) then
	  read_thf_file tff (find_read_thf_file dir)
	else
	  find_read_thf_file_r dir dir f
      with
      | Not_found -> find_read_thf_file_r dir dir f
    end;;

st_find_read_thf_fun := find_read_thf_file;;

let read_proofkind = function
  "tstp" -> TSTP
| "coqscript" -> CoqScript
| "coqspfterm" -> CoqSPfTerm
| "hocore" -> HOCore
| "model" -> Model
| "modeltrue" -> ModelTrue
| "isar" -> IsarScript
| "info" -> PfInfo
| "useful" -> PfUseful
| "formdeps" -> PfFormdeps
| p -> raise (InputHelpError ("Unknown kind of proof " ^ p ^ " for -p"))

let setup_proofkind = function
  IsarScript ->
    mkproofterm := Some IsarScript;
    Flag.result_coq := false;
    Flag.result_isabellehol := true
| p -> mkproofterm := Some p

let enslave args = slaveargs := List.rev_append args !slaveargs

let process_short_cmd_line_arg = function
  'v' -> enslave ["-v"]; verbosity := 5
| 'V' -> print_endline Version.version; exit 0
| 'h' -> enslave ["-h"]; recognize_hashroots := true
| 'i' -> enslave ["-i"]; completep := false
|  a  -> raise (InputHelpError ("Unknown command line argument " ^ String.make 1 a))

let set_problemfile p =
  if !problemfile = "" then problemfile := p
  else raise (InputHelpError ("Multiple problem files passed: " ^ !problemfile
  ^ " and " ^ p))

let process_cmd_line_arg = function
  "-m"::m::r -> mode := m :: !mode; r
| "-s"::s::r -> schedule_files := s :: !schedule_files; r
| "-M"::m::r -> Config.modedir := m; enslave ["-M"; m]; r
| "-P"::p::r -> Config.picomus := p; enslave ["-P"; p]; r
| "-E"::e::r -> Config.eprover := e; enslave ["-E"; e]; r
| "-t"::t::r -> timeout := Some (float_of_string t); r
| "-ht"::t::r -> hardtimeout := Some (float_of_string t); r
| "-C"::r -> coqlocalfile := true; enslave ["-C"]; r
| "-G"::r -> coqglobalfile := true; r
| "-c"::c::r ->
    coq := true;
    if (c = "-") then coqoutchannel := stdout
    else (coqfile := c; coqoutchannel := open_out c);
    enslave ["-c"; c]; r
| "-slave"::r -> slave := true; r
| "-preparsed"::r -> preparsed := true; r
| "-N"::r -> nontheorem := true; enslave ["-N"]; r
| "-flag"::f::v::r ->
    flag_overrides := (f, v)::!flag_overrides;
    enslave ["-flag"; f; v]; r
| "-p"::p::r ->
    setup_proofkind (read_proofkind (String.lowercase p));
    enslave ["-p"; p]; r
| "-pfusefulout"::f::r -> pfusefulout := Some(f); enslave ["-pfusefulout";f]; r
| "-pfformdepsout"::f::r -> pfformdepsout := Some(f); enslave ["-pfformdepsout";f]; r
| "-verb"::v::r -> verbosity := int_of_string v; enslave ["-verb"; v]; r
| "-inferences"::i::r -> Searchoption.max_searchoptions := Some (int_of_string i); enslave ["-inferences"; i]; r
| "-numaxioms"::r -> printnumaxiomsflag := true; enslave ["-numaxioms"]; r
| "-selectaxioms"::n::r -> (*** This is only to experiment with different selections and (order) of the axioms/conjecture. ***)
    selectaxiomsflag := true;
    let num = int_of_string n in
    let axs = List.map int_of_string (ListE.take num r) in
    select_axioms_list := List.rev_append axs !select_axioms_list;
    ListE.drop num r
| "-foffiles"::r -> (*** This is only for testing and debugging interaction with FO provers like E. ***)
    Eprover.foffiles := true; enslave ["-foffiles"]; r
| ""::r -> raise (InputHelpError "Problem processing command line arguments")
| "-"::r -> problemfile := ""; r
| opt::r ->
    if opt.[0] = '-'
    then String.iter process_short_cmd_line_arg (StringE.tail opt)
    else set_problemfile opt;
    r
| [] -> []

let process_command_line_args = function
  [] -> print_endline Version.version; List.iter print_endline help_lines; exit 1
| args -> ListE.iterate process_cmd_line_arg args


(*** -p implies -c if -c was not given. Output proof via Coq out channel. - Chad, July 2012 ***)
let set_coq () = if (not (!coq)) then (coq := true; coqoutchannel := stdout)

let prepare_proofterm = function
  | TSTP -> set_coq ()
  | CoqScript -> set_coq ()
  | CoqSPfTerm -> coq2 := true; set_coq ()
  | IsarScript -> set_coq () (*FIXME code in this section, and in related sections, need refactoring. names are a bit misleading.*)
  | _ -> ()


let code_status = function
  | (true , Some _) -> 10, "CounterSatisfiable"
  | (true , None  ) -> 15, "Satisfiable"
  | (false, Some _) -> 20, "Theorem"
  | (false, None  ) -> 25, "Unsatisfiable"

let n_inferences () = Queue.length Searchoption.searchoptions_retrieved
let inferences_str () = "% Inferences: " ^ string_of_int (n_inferences ())

let show_status s =
  [ "% SZS status " ^ s
  ; "% Mode: " ^ (String.concat " " !mode)
  ; inferences_str ()
  ]

let print_status s =
  if !verbosity > 0 then List.iter print_endline (show_status s)

let print_proofmsg c l =
  let enbracket s =
    if !mkproofterm = Some IsarScript then "(*" ^ s ^ "*)" else s in
  if c = stdout then List.iter print_endline (List.map enbracket l)

let print_start c l =
  let (_, status) = code_status (false, !conjecture) in
  print_proofmsg c (show_status status @ l)

let print_end c l = print_proofmsg c l; if c != stdout then close_out c else flush c

let try_proofout f =
  try f()
  with CoqProofTooBig coqproofsize ->
    if (!verbosity > 0) then Printf.printf "%% SZS status Success\nProof Too Big: %d steps\n" coqproofsize;
    exit 26

let print_proofterm_full c r = function
  | TSTP ->
      print_start c ["% SZS output start Proof"];
      try_proofout (fun () -> Proofterm.print_tstp c r);
      print_end c ["% SZS output end Proof"]
  | CoqScript ->
      print_start c ["% SZS output start Proof"; "% Coq Proof Script"];
      try_proofout (fun () -> Proofterm.print_coq_proofscript c r);
      print_end c ["% SZS output end Proof"]
  | CoqSPfTerm ->
      print_start c ["% SZS output start Proof"; "% Coq Proof Script"];
      try_proofout (fun () -> Proofterm.print_coq_sproofterm c r);
      print_end c ["% SZS output end Proof"]
  | HOCore ->
      print_start c ["% Higher-Order Unsat Core BEGIN"];
      Proofterm.print_hocore c r;
      print_end c ["% Higher-Order Unsat Core END"]
  | IsarScript ->
      print_start c ["% SZS output start Proof"; "% Isar Proof Script"];
      try_proofout (fun () -> Proofterm.print_coq_proofscript c r);
      print_end c ["% SZS output end Proof"]
  | PfInfo ->
      print_start c ["% Pf Info BEGIN"];
      Proofterm.print_pfinfo c r;
      print_end c ["% Pf Info END"]
  | PfUseful ->
      print_start c ["% Pf Useful BEGIN"];
      Proofterm.print_pfuseful c r !pfusefulout;
      print_end c ["% Pf Useful END"]
  | PfFormdeps ->
      print_start c ["% Pf Formdeps BEGIN"];
      Proofterm.print_pfformdeps c r !pfformdepsout;
      print_end c ["% Pf Formdeps END"]
  | _ -> ()


let prepare_coq () =
  if (!coq) then TermP.termP_init();
  if (!coqlocalfile) then read_coq_file (!problemfile) else read_thf_file (!problemfile) (find_read_thf_file (Filename.dirname (!problemfile)));
  probsig := List.rev !probsig

let set_timeouts s =
  if (s > 0.0) then begin
    if (!nontheorem && get_bool_flag "SPLIT_GLOBAL_DISJUNCTIONS" && s >= 0.2)
    then (set_timer (s *. 0.5); mult_timeout 0.5)
    else (set_timer s; timeout := Some 0.0)
  end

let preweightsum ps = List.fold_left (fun v z -> v +. probitem_weight z) 0.0 ps

let problem_is_small ps = preweightsum ps < 128.0

let auto_schedule () =
  if (!nontheorem) then "schedule_nontheorem"
  else if problem_is_small !probsig then "schedule_3_1"
  else "schedule_3_1_sine"

let get_schedule = function
  [] -> load_schedule (auto_schedule ())
| st -> List.concat (List.rev_map load_schedule st)

let slave_cmd s m arg =
  let mode = ["-m"; m] in
  let u = Unix.gettimeofday() in
  let rmtm = !endtime -. u in
  let timo =
    match s with
    | Some(s) ->
	if rmtm > s then
	  ["-t"; string_of_float s;"-ht"; string_of_float rmtm]
	else
	  ["-t"; string_of_float rmtm]
    | None -> []
  in
  String.concat " " ((List.rev !slaveargs) @ arg @ mode @ timo @ ["-preparsed"])

(*** If the slave got a final result, then use it. ***)
let handle_slave_return pstatus =
  match pstatus with
  | 5 -> raise Timeout
  | 6 -> raise IncompleteSatisfiable
  | 10
  | 15
  | 20
  | 25 -> exit pstatus
  | _ -> ()

let write_preparsed c =
  output_value c !name_base_list;
  output_value c (List.map (fun (x,_,tp) -> (x,tp)) !name_trm_list);
  output_value c !is_of_names;
  output_value c !all_of_names;
  output_value c !probsig

let read_preparsed c =
  let basetps : string list = input_value c in
  List.iter declare_base_type (List.rev basetps);
  let nametrms : (string * stp) list = input_value c in
  List.iter (fun (x,tp) -> declare_name_type x tp) (List.rev nametrms);
  is_of_names := input_value c;
  List.iter (fun x -> Hashtbl.add is_of_name x ()) !is_of_names;
  all_of_names := input_value c;
  List.iter (fun x -> Hashtbl.add all_of_name x ()) !all_of_names;
  probsig := input_value c

(* print all output from channel to stdout *)
let to_stdout c =
  while true do
    let l = input_line c in
    Printf.printf "%s\n" l
  done

let run_slave s m =
  let final = match s with Some _ -> false | None -> true in
  let cmd = slave_cmd s m (if final then [] else ["-slave"]) in
  if (!verbosity > 4) then print_endline ("Starting slave: " ^ cmd);
  flush stdout; (*** 2015, to prevent race conditions with output of main process vs. slave process ***)
  let (myout,myin,myerr) = Unix.open_process_full cmd [| |] in
  write_preparsed myin;
  close_out myin;
  try to_stdout myout
  with End_of_file ->
    match Unix.close_process_full (myout,myin,myerr) with
    | (Unix.WEXITED pstatus) ->
	if (!verbosity > 4) then
	  Printf.printf "slave returned with status %d\n" pstatus;
	handle_slave_return pstatus; if final then exit pstatus
    | _ ->
	if (!verbosity > 0) then
	  begin
            print_endline "slave returned with unknown status";
            if final then exit 3
	  end

let run_mode m s =
  try
    run_slave s m
  with
  | IncompleteSatisfiable -> () (*** in this case, the mode was incomplete and the subproblem was determined to be satisfiable, so go to the next mode ***)
  | Timeout -> () (*** upon timeout, go to the next mode ***)

(*** total time of schedule ***)
let schedule_time = List.fold_left (fun s1 (x,s2) -> (s1 +. s2)) 0.0

let run_schedule schedule stoptime =
  let rec run_schedule_r sch stoptime schtime =
  match sch with
  | [] -> raise Timeout
  | ((m,s)::rsch) ->
      let remtime = stoptime -. Unix.gettimeofday() in
      if remtime < s then
	raise Timeout
      else
	let s2 = s *. (max 1. (remtime /. schtime)) in
	run_mode m (Some(s2));
	run_schedule_r rsch stoptime (schtime -. s)
  in
  run_schedule_r schedule stoptime (schedule_time schedule)

let rec run_schedule_notimeout schedule =
  match schedule with
  | [] -> raise Timeout (*** If nothing on schedule, then Timeout anyway. ***)
  | [(m,_)] -> (*** Last mode on schedule, call it without a timeout and without telling it it's a slave. ***)
      run_mode m None
  | ((m,s)::rsch) ->
      run_mode m (Some(s));
      run_schedule_notimeout rsch
    
let print_num_axioms () =
  Printf.printf "(NUMAXIOMS \"%s\" %d)\n" (!problemfile) (num_axioms ());
  exit 123

let filter_probitems r ps =
  let ps' = List.filter (fun z -> probitem_weight z <= r) ps in
  if !verbosity > 4 then
    begin
      Printf.printf "Including those ranked <= %f\n" r;
      List.iter
        (fun z ->
          match z with
          | ProbDef(x,_,_,_,_) -> Printf.printf "Including def %s\n" x
          | ProbAx(x,_,_,_,_) -> Printf.printf "Including ax %s\n" x
          | ProbConj(x,_,_,_) -> Printf.printf "Including conj %s\n" x)
        ps'
    end;
  ps'

let sine ps =
  filter_probitems (get_float_flag "SINE_RANK_LIMIT") (sinelike_premsel ps)

let run_modes modes =
  try
    List.iter (fun mo -> load_mode_overrides (parse_mode_overrides mo)) modes;
    List.iter (fun (k, v) -> set_flag k v) !flag_overrides;
    if (!verbosity > 8) then print_flags ();
    OptionE.mapm prepare_proofterm !mkproofterm;
    set_timeouts (get_timeout_default 0.0);
    if !preparsed then read_preparsed stdin else prepare_coq ();
    if get_bool_flag "USE_SINE" then (probsig := sine !probsig; completep := false);
    List.iter init_probitem !probsig;
    if (!printnumaxiomsflag) then print_num_axioms ();
    if (!selectaxiomsflag) then select_axioms ();
    Eprover.setup_eprover ();
    search ()
  with
  | Refut.Unsatisfiable(r) ->
      (*** Some subgoals may have timed out and the last one reported Unsatisfiable ***)
      if (!nontheorem) then raise Timeout;
      (*** change the timeout to be the hard timeout, so that instead of continuing with the strategy schedule the rest of the time is spent trying to output this proof ***)
      begin
	match !hardtimeout with
	| Some hs ->
	    let rm = remaining_time() in
	    set_timer (hs +. rm)
	| _ -> ()
      end;
      let (code, status) = code_status (false, !conjecture) in
      begin match (r, !mkproofterm) with
          (Some r, Some pt) ->
            if !coq && not !coq2 && not !slave then print_coqsig !coqoutchannel;
            print_proofterm_full !coqoutchannel r pt; exit code
        | (_, _) -> print_status status; exit code
      end
  | Refut.Satisfiable ->
      if not !completep then raise IncompleteSatisfiable;
      let (code, status) = code_status (true, !conjecture) in
      print_status status; exit code

let search_main () =
  match (!mode) with
  | [] ->
      starttime := Unix.gettimeofday();
      endtime := !starttime +. get_timeout_default 600.0;
      prepare_coq(); (*** parse the problem before calling slaves - Chad, Nov 2016 ***)
      if !timeout = None then
        run_schedule_notimeout (get_schedule !schedule_files)
      else
        run_schedule (get_schedule !schedule_files) !endtime
  | modes -> run_modes modes
