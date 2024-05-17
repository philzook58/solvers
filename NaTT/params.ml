open Util
open Term
open Strategy

let version = "2.2";


type estimator_mode =
| E_tcap
| E_sym_trans
type acdp_mode =
| ACDP_new
| ACDP_union
type ac_mark_mode =
| AC_unmark
| AC_mark
| AC_guard
type rdp_mode = (* for relative DP *)
| RDP_naive
| RDP_move
type mode =
| MODE_default
| MODE_order
| MODE_flat
| MODE_freezing
| MODE_simple
| MODE_dup
| MODE_cond
| MODE_through
| MODE_higher_xml
| MODE_xml
| MODE_infeasibility of (Sym.sym term * Sym.sym term) list

type params_type = {
  mutable mode : mode;
  mutable file : string;
  mutable dp : bool;
  mutable edge_mode : estimator_mode;
  mutable edge_length : int;
  mutable freezing : bool;
  mutable max_loop : int;
  mutable max_narrowing : int;
  mutable acdp_mode : acdp_mode;
  mutable rdp_mode : rdp_mode;
  mutable ac_mark_mode : ac_mark_mode;
  mutable orders_rule : order_params array;
  mutable orders_dp : order_params array;
  mutable orders_edge : order_params array;
  mutable nonreach_estimator : bool;
  mutable orders_nonreach : order_params array;
  mutable result : bool;
  mutable cpf : bool;
  mutable cpf_to : out_channel;
  mutable relative_usable : bool;
  mutable naive_C : bool;
};;

let params = {
  mode = MODE_default;
  file = "";
  dp = false;
  edge_mode = E_sym_trans;
  edge_length = 8;
  freezing = false;
  max_loop = 0;
  max_narrowing = 8;
  acdp_mode = ACDP_new;
  rdp_mode = RDP_move;
  ac_mark_mode = AC_mark;
  orders_rule = [||];
  orders_dp = [||];
  orders_edge = [||];
  nonreach_estimator = true;
  orders_nonreach = [||];
  result = true;
  cpf = false;
  cpf_to = stdout;
  relative_usable = true;
  naive_C = false;
};;

let set_strategy (pre,freezing,rest,reach) =
  params.orders_rule <- Array.of_list pre;
  params.freezing <- freezing;
  ( match rest with
    | Some(orders_dp,orders_edge,loop) ->
      params.dp <- true;
      params.orders_dp <- Array.of_list orders_dp;
      params.orders_edge <- Array.of_list orders_edge;
      params.max_loop <- loop;
    | None -> ()
  );
  params.orders_nonreach <- Array.of_list reach;
in
let err msg =
  prerr_endline msg;
  print_endline "ERR";
  exit 1;
in
let argv = Sys.argv in
let argc = Array.length argv in
let prerr_help () =
  let pr = prerr_string in
  let pe = prerr_endline in
  pr "NaTT ver."; pe version;
  pr "Usage: "; pr argv.(0); pe " [FILE] [OPTION]...";
  pe "";
  pe "Checks termination of TRS specified by FILE (stdin by default).";
  pe "";
  pe "OPTIONs:";
  pe "  -v:<n>         set verbosity (0 to 6, default: 3).";
  pe "  --cvc4         use CVC4 instead of Z3.";
in
let i = ref 1 in
let erro str = err ("unknown option: " ^ str ^ "!") in
let safe_atoi s arg = (try int_of_string s with _ -> erro arg) in
let strategy_str = ref "" in
let strategy_file = ref "" in
let default_smt = ref Smt.z3_params in
while !i < argc do
  let arg = argv.(!i) in
  if arg.[0] = '-' then begin
    let (opt,optarg) =
      let len = String.length arg in
      try let b = String.index argv.(!i) ':' in
        (String.sub arg 1 (b - 1), Some(String.sub arg (b+1) (len - b - 1)))
      with Not_found ->
        (String.sub arg 1 (len - 1), None)
    in
    match opt, optarg with
    | "-help", _ -> prerr_help (); exit 0;
    | "s", Some file -> strategy_file := file;
    | "S", Some str -> strategy_str := str;
    | "-smt", Some str -> default_smt := Txtr.parse_string (Smt.params_of_xml Smt.z3_params) str;
    | "-z3", None -> default_smt := Smt.z3_params;
    | "-cvc4", None -> default_smt := Smt.cvc4_params;
    | "-naive-C", None -> params.naive_C <- true;
    | "-ac", Some s -> (
      match s with
      | "new" -> params.acdp_mode <- ACDP_new;
      | "union" -> params.acdp_mode <- ACDP_union;
      | "u" -> params.ac_mark_mode <- AC_unmark;
      | "m" -> params.ac_mark_mode <- AC_mark;
      | "g" -> params.ac_mark_mode <- AC_guard;
      | _ -> erro arg;
    )
    | "-rdp", Some s -> (
      match s with
      | "naive" -> params.rdp_mode <- RDP_naive;
      | _ -> erro arg;
    )
    | "v", Some s -> (
      match s with
      | "p" | "problem" -> verbosity.(3) <- true;
      | "l" | "log" -> verbosity.(4) <- true;
      | "d" | "debug" -> verbosity.(5) <- true;
      | "d2" | "debug2" -> verbosity.(6) <- true;
      | _ ->
        let v = safe_atoi s arg in
        for i = 0 to Array.length verbosity - 1 do
          verbosity.(i) <- v > i;
        done
    )
    | "V", None ->
      for i = 0 to Array.length verbosity - 1 do
        verbosity.(i) <- false;
      done
    | "x", None ->
      for i = 0 to Array.length verbosity - 1 do
        verbosity.(i) <- false;
      done;
      params.result <- false;
      params.cpf <- true;
      params.naive_C <- true;
    | "x", Some file ->
      params.cpf <- true;
      params.cpf_to <- open_out file;
      params.naive_C <- true;
    | "-dup", None -> params.mode <- MODE_dup;
    | "-cond", None -> params.mode <- MODE_cond;
    | "-tcap", None -> params.edge_mode <- E_tcap;
    | "-edge", Some s -> params.edge_length <- safe_atoi s arg;
    | "t", mode -> (
      match mode with
      | Some "ho" -> params.mode <- MODE_higher_xml;
      | Some "x" -> params.mode <- MODE_xml;
      | Some str -> err ("Unknown transformation mode: " ^ str ^ "!");
      | _ -> params.mode <- MODE_through;
    )
    | _ -> erro arg;
  end else begin
    if params.file <> "" then err ("too many input file: " ^ arg ^ "!");
    params.file <- arg;
  end;
  i := !i + 1;
done;
set_strategy (
	if !strategy_str <> "" then
		Strategy.of_string !default_smt !strategy_str
	else if !strategy_file <> "" then
		Strategy.of_file !default_smt !strategy_file
	else
		Strategy.default !default_smt
);;
let cpf =
  if params.cpf then
    let os = new Io.pretty_wrap_out params.cpf_to in
    fun proc -> proc os
  else fun _ -> ()
