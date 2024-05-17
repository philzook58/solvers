(* File: tptp_config.ml *)
(* tptp_config.ml file with accumulator written by Frank Theiss for Chris Benzmueller's LEO-II *)
(*** Chad, Oct 2010: Added code to process THF ***)

open Syntax
open State
open Log
open Formula

let binop = function
  | "=>" -> PImplies
  | "<=" -> PRevImplies
  | "~|" -> PNOr
  | "~&" -> PNAnd
  | "<=>" -> PIff
  | "<~>" -> PNIff
  | "=" -> PEq
  | "!=" -> PNEq
  | _ -> raise Not_found

let unop = function
  | "~" -> PNeg
  | "!!" -> PForall
  | "??" -> PExists
  | _ -> raise Not_found

let pname = function
  | "$tType" -> PType
  | "$o" -> PPropTp
  | "$i" -> PIndTp
  | "$true" -> PTrue
  | "$false" -> PFalse
  | "&" -> PAnd
  | "|" -> POr
  | _ -> raise Not_found

let pand m n = PAp(PAp(PAnd,m),n)

let por m n = PAp(PAp(POr,m),n)

let rec formula_to_pretrm f =
  match f with
  | SymbolAt (f, a) -> PAp(formula_to_pretrm f, formula_to_pretrm a)
  | Symbol x ->
      begin
	try
	  pname x
	with
	| Not_found ->
	    try
	      unop x
	    with
	    | Not_found ->
		try
		  binop x
		with
		| Not_found ->
		    PName x
      end
  | Appl (Symbol "&",(f1::fl)) ->
      List.fold_left pand (formula_to_pretrm f1) (List.map formula_to_pretrm fl)
  | Appl (Symbol "|",(f1::fl)) ->
      List.fold_left por (formula_to_pretrm f1) (List.map formula_to_pretrm fl)
  | Appl (Symbol ">",[f1;f2]) ->
      PAr(formula_to_pretrm f1,formula_to_pretrm f2)
  | Appl (Symbol "$$type_formula",[f1;f2]) ->
      POf(formula_to_pretrm f1,formula_to_pretrm f2)
  | Appl (Symbol ":",[f1;f2]) ->
      POf(formula_to_pretrm f1,formula_to_pretrm f2)
  | Appl (Symbol ":=",[f1;f2]) ->
      PDef(formula_to_pretrm f1,formula_to_pretrm f2)
  | Appl (Symbol b,[f1;f2]) ->
      begin
	try
	  let a = binop b in
	  PAp(PAp(a,formula_to_pretrm f1),formula_to_pretrm f2)
	with
	| Not_found ->
	    raise (GenericSyntaxError("Could not convert to a preterm (unknown binary operator): " ^ (Formula.to_string f)))
      end
  | Appl (Symbol b,[f1]) ->
      begin
	try
	  let a = unop b in
	  PAp(a,formula_to_pretrm f1)
	with
	| Not_found ->
	    raise (GenericSyntaxError("Could not convert to a preterm (unknown unary operator): " ^ (Formula.to_string f)))
      end
  | Appl (Symbol "$$quantified",[Symbol "^";Appl (_,vl);body]) ->
      PLam(List.map tvar vl,formula_to_pretrm body)
  | Appl (Symbol "$$quantified",[Symbol "!";Appl (_,vl);body]) ->
      PAll(List.map tvar vl,formula_to_pretrm body)
  | Appl (Symbol "$$quantified",[Symbol "?";Appl (_,vl);body]) ->
      PEx(List.map tvar vl,formula_to_pretrm body)
  | Appl (Symbol "$$quantified",[Symbol "@+";Appl (_,[v]);body]) ->
      PChoice(tvar v,formula_to_pretrm body)
  | Appl (Symbol "$$quantified",[Symbol "!>";_;_])
  | Appl (Symbol "$$quantified",[Symbol "?*";_;_]) ->
      raise Polymorphism
  | _ ->
      raise (GenericSyntaxError("Could not convert to a preterm: " ^ (Formula.to_string f)))
and tvar v =
  match v with
    Appl (Symbol "$$typed_var",[Symbol x;f]) ->
      (x,formula_to_pretrm f)
  | _ -> raise (GenericSyntaxError("Could not convert to a tvar: " ^ (Formula.to_string v)))

let rec annotations_defn_p l =
  match l with
  | Appl(Symbol x,r) ->
      if (x = "abbrev") then true else annotations2_defn_p r
  | Symbol x -> if (x = "abbrev") then true else false
  | _ -> false
and annotations2_defn_p l =
  match l with
  | (x::r) -> annotations_defn_p x || annotations2_defn_p r
  | [] -> false

let rec annotation_strings l =
  match l with
  | Appl(Symbol "hashroot",[Symbol h]) ->
      if String.length h = 66 then
	[("hashroot",String.sub h 1 64)]
      else
	raise (Failure ("malformed hashroot " ^ h ^ "; should be '<hash>' where <hash> is 64 characters from [0-9a-f]"))
  | Appl(Symbol x,r) -> annotation_strings_l r
  | _ -> []
and annotation_strings_l l =
  match l with
  | l::r -> annotation_strings l @ annotation_strings_l r
  | [] -> []

let process_thf f =
  match f with
    Appl(Symbol "$$thf",[Symbol name;Symbol role;f;annotations]) ->
      if ((role = "definition") ||
          ((role = "axiom") && (annotations_defn_p annotations)))
      then
	declare_definition name role (formula_to_pretrm f) (annotation_strings annotations)
      else if (role = "type") then
	declare_typed_constant name role (formula_to_pretrm f) (annotation_strings annotations)
      else
	declare_thf_logic_formula name role (formula_to_pretrm f) (annotation_strings annotations)
  | Appl(Symbol "$$include",((Symbol file)::_)) -> (*** ignoring select ***)
      let file2 = String.sub file 1 (String.length file - 2) in (*** Remove the quotes ***)
      let dir2 = Filename.dirname file2 in
      if (dir2 = ".") then
	begin
	  if (!verbosity > 1) then Printf.printf "include file %s\n" file;
	  !st_include_fun (String.sub file 1 (String.length file - 2)); (*** Remove the quotes ***)
	  if (!verbosity > 1) then Printf.printf "included file %s\n" file;
	end
      else
	begin
	  if (!verbosity > 1) then Printf.printf "include file %s\n" file;
	  !st_find_read_thf_fun dir2 file2;
	  if (!verbosity > 1) then Printf.printf "included file %s\n" file;
	end
  | _ -> raise (GenericSyntaxError("Unhandled TPTP declaration. " ^ (Formula.to_string f)))

let accumulator f f_list = f::f_list

(* Processing from first to last, no formulae are kept *)
let accumulator2 f f_list = process_thf f
