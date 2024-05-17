(* File: syntax.ml *)
(* Author: Chad E Brown *)
(* Created: March 2008/September 2008 *)

open String

exception ParsingError of int * int * int * int * string
exception GenericSyntaxError of string
exception DeclareInd
exception Polymorphism

type pretrm =
    PName of string
  | PType | PPropTp | PIndTp | PIntTp | PRealTp | PTrue | PFalse | PIff | PNIff | PImplies | PRevImplies | POr | PNOr | PAnd | PNAnd | PEq | PNEq | PNeg | PForall | PExists
  | PInt of int
  | PReal of float
  | PAp of pretrm * pretrm
  | PULam of string list * pretrm
  | PLam of ((string * pretrm) list) * pretrm
  | PAll of ((string * pretrm) list) * pretrm
  | PEx of ((string * pretrm) list) * pretrm
  | PExU of string * pretrm * pretrm
  | PChoice of (string * pretrm) * pretrm
  | PAr of pretrm * pretrm
  | POf of pretrm * pretrm
  | PDef of pretrm * pretrm
  | PLet of string * pretrm * pretrm
  | PTLet of string * pretrm * pretrm * pretrm

type prectx = (string option * pretrm option * pretrm option) list

let rec prectx_lam c m =
  match c with
  | (Some x,Some a,None)::c' -> prectx_lam c' (PLam([(x,a)],m))
  | (Some x,_,Some n)::c' -> prectx_lam c' (PLet(x,n,m))
  | (None,Some p,None)::c' -> prectx_lam c' m
  | _::_ -> raise (GenericSyntaxError "Impossible prectx case")
  | [] -> m

let rec prectx_all c m =
  match c with
  | (Some x,Some a,None)::c' -> prectx_all c' (PAll([(x,a)],m))
  | (Some x,_,Some n)::c' -> prectx_all c' (PLet(x,n,m))
  | (None,Some p,None)::c' -> prectx_all c' (PAp(PAp(PImplies,p),m))
  | _::_ -> raise (GenericSyntaxError "Impossible prectx case")
  | [] -> m

let rec prectx_ar c m =
  match c with
  | (Some x,Some a,None)::c' -> prectx_ar c' (PAr(a,m))
  | (Some x,_,Some n)::c' -> prectx_ar c' m
  | (None,Some p,None)::c' -> prectx_ar c' m
  | _::_ -> raise (GenericSyntaxError "Impossible prectx case")
  | [] -> m

let rec pretrm_str m =
  match m with
  | PName x -> x
  | PType -> "$type"
  | PPropTp -> "$o"
  | PIndTp -> "$i"
  | PIntTp -> "$int"
  | PRealTp -> "$real"
  | PTrue -> "$true"
  | PFalse -> "$false"
  | PIff -> "$iff"
  | PNIff -> "$niff"
  | PImplies -> "$implies"
  | PRevImplies -> "$revimplies"
  | POr -> "$or"
  | PNOr -> "$Nor"
  | PAnd -> "$and"
  | PNAnd -> "$Nand"
  | PEq -> "$eq"
  | PNEq -> "$neq"
  | PNeg -> "~"
  | PForall -> "!!"
  | PExists -> "??"
  | PInt i -> string_of_int i
  | PReal z -> string_of_float z
  | PAp(n,p) -> "(" ^ (pretrm_str n) ^ " @ " ^ (pretrm_str p) ^ ")"
  | PULam(xl,m) -> "(^ [" ^ (String.concat "," xl) ^ "] " ^ (pretrm_str m) ^ ")"
  | PLam(xl,m) -> "(^ [" ^ (String.concat "," (List.map (fun (x,a) -> x ^ ":" ^ (pretrm_str a)) xl)) ^ "] " ^ (pretrm_str m) ^ ")"
  | PAll(xl,m) -> "(! [" ^ (String.concat "," (List.map (fun (x,a) -> x ^ ":" ^ (pretrm_str a)) xl)) ^ "] " ^ (pretrm_str m) ^ ")"
  | PEx(xl,m) -> "(? [" ^ (String.concat "," (List.map (fun (x,a) -> x ^ ":" ^ (pretrm_str a)) xl)) ^ "] " ^ (pretrm_str m) ^ ")"
  | PExU(x,a,m) -> "(?! [" ^ x ^ ":" ^ (pretrm_str a) ^ "] " ^ (pretrm_str m) ^ ")"
  | PChoice((x,xa),m) -> "(@+ [" ^ x ^ ":" ^ (pretrm_str xa) ^ "] " ^ (pretrm_str m) ^ ")"
  | PAr(n,p) -> "(" ^ (pretrm_str n) ^ " > " ^ (pretrm_str p) ^ ")"
  | POf(n,p) -> "(" ^ (pretrm_str n) ^ " : " ^ (pretrm_str p) ^ ")"
  | PDef(n,p) -> "(" ^ (pretrm_str n) ^ " := " ^ (pretrm_str p) ^ ")"
  | PLet(x,n,p) -> "(" ^ x ^ " := " ^ (pretrm_str n) ^ " in " ^ (pretrm_str p) ^ ")"
  | PTLet(x,a,n,p) -> "(" ^ x ^ " : " ^ (pretrm_str a) ^ " := " ^ (pretrm_str n) ^ " in " ^ (pretrm_str p) ^ ")"

type input =
    DeclareTHF of string * string * pretrm
  | Include of string


(*** Print preterms as Coq ***)
let coqify_name_1 x =
  let r = ref "" in
  if (x = "$i") then r := "i" else
  begin
    let fst = ref true in
    String.iter
      (fun c ->
	let co = Char.code c in
	if (((co >= 65) && (co <= 90)) || ((co >= 97) && (co <= 122))) then
	  begin
	    fst := false;
	    r := (!r) ^ (Char.escaped c)
	  end
	else
	  begin
	    if ((!fst) && (co <> 95)) then r := "_";
	    fst := false;
	    if ((co >= 48) && (co <= 57)) then
	      r := (!r) ^ (Char.escaped c)
	    else if (co = 39) then
	      r := (!r) ^ "'"
	    else if (co = 95) then
	      r := (!r) ^ "_";
	    (*** omit any other characters, relying on coqify_name_0 to ensure it's fresh ***)
	  end
      )
      x;
    if ((!r) = "_") then r := "_X";
  end;
  r

let coqify_name_0 x h =
  let r = coqify_name_1 x in
  while (Hashtbl.mem h (!r)) do
    r := (!r) ^ "'"; (*** add primes until it's fresh ***)
  done;
  (!r)

let coqify_name x h1 h2 =
  let y = coqify_name_0 x h2 in
  Hashtbl.add h1 x y;
  Hashtbl.add h2 y ();
  y
  

let rec print_pretrm_coq c m h hu lp rp =
  match m with
  | PName x ->
      Printf.fprintf c "%s" (Hashtbl.find h x)
  | PType -> Printf.fprintf c "SType"
  | PPropTp -> Printf.fprintf c "o"
  | PIndTp ->
      Printf.fprintf c "%s" (Hashtbl.find h "$i")
  | PTrue -> Printf.fprintf c "True"
  | PFalse -> Printf.fprintf c "False"
  | PAp(PNeg,m1) ->
      if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  print_pretrm_coq c m1 h hu 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  print_pretrm_coq c m1 h hu 30 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PForall,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "SPi _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "(SPi _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PExists,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "SSigma _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "(SSigma _ ";
	  print_pretrm_coq c m1 h hu (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PImplies,m1),m2) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq c m1 h hu lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PRevImplies,m2),m1) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq c m1 h hu lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq c m2 h hu 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PAnd,m1),m2) ->
      if ((lp < 21) && (rp < 20)) then
	begin
	  print_pretrm_coq c m1 h hu lp 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq c m2 h hu 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq c m2 h hu 20 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(POr,m1),m2) ->
      if ((lp < 19) && (rp < 18)) then
	begin
	  print_pretrm_coq c m1 h hu lp 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq c m2 h hu 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq c m2 h hu 18 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PIff,m1),m2) ->
      if ((lp < 14) && (rp < 14)) then
	begin
	  print_pretrm_coq c m1 h hu lp 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq c m2 h hu 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq c m2 h hu 14 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PEq,m1),m2) ->
      if ((lp < 40) && (rp < 40)) then
	begin
	  print_pretrm_coq c m1 h hu lp 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq c m2 h hu 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq c m2 h hu 40 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PNEq,m1),m2) ->
      if (rp >= 40) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 40;
      Printf.fprintf c " = ";
      print_pretrm_coq c m2 h hu 40 (-1);
      Printf.fprintf c ")";
      if (rp >= 40) then Printf.fprintf c ")";
  | PAp(PAp(PNIff,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 14;
      Printf.fprintf c " <-> ";
      print_pretrm_coq c m2 h hu 14 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNAnd,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 20;
      Printf.fprintf c " //\ ";
      print_pretrm_coq c m2 h hu 21 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNOr,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq c m1 h hu (-1) 18;
      Printf.fprintf c " \\/ ";
      print_pretrm_coq c m2 h hu 19 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PIff -> Printf.fprintf c "Siff"
  | POr -> Printf.fprintf c "Sor"
  | PAnd -> Printf.fprintf c "Sand"
  | PNeg -> Printf.fprintf c "Snot"
  | PForall ->
      Printf.fprintf c "(SPi _)";
  | PExists ->
      Printf.fprintf c "(SSigma _)";
  | PEq ->
      Printf.fprintf c "(Seq _)";
  | PAp(m1,m2) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  print_pretrm_coq c m1 h hu lp 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq c m2 h hu 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq c m2 h hu 5001 (-1);
	  Printf.fprintf c ")";
	end
  | PAr(m1,m2) ->
      if ((lp < 71) && (rp < 70)) then
	begin
	  print_pretrm_coq c m1 h hu lp 71;
	  Printf.fprintf c " --> ";
	  print_pretrm_coq c m2 h hu 70 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq c m1 h hu (-1) 71;
	  Printf.fprintf c " --> ";
	  print_pretrm_coq c m2 h hu 70 (-1);
	  Printf.fprintf c ")";
	end
  | POf(n,p) -> print_pretrm_coq c n h hu lp rp
(***  | PDef(n,p) -> print_pretrm_coq c n h hu lp rp ***)
  | PULam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_ulam_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PLam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_lam_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PAll(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PEx(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq c xl m h hu
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PChoice((x,xa),m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  let y = coqify_name x h hu in
	  Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	  Hashtbl.remove hu y; (*** free y to print the domain ***)
	  Printf.fprintf c "Sepsilon (fun ";
	  Printf.fprintf c " %s" y;
	  Printf.fprintf c ":";
	  print_pretrm_coq c xa h hu (-1) (-1);
	  Hashtbl.add h x y; (*** put y back on ***)
	  Hashtbl.add hu y (); (*** put y back on ***)
	  Printf.fprintf c " => ";
	  print_pretrm_coq c m h hu (-1) (-1);
	  Hashtbl.remove h x; (*** pops y from the values of x ***)
	  Hashtbl.remove hu y; (*** free y to be used later ***)
	  Printf.fprintf c ")";
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | _ -> raise (GenericSyntaxError ("Unknown pretrm case print Coq version : " ^ (pretrm_str m)))
and print_ulam_coq c xl m h hu =
  match xl with
    (x::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c " ";
	Printf.fprintf c "%s" y;
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_ulam_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq c m h hu (-1) (-1)
      end
and print_lam_coq c xl m h hu =
  match xl with
    ((x,a)::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq c a h hu (-1) (-1); Printf.fprintf c ")";
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_lam_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq c m h hu (-1) (-1)
      end
and print_all_coq c xl m h hu =
  match xl with
    ((x,a)::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq c a h hu (-1) (-1); Printf.fprintf c ")";
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_all_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	Printf.fprintf c ", ";
	print_pretrm_coq c m h hu (-1) (-1)
      end
and print_ex_coq c xl m h hu =
  match xl with
    ((x,a)::xr) ->
      begin
	let y = coqify_name x h hu in
	Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	Hashtbl.remove hu y; (*** free y to print the domain ***)
	Printf.fprintf c "exists"; Printf.fprintf c " %s" y; Printf.fprintf c ":"; print_pretrm_coq c a h hu (-1) (-1); Printf.fprintf c ", ";
	Hashtbl.add h x y; (*** put y back on ***)
	Hashtbl.add hu y (); (*** put y back on ***)
	print_ex_coq c xr m h hu;
	Hashtbl.remove h x; (*** pops y from the values of x ***)
	Hashtbl.remove hu y; (*** free y to be used later ***)
      end
  | [] ->
      begin
	print_pretrm_coq c m h hu (-1) (-1)
      end

(*FIXME repeating the code is a bad idea. this is repeated from print_pretrm_coq*)
let rec print_pretrm_isar c m h hu lp rp =
  match m with
    | PName x ->
        Printf.fprintf c "%s" (Hashtbl.find h x)
    | PType -> (* Printf.fprintf c "SType" *) ()
    | PPropTp -> Printf.fprintf c "o"
    | PIndTp ->
        Printf.fprintf c "%s" (Hashtbl.find h "$i") (*FIXME what's set as $i? where is this set?*)  
    | PTrue -> Printf.fprintf c "True"
    | PFalse -> Printf.fprintf c "False"
    | PAp(PNeg,m1) ->
        if ((lp < 0) && (rp < 30)) then
	        begin
	          Printf.fprintf c "~ ";
	          print_pretrm_isar c m1 h hu 30 rp;
	        end
        else
	        begin
	          Printf.fprintf c "(~ ";
	          print_pretrm_isar c m1 h hu 30 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PForall,m1) ->
        if ((lp < 0) && (rp < 0)) then
	        begin
	          (* Printf.fprintf c "SPi _ "; *)
	          Printf.fprintf c "All";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	        end
        else
	        begin
	          (* Printf.fprintf c "(SPi _ "; *)
	          Printf.fprintf c "(All ";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PExists,m1) ->
        if ((lp < 0) && (rp < 0)) then
	        begin
	          (* Printf.fprintf c "SSigma _ "; *)
	          Printf.fprintf c "Ex ";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	        end
        else
	        begin
	          (* Printf.fprintf c "(SSigma _ "; *)
	          Printf.fprintf c "(Ex ";
	          print_pretrm_isar c m1 h hu (-1) (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PImplies,m1),m2) ->
(*
        if ((lp < 17) && (rp < 16)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PRevImplies,m2),m1) ->
(*
        if ((lp < 17) && (rp < 16)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 17;
	          Printf.fprintf c " --> ";
	          print_pretrm_isar c m2 h hu 16 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PAnd,m1),m2) ->
(*
        if ((lp < 21) && (rp < 20)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 21;
	          Printf.fprintf c " & ";
	          print_pretrm_isar c m2 h hu 20 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 21;
	          Printf.fprintf c " & ";
	          print_pretrm_isar c m2 h hu 20 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(POr,m1),m2) ->
(*FIXME excluding parentheses can lead to parse problems on the Isabelle side
        if ((lp < 19) && (rp < 18)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 19;
	          Printf.fprintf c " | ";
	          print_pretrm_isar c m2 h hu 18 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 19;
	          Printf.fprintf c " | ";
	          print_pretrm_isar c m2 h hu 18 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PIff,m1),m2) ->
(*
        if ((lp < 14) && (rp < 14)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 14;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 14 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 14;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 14 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PEq,m1),m2) ->
(*
        if ((lp < 40) && (rp < 40)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 40;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 40 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 40;
	          Printf.fprintf c " = ";
	          print_pretrm_isar c m2 h hu 40 (-1);
	          Printf.fprintf c ")";
	        end
    | PAp(PAp(PNEq,m1),m2) ->
(*        if (rp >= 40) then*) Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 40;
        Printf.fprintf c " = ";
        print_pretrm_isar c m2 h hu 40 (-1);
        Printf.fprintf c ")";
(*        if (rp >= 40) then*) Printf.fprintf c ")";
    | PAp(PAp(PNIff,m1),m2) ->
(*        if (rp >= 30) then*) Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 14;
        Printf.fprintf c " = ";
        print_pretrm_isar c m2 h hu 14 (-1);
        Printf.fprintf c ")";
(*        if (rp >= 30) then*) Printf.fprintf c ")";
    | PAp(PAp(PNAnd,m1),m2) ->
(*        if (rp >= 30) then*) Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 20;
        Printf.fprintf c " & ";
        print_pretrm_isar c m2 h hu 21 (-1);
        Printf.fprintf c ")";
(*        if (rp >= 30) then*) Printf.fprintf c ")";
    | PAp(PAp(PNOr,m1),m2) ->
(*        if (rp >= 30) then*) Printf.fprintf c "(";
        Printf.fprintf c "~ (";
        print_pretrm_isar c m1 h hu (-1) 18;
        Printf.fprintf c " | ";
        print_pretrm_isar c m2 h hu 19 (-1);
        Printf.fprintf c ")";
(*        if (rp >= 30) then*) Printf.fprintf c ")";
    | PIff -> Printf.fprintf c "(=)"
    | POr -> Printf.fprintf c "(|)"
    | PAnd -> Printf.fprintf c "(&)"
    | PNeg -> Printf.fprintf c "Not"
    | PForall ->
        Printf.fprintf c "All";
    | PExists ->
        Printf.fprintf c "Ex";
    | PEq ->
        Printf.fprintf c "(op =)";
    | PAp(m1,m2) ->
(*
        if ((lp < 5000) && (rp < 5001)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 5000;
	          Printf.fprintf c " ";
	          print_pretrm_isar c m2 h hu 5001 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 5000;
	          Printf.fprintf c " ";
	          print_pretrm_isar c m2 h hu 5001 (-1);
	          Printf.fprintf c ")";
	        end
    | PAr(m1,m2) ->
(*
        if ((lp < 71) && (rp < 70)) then
	        begin
	          print_pretrm_isar c m1 h hu lp 71;
	          Printf.fprintf c " => ";
	          print_pretrm_isar c m2 h hu 70 rp;
	        end
        else
*)
	        begin
	          Printf.fprintf c "(";
	          print_pretrm_isar c m1 h hu (-1) 71;
	          Printf.fprintf c " => ";
	          print_pretrm_isar c m2 h hu 70 (-1);
	          Printf.fprintf c ")";
	        end
    | POf(n,p) -> print_pretrm_isar c n h hu lp rp
(***  | PDef(n,p) -> print_pretrm_isar c n h hu lp rp ***)
    | PULam(xl,m) ->
        begin
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c "(";
	        begin
	          Printf.fprintf c "%% ";
	          print_ulam_isar c xl m h hu
	        end;
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c ")";
        end
    | PLam(xl,m) ->
        begin
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c "(";
	        begin
	          Printf.fprintf c "%% ";
	          print_lam_isar c xl m h hu
	        end;
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c ")";
        end
    | PAll(xl,m) ->
        begin
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c "(";
	        begin
	          Printf.fprintf c "!";
	          print_all_isar c xl m h hu
	        end;
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c ")";
        end
    | PEx(xl,m) ->
        begin
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c "(";
	        begin
	          print_ex_isar c xl m h hu
	        end;
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c ")";
        end
    | PChoice((x,xa),m) ->
        begin
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c "(";
	        begin
	          let y = coqify_name x h hu in
	            Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	            Hashtbl.remove hu y; (*** free y to print the domain ***)
	            Printf.fprintf c "Eps (%% ";
	            Printf.fprintf c " %s" y;
	            Printf.fprintf c "::";
	            print_pretrm_isar c xa h hu (-1) (-1);
	            Hashtbl.add h x y; (*** put y back on ***)
	            Hashtbl.add hu y (); (*** put y back on ***)
	            Printf.fprintf c " . ";
	            print_pretrm_isar c m h hu (-1) (-1);
	            Hashtbl.remove h x; (*** pops y from the values of x ***)
	            Hashtbl.remove hu y; (*** free y to be used later ***)
	            Printf.fprintf c ")";
	        end;
(*	        if ((lp >= 0) || (rp >= 0)) then*) Printf.fprintf c ")";
        end
    | _ -> raise (GenericSyntaxError ("Unknown pretrm case print Coq version : " ^ (pretrm_str m))) (*FIXME this wasnt changed from the original function*)
and print_ulam_isar c xl m h hu =
  match xl with
      (x::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c " ";
	          Printf.fprintf c "%s" y;
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_ulam_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        Printf.fprintf c " . ";
	        print_pretrm_isar c m h hu (-1) (-1)
        end
and print_lam_isar c xl m h hu =
  match xl with
      ((x,a)::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_pretrm_isar c a h hu (-1) (-1); Printf.fprintf c ")";
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_lam_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        Printf.fprintf c " . ";
	        print_pretrm_isar c m h hu (-1) (-1)
        end
and print_all_isar c xl m h hu =
  match xl with
      ((x,a)::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c "::"; print_pretrm_isar c a h hu (-1) (-1); Printf.fprintf c ")";
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_all_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        Printf.fprintf c ". ";
	        print_pretrm_isar c m h hu (-1) (-1)
        end
and print_ex_isar c xl m h hu =
  match xl with
      ((x,a)::xr) ->
        begin
	        let y = coqify_name x h hu in
	          Hashtbl.remove h x; (*** pops y from the values of x to print domain ***)
	          Hashtbl.remove hu y; (*** free y to print the domain ***)
	          Printf.fprintf c "?"; Printf.fprintf c " %s" y; Printf.fprintf c "::"; print_pretrm_isar c a h hu (-1) (-1); Printf.fprintf c ". ";
	          Hashtbl.add h x y; (*** put y back on ***)
	          Hashtbl.add hu y (); (*** put y back on ***)
	          print_ex_isar c xr m h hu;
	          Hashtbl.remove h x; (*** pops y from the values of x ***)
	          Hashtbl.remove hu y; (*** free y to be used later ***)
        end
    | [] ->
        begin
	        print_pretrm_isar c m h hu (-1) (-1)
        end


let rec print_pretrm_coq2 c m lp rp =
  match m with
  | PName x ->
      Printf.fprintf c "%s" x
  | PType -> Printf.fprintf c "Type"
  | PPropTp -> Printf.fprintf c "prop"
  | PIndTp ->
      Printf.fprintf c "set"
  | PTrue -> Printf.fprintf c "True"
  | PFalse -> Printf.fprintf c "False"
  | PAp(PNeg,m1) ->
      if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  print_pretrm_coq2 c m1 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  print_pretrm_coq2 c m1 30 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PForall,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "(fun p => forall x, p x) ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "((fun p => forall x, p x) ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PExists,m1) ->
      if ((lp < 0) && (rp < 0)) then
	begin
	  Printf.fprintf c "ex _ ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	end
      else
	begin
	  Printf.fprintf c "(ex _ ";
	  print_pretrm_coq2 c m1 (-1) (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PImplies,m1),m2) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq2 c m1 lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PRevImplies,m2),m1) ->
      if ((lp < 17) && (rp < 16)) then
	begin
	  print_pretrm_coq2 c m1 lp 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 17;
	  Printf.fprintf c " -> ";
	  print_pretrm_coq2 c m2 16 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PAnd,m1),m2) ->
      if ((lp < 21) && (rp < 20)) then
	begin
	  print_pretrm_coq2 c m1 lp 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq2 c m2 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 21;
	  Printf.fprintf c " /\\ ";
	  print_pretrm_coq2 c m2 20 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(POr,m1),m2) ->
      if ((lp < 19) && (rp < 18)) then
	begin
	  print_pretrm_coq2 c m1 lp 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq2 c m2 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 19;
	  Printf.fprintf c " \\/ ";
	  print_pretrm_coq2 c m2 18 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PIff,m1),m2) ->
      if ((lp < 14) && (rp < 14)) then
	begin
	  print_pretrm_coq2 c m1 lp 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq2 c m2 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 14;
	  Printf.fprintf c " <-> ";
	  print_pretrm_coq2 c m2 14 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PEq,m1),m2) ->
      if ((lp < 40) && (rp < 40)) then
	begin
	  print_pretrm_coq2 c m1 lp 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq2 c m2 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 40;
	  Printf.fprintf c " = ";
	  print_pretrm_coq2 c m2 40 (-1);
	  Printf.fprintf c ")";
	end
  | PAp(PAp(PNEq,m1),m2) ->
      if (rp >= 40) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 40;
      Printf.fprintf c " = ";
      print_pretrm_coq2 c m2 40 (-1);
      Printf.fprintf c ")";
      if (rp >= 40) then Printf.fprintf c ")";
  | PAp(PAp(PNIff,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 14;
      Printf.fprintf c " <-> ";
      print_pretrm_coq2 c m2 14 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNAnd,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 20;
      Printf.fprintf c " //\ ";
      print_pretrm_coq2 c m2 21 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PAp(PAp(PNOr,m1),m2) ->
      if (rp >= 30) then Printf.fprintf c "(";
      Printf.fprintf c "~ (";
      print_pretrm_coq2 c m1 (-1) 18;
      Printf.fprintf c " \\/ ";
      print_pretrm_coq2 c m2 19 (-1);
      Printf.fprintf c ")";
      if (rp >= 30) then Printf.fprintf c ")";
  | PIff -> Printf.fprintf c "iff"
  | POr -> Printf.fprintf c "or"
  | PAnd -> Printf.fprintf c "and"
  | PNeg -> Printf.fprintf c "not"
  | PForall ->
      Printf.fprintf c "(fun p => forall x, p x)";
  | PExists ->
      Printf.fprintf c "(ex _)";
  | PEq ->
      Printf.fprintf c "(eq _)";
  | PAp(m1,m2) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  print_pretrm_coq2 c m1 lp 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq2 c m2 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 5000;
	  Printf.fprintf c " ";
	  print_pretrm_coq2 c m2 5001 (-1);
	  Printf.fprintf c ")";
	end
  | PAr(m1,m2) ->
      if ((lp < 71) && (rp < 70)) then
	begin
	  print_pretrm_coq2 c m1 lp 71;
	  Printf.fprintf c " > ";
	  print_pretrm_coq2 c m2 70 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  print_pretrm_coq2 c m1 (-1) 71;
	  Printf.fprintf c " > ";
	  print_pretrm_coq2 c m2 70 (-1);
	  Printf.fprintf c ")";
	end
  | POf(n,p) -> print_pretrm_coq2 c n lp rp
(***  | PDef(n,p) -> print_pretrm_coq2 c n lp rp ***)
  | PULam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_ulam_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PLam(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_lam_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PAll(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PEx(xl,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq2 c xl m
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PChoice((x,xa),m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "Eps _ (fun ";
	  Printf.fprintf c " %s" x;
	  Printf.fprintf c ":";
	  print_pretrm_coq2 c xa (-1) (-1);
	  Printf.fprintf c " => ";
	  print_pretrm_coq2 c m (-1) (-1);
	  Printf.fprintf c ")";
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PLet(x,m1,m2) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	Printf.fprintf c "let %s := " (if (x = "") then "_" else x);
	print_pretrm_coq2 c m1 (-1) (-1);
	Printf.fprintf c " in ";
	print_pretrm_coq2 c m2 (-1) (-1);
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | PTLet(x,a1,m1,m2) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	Printf.fprintf c "let %s : " (if (x = "") then "_" else x);
	print_pretrm_coq2 c a1 (-1) (-1);
	Printf.fprintf c " := ";
	print_pretrm_coq2 c m1 (-1) (-1);
	Printf.fprintf c " in ";
	print_pretrm_coq2 c m2 (-1) (-1);
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | _ -> raise (GenericSyntaxError ("Unknown pretrm case print Coq version : " ^ (pretrm_str m)))
and print_ulam_coq2 c xl m =
  match xl with
  | (x::xr) when x = "" ->
      begin
	Printf.fprintf c " _";
	print_ulam_coq2 c xr m;
      end
  | (x::xr) ->
      begin
	let y = x in
	Printf.fprintf c " "; Printf.fprintf c "%s" y;
	print_ulam_coq2 c xr m;
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq2 c m (-1) (-1)
      end
and print_lam_coq2 c xl m =
  match xl with
  | ((x,a)::xr) when x = "" ->
      begin
	Printf.fprintf c " (_"; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_lam_coq2 c xr m;
      end
  | ((x,a)::xr) ->
      begin
	let y = x in
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_lam_coq2 c xr m;
      end
  | [] ->
      begin
	Printf.fprintf c " => ";
	print_pretrm_coq2 c m (-1) (-1)
      end
and print_all_coq2 c xl m =
  match xl with
  | ((x,a)::xr) when x = "" ->
      begin
	Printf.fprintf c " (_"; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_all_coq2 c xr m;
      end
  | ((x,a)::xr) ->
      begin
	let y = x in
	Printf.fprintf c " ("; Printf.fprintf c "%s" y; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ")";
	print_all_coq2 c xr m;
      end
  | [] ->
      begin
	Printf.fprintf c ", ";
	print_pretrm_coq2 c m (-1) (-1)
      end
and print_ex_coq2 c xl m =
  match xl with
  | ((x,a)::xr) when x = "" ->
      begin
	Printf.fprintf c "exists _:"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ", ";
	print_ex_coq2 c xr m;
      end
  | ((x,a)::xr) ->
      begin
	let y = x in
	Printf.fprintf c "exists"; Printf.fprintf c " %s" y; Printf.fprintf c ":"; print_pretrm_coq2 c a (-1) (-1); Printf.fprintf c ", ";
	print_ex_coq2 c xr m;
      end
  | [] ->
      begin
	print_pretrm_coq2 c m (-1) (-1)
      end
