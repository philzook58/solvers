(* Stateful term printing *)

open Term

let coq_used_names : (string,unit) Hashtbl.t = Hashtbl.create 100
let coq_names : (string,string) Hashtbl.t = Hashtbl.create 100
let coq_hyp_names : (string,string) Hashtbl.t = Hashtbl.create 100

(** Translate de Bruijn indices to variables**)
module Variables = struct
  (** next variable counter and list of used variable names**)
  type t = int * (string list)
  let make () = (1,[])
  (** Input: Variables (n,v)
    Output: Variables (m,v') with m>n and a new variable name x in v'  **)
  let rec push (n,v) =
    let x = "X" ^ (string_of_int n) in
    let n = n+1 in
    if (Hashtbl.mem coq_used_names x)
      then push (n,v)
      else (n,x::v)
  let top (_,v) = List.hd v
  let get i (_,v) = List.nth v i
end

let coq_keywords =
[ "as"
; "at"
; "cofix"
; "else"
; "end"
; "exists2"
; "fix"
; "for"
; "forall"
; "fun"
; "if"
; "IF"
; "in"
; "let"
; "match"
; "mod"
; "Prop"
; "return"
; "Set"
; "then"
; "Type"
; "using"
; "where"
; "with"
(*** Avoid certain names used by stt in Coq ***)
; "SType"
; "Sar"
; "o"
; "prop"
; "Sepsilon"
; "forall"
; "exists"
; "False"
; "True"
; "not"
; "Snot"
; "and"
; "Sand"
; "or"
; "Sor"
; "iff"
; "Siff"
; "ex"
; "SSigma"
; "SPi"
; "eq"
; "Seq"
; "I"
; "FalseE"
; "conj"
; "proj1"
; "proj2"
; "and_ind"
; "or_introl"
; "or_intror"
; "or_ind"
; "ex_intro"
; "ex_ind"
; "refl_equal"
; "eq_ind"
; "SinhE"
; "classic"
; "NNPP"
; "prop_ext"
; "functional_extensionality"
; "Sepsilon_spec"
(*** Other names to avoid ***)
; "claim"
(*FIXME add isar keywords*)
; "thm"
; "lemma"
; "case"
]

let termP_init () =
  List.iter (fun w -> Hashtbl.add coq_used_names w ()) coq_keywords

let tstpizename x =
  if (String.length x > 0) then
    if (String.get x 0 = '_') then
      "eigen" ^ x
    else if (String.get x 0 = '@') then
      String.sub x 1 ((String.length x) - 1)
    else
      if ((String.length x > 5) && (String.sub x 0 5 = "eigen")) then
        "not" ^ x
      else
        x
  else x

let isarize_name x =
  if String.length x > 0 then
    if String.get x 0 = '_' then
      "eigen" ^ x
    else if String.get x 0 = '@' then
      String.sub x 1 ((String.length x) - 1)
    else
      if (String.length x > 5 && String.sub x 0 5 = "eigen") then
        "not" ^ x
      else
        (*Rename constants to avoid clashes with keywords*)
        let x =
          try Hashtbl.find coq_names x with
              Not_found -> x
        in x
  else failwith "Name cannot have zero length"



(** Input: out_channel c, term m, list of bound variables
Invariant: m is closed, if  it is enclosed in quantifiers for the bound variables
	Prints the term m on the channel c**)
let rec trm_to_coq c m bound lp rp =
  match m with
    Name(x,_) -> (* Definitions *)
	let x = try (Hashtbl.find coq_names x) with Not_found -> x in
      Printf.fprintf c "%s" x
  | False -> (* Bottom *)
	Printf.fprintf c "False"
  | Ap(Ap(Imp,m1),False) ->  (* Negation *)
	if ((lp < 0) && (rp < 30)) then
	begin
	  Printf.fprintf c "~ ";
	  trm_to_coq c m1 bound 30 rp;
	end
      else
	begin
	  Printf.fprintf c "(~ ";
	  trm_to_coq c m1 bound 30 (-1);
	  Printf.fprintf c ")";
	end
   | Ap(Ap(Imp,m1),m2) -> (* Implication *)
      if ((lp < 17) && (rp < 16)) then
	begin
	  trm_to_coq c m1 bound lp 17;
	  Printf.fprintf c " -> ";
	  trm_to_coq c m2 bound 16 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 17;
	  Printf.fprintf c " -> ";
	  trm_to_coq c m2 bound 16 (-1);
	  Printf.fprintf c ")";
	end
  | Ap(Imp,m1) -> trm_to_coq c (Lam(Prop,Ap(Ap(Imp,shift m1 0 1),DB(0,Prop)))) bound lp rp;
  | Imp -> trm_to_coq c (Lam(Prop,Lam(Prop,Ap(Ap(Imp,DB(1,Prop)),DB(0,Prop))))) bound lp rp; 
  | Ap(Forall(a),Lam(_,m1)) -> (* forall with Lam *)
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "forall";
	  print_all_coq c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Forall(a) ->
      begin
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c "(";
	Printf.fprintf c "SPi "; print_stp_coq c a coq_names true;
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c ")";
      end
  | Ap(Ap(Eq(a),m1),m2) -> (* Equality *)
      if ((lp < 40) && (rp < 40)) then
	begin
	  trm_to_coq c m1 bound lp 40;
	  Printf.fprintf c " = ";
	  trm_to_coq c m2 bound 40 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 40;
	  Printf.fprintf c " = ";
	  trm_to_coq c m2 bound 40 (-1);
	  Printf.fprintf c ")";
	end
  | Eq(a) ->
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "Seq ";
	  print_stp_coq c a coq_names true;
	end
      else
	begin
	  Printf.fprintf c "(Seq ";
	  print_stp_coq c a coq_names true;
	  Printf.fprintf c ")";
	end
(*** I'm now always explicitly giving the Stype
  | Ap(Choice(a),m) ->   (* Choice *)
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "@Sepsilon ";
	  trm_to_coq c m bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(@Sepsilon ";

	  trm_to_coq c m bound 5001 (-1);
	  Printf.fprintf c ")";
	end
***)
  | Choice(a) ->
      if ((lp < 5000) && (rp < 5001)) then
	begin
	  Printf.fprintf c "@Sepsilon ";
	  print_stp_coq c a coq_names true
	end
      else
	begin
	  Printf.fprintf c "(@Sepsilon ";
	  print_stp_coq c a coq_names true;
	  Printf.fprintf c ")"
	end
  | True -> (* Top *)
	Printf.fprintf c "True"
  | Ap(Ap(And,m1),m2) -> (* conjunction *)
      if ((lp < 21) && (rp < 20)) then
	begin
	  trm_to_coq c m1 bound lp 21;
	  Printf.fprintf c " /\\ ";
	  trm_to_coq c m2 bound 20 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 21;
	  Printf.fprintf c " /\\ ";
	  trm_to_coq c m2 bound 20 (-1);
	  Printf.fprintf c ")";
	end
  | And ->Printf.fprintf c "and"
  | Ap(Ap(Or,m1),m2) -> (* disjunction *)
      if ((lp < 19) && (rp < 18)) then
	begin
	  trm_to_coq c m1 bound lp 19;
	  Printf.fprintf c " \\/ ";
	  trm_to_coq c m2 bound 18 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 19;
	  Printf.fprintf c " \\/ ";
	  trm_to_coq c m2 bound 18 (-1);
	  Printf.fprintf c ")";
	end
  | Or -> Printf.fprintf c "or"
  | Ap(Ap(Iff,m1),m2) -> (* equivalenz *)
      if ((lp < 14) && (rp < 14)) then
	begin
	  trm_to_coq c m1 bound lp 14;
	  Printf.fprintf c " <-> ";
	  trm_to_coq c m2 bound 14 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 14;
	  Printf.fprintf c " <-> ";
	  trm_to_coq c m2 bound 14 (-1);
	  Printf.fprintf c ")";
	end
  | Iff -> Printf.fprintf c "iff"
  | Neg -> Printf.fprintf c "not"
  | Ap(Exists(a),Lam(_,m1)) -> (* exist *)
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  print_ex_coq c a m1 bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Exists(a) ->
      begin
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c "(";
	Printf.fprintf c "SSigma "; print_stp_coq c a coq_names true;
	if ((lp >= 5000) || (rp >= 5001)) then Printf.fprintf c ")";
      end
  | DB(i,a) -> (* Bound variable *)
	Printf.fprintf c "%s" (Variables.get i bound)
  | Lam(a,m) ->
      begin
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c "(";
	begin
	  Printf.fprintf c "fun";
	  print_lam_coq c a m bound
	end;
	if ((lp >= 0) || (rp >= 0)) then Printf.fprintf c ")";
      end
  | Ap(m1,m2) ->
	if ((lp < 5000) && (rp < 5001)) then
	begin
	  trm_to_coq c m1 bound lp 5000;
	  Printf.fprintf c " ";
	  trm_to_coq c m2 bound 5001 rp;
	end
      else
	begin
	  Printf.fprintf c "(";
	  trm_to_coq c m1 bound (-1) 5000;
	  Printf.fprintf c " ";
	  trm_to_coq c m2 bound 5001 (-1);
	  Printf.fprintf c ")";
	end

(* Prints consecutive lambda-terms as a single fun in Coq. *)
and print_lam_coq c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_coq c a coq_names false; Printf.fprintf c ")";
  match m with
  | Lam(b,m') -> print_lam_coq c b m' bound
  | _ -> Printf.fprintf c " => "; trm_to_coq c m bound (-1) (-1)

(* Prints consecutive forall-terms together with the corresponding lambda-terms as a single forall in Coq. *)
and print_all_coq c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c " ("; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c ":"; print_stp_coq c a coq_names false; Printf.fprintf c ")";
  match m with
  | Ap(Forall(a'),Lam(_,m'))-> print_all_coq c a' m' bound
  | _ -> Printf.fprintf c ", "; trm_to_coq c m bound (-1) (-1)

(* Prints an exist-term together with the corresponding lambda-term as an exists in Coq. *)
and print_ex_coq c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c "exists"; Printf.fprintf c " %s" (Variables.top bound);
  Printf.fprintf c ":"; print_stp_coq c a coq_names false;
  Printf.fprintf c ", ";
  trm_to_coq c m bound (-1) (-1)



(*FIXME next batch of functions are adapted from the TSTP functions*)
let rec trm_to_isar c m bound =
  match m with
      Name(x,_) -> (* Definitions *)
        Printf.fprintf c "%s" (isarize_name x)
    | False -> (* Bottom *)
	Printf.fprintf c "False"
    | Ap(Ap(Imp,m1),False) ->  (* Negation *)
	begin
	  Printf.fprintf c "(~(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c "))";
	end
    | Ap(Ap(Imp,m1),m2) -> (* Implication *)
	begin
	  Printf.fprintf c "(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c " --> ";
	  trm_to_isar c m2 bound;
	  Printf.fprintf c ")";
	end
    | Ap(Imp,m1) -> trm_to_isar c (Lam(Prop,Ap(Ap(Imp,shift m1 0 1),DB(0,Prop)))) bound
    | Imp -> trm_to_isar c (Lam(Prop,Lam(Prop,Ap(Ap(Imp,DB(1,Prop)),DB(0,Prop))))) bound
    | Ap(Forall(a),Lam(_,m1)) -> (* forall with Lam *)
        begin
	  print_all_isar c a m1 bound
        end
    | Forall(a) ->
        begin
	  Printf.fprintf c "All";
        end
    | Ap(Ap(Eq(a),m1),m2) -> (* Equality *)
	begin
	  Printf.fprintf c "(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c " = ";
	  trm_to_isar c m2 bound;
	  Printf.fprintf c ")"
	end
    | Eq(a) ->
        Printf.fprintf c "(=)"
    | Ap(Choice(a),Lam(_,m1)) ->
        let bound = Variables.push bound in
        Printf.fprintf c "(@ "; Printf.fprintf c "%s" (Variables.top bound);
        Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false;
        Printf.fprintf c ". ";
        trm_to_isar c m1 bound; Printf.fprintf c ")"
    | Choice(a) ->
        Printf.fprintf c "Eps";
    | True -> (* Top *)
	      Printf.fprintf c "True"
    | Ap(Ap(And,m1),m2) -> (* conjunction *)
	begin
	  Printf.fprintf c "(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c " & ";
	  trm_to_isar c m2 bound;
	  Printf.fprintf c ")";
	end
    | And ->Printf.fprintf c "(&)"
    | Ap(Ap(Or,m1),m2) -> (* disjunction *)
	begin
	  Printf.fprintf c "(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c " | ";
	  trm_to_isar c m2 bound;
	  Printf.fprintf c ")";
	end
    | Or -> Printf.fprintf c "(|)"
    | Ap(Ap(Iff,m1),m2) -> (* equivalenz *)
	begin
	  Printf.fprintf c "(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c " = ";
	  trm_to_isar c m2 bound;
	  Printf.fprintf c ")";
	end
    | Iff -> Printf.fprintf c "(=)"
    | Neg -> Printf.fprintf c "Not"
    | Ap(Exists(a),Lam(_,m1)) -> (* exist *)
        begin
	  print_ex_isar c a m1 bound
        end
    | Exists(a) ->
        begin
	  Printf.fprintf c "Ex";
        end
    | DB(i,a) -> (* Bound variable *)
	Printf.fprintf c "%s" (Variables.get i bound)
    | Lam(a,m) ->
        begin
	  print_lam_isar c a m bound
        end
    | Ap(m1,m2) ->
	begin
	  Printf.fprintf c "(";
	  trm_to_isar c m1 bound;
	  Printf.fprintf c " ";
	  trm_to_isar c m2 bound;
	  Printf.fprintf c ")";
	end

 (* Prints consecutive lambda-terms as a single fun in Isar. *)
and print_lam_isar c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c "(%% "; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false; Printf.fprintf c ". ";
  match m with
  | Lam(b,m') -> print_lam_isar c b m' bound; Printf.fprintf c ")"
  | _ -> trm_to_isar c m bound; Printf.fprintf c ")"
(* Prints consecutive forall-terms together with the corresponding lambda-terms as a single forall in Isar. *)
and print_all_isar c a m bound =
  let bound = Variables.push bound in
    Printf.fprintf c "(! "; Printf.fprintf c "%s" (Variables.top bound); Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false; Printf.fprintf c ". ";
    match m with
      | Ap(Forall(a'),Lam(_,m')) -> print_all_isar c a' m' bound; Printf.fprintf c ")"
      | _ -> trm_to_isar c m bound; Printf.fprintf c ")"
(* Prints an exist-term together with the corresponding lambda-term as an exists in Isar. *)
and print_ex_isar c a m bound =
  let bound = Variables.push bound in
  Printf.fprintf c "(? "; Printf.fprintf c "%s" (Variables.top bound);
  Printf.fprintf c "::"; print_stp_isar c a (*Hashtbl.create 0(*FIXME*)*) false;
  Printf.fprintf c ". ";
  trm_to_isar c m bound; Printf.fprintf c ")"
