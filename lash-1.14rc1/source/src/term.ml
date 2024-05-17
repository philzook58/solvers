(* Lash *)
(* ported from Satallax file: term.ml
   but with major changes to use the C ftm representation
 *)

open String
open Preterm

let basename_no_h=(Hashtbl.create 1000 : (string, int) Hashtbl.t);;
let no_basename_h=(Hashtbl.create 1000 : (int, string) Hashtbl.t);;
let basename_num = ref 0;;
let basename_no name =
  try Hashtbl.find basename_no_h name
  with Not_found ->
    incr basename_num;
    Hashtbl.add basename_no_h name !basename_num;
    Hashtbl.add no_basename_h !basename_num name;
    !basename_num
and no_basename =
  try Hashtbl.find no_basename_h
  with Not_found -> assert false

let tyname_dollar_i = basename_no "$i";;
let tyname_set = basename_no "set";;
let tyname_star = basename_no "*";;
let tyname_underscore = basename_no "_";;


type stp_internal = Base of int | Prop | Ar of (int * int);;
let ty = Vector.make 1024 Prop;;
let bases = Vector.make 1024 0;;
let ars_hash = Hashtbl.create 1000;;

let ty_num = ref 1;; (* 0 is already prop *)
let mk_prop = 0;;
let mk_base i =
  let ret = Vector.get_default bases i 0 in
  if ret > 0 then ret else begin
    let ret = !ty_num in
    Vector.set ty ret (Base i);
    incr ty_num;
    Vector.set bases i ret; ret
  end;;

let mk_ar l r =
  try Hashtbl.find ars_hash (l, r) with
  | Not_found ->
    let ret = !ty_num in
    Vector.set ty ret (Ar (l, r));
    incr ty_num;
    Hashtbl.add ars_hash (l, r) ret; ret;;

let is_ar a = match Vector.get ty a with Ar(_,_) -> true | _ -> false
let is_base a = match Vector.get ty a with Base _ -> true | _ -> false
let ty_get_l a = match Vector.get ty a with Ar(a1,a2) -> a1 | _ -> assert false
let ty_get_r a = match Vector.get ty a with Ar(a1,a2) -> a2 | _ -> assert false
let ty_get_no a = match Vector.get ty a with Base b -> b | _ -> assert false

type stp = int;;

let ty_pred_over a =
  if is_ar a && ty_get_r a = mk_prop then
    Some(ty_get_l a)
  else
    None

exception ExpectedTypeError of pretrm * stp * stp

type ctx = (string * stp) list

type trm =
    Name of string * stp
  | False | Imp | Forall of stp | Eq of stp | Choice of stp
  | True | Neg | Or | And | Iff | Exists of stp (*** These are normalized away. ***)
  | DB of int * stp
  | Lam of stp * trm
  | Ap of trm * trm

let oo = mk_ar mk_prop mk_prop
let ooo = mk_ar mk_prop oo
let imp x y = Ap(Ap(Imp,x),y)
let preneg x = Ap(Neg,x)
let neg x = imp x False
let normneg m =
  begin
    match m with
    | Ap(Ap(Imp,m1),False) -> m1
    | _ -> neg m
  end
let predisj x y = Ap(Ap(Or,x),y)
let preconj x y = Ap(Ap(And,x),y)
let preiff x y = Ap(Ap(Iff,x),y)
let disj x y = imp (neg x) y
let conj x y = neg (imp x (neg y))
let iff x y = Ap(Ap(Eq(mk_prop),x),y)
let eq a x y = Ap(Ap(Eq(a),x),y)
let forall a m = Ap(Forall(a),Lam(a,m))
let exists a m = neg (forall a (neg m))
let choice a m = Ap(Choice(a),Lam(a,m))

let existsconst a = let ao = mk_ar a mk_prop in Lam(ao,neg (forall a (neg (Ap(DB(1,ao),DB(0,ao))))))

let lpar p = if p then "(" else ""

let rpar p = if p then ")" else ""

let rec stp_str_rec a p =
  if is_base a then
    no_basename (ty_get_no a)
  else if is_ar a then
    let b = ty_get_l a in
    let c = ty_get_r a in
    (lpar p) ^ (stp_str_rec b true) ^ ">" ^ (stp_str_rec c false) ^ (rpar p)
  else
    "$o"

let stp_str a = stp_str_rec a false

let rec stp_contains a b =
  if is_ar b then
    (stp_contains a (ty_get_l b) || stp_contains a (ty_get_r b))
  else
    a = b

let rec church_num_body m =
  match m with
  | DB(0,_) -> true
  | Ap(DB(1,_),m1) -> church_num_body m1
  | _ -> false

let rec church_num_body_val m =
  match m with
  | DB(0,_) -> 0
  | Ap(DB(1,_),m1) -> 1 + (church_num_body_val m1)
  | _ -> raise (GenericSyntaxError("Falsely thought I had the body of a Church numeral. BUG"))

let rec trm_str_rec m p =
  match m with
    Name(x,_) -> x
  | Lam(a12,DB(0,_)) when is_ar a12 && (ty_get_l a12 = ty_get_r a12) -> "#1:" ^ (stp_str (ty_get_l a12)) (*** Church Numeral 1 Printed in a special way. - Chad, Feb 2, 2011 ***)
  | Lam(a12,Lam(a3,m)) when is_ar a12 && ty_get_l a12 = ty_get_r a12 && ty_get_l a12 = a3 && church_num_body m -> "#" ^ string_of_int (church_num_body_val m) ^ ":" ^ stp_str (ty_get_l a12) (*** Church Numerals Printed in a special way. - Chad, Feb 2, 2011 ***)
  | False -> "False"
  | Imp -> "imp"
  | Forall(a) -> "Pi:" ^ (stp_str a)
  | Eq(a) -> "eq:" ^ (stp_str a)
  | Choice(a) -> "Sepsilon:" ^ (stp_str a)
  | DB(i,_) -> "^" ^ (string_of_int i)
  | Lam(a,m) -> (lpar p) ^ "\\_:" ^ (stp_str a) ^ "." ^ (trm_str_rec m false) ^ (rpar p)
  | Ap(m1,m2) ->
      begin
	match m1 with
	| Lam _ -> (lpar p) ^ (trm_str_rec m1 true) ^ " " ^ (trm_str_rec m2 true) ^ (rpar p)
	| _ -> (lpar p) ^ (trm_str_rec m1 false) ^ " " ^ (trm_str_rec m2 true) ^ (rpar p)
      end
(*** If logic has not been normalized away ***)
  | True -> "True"
  | Neg -> "not"
  | Or -> "or"
  | And -> "and"
  | Iff -> "iff"
  | Exists(_) -> "Sigma"

let trm_str m = trm_str_rec m false

(*** This function assumes m is well-typed. ***)
let rec tpof m =
  match m with
    Name(_,a) -> a
  | False -> mk_prop
  | Imp -> ooo
  | Forall(a) -> mk_ar (mk_ar a mk_prop) mk_prop
  | Eq(a) -> mk_ar a (mk_ar a mk_prop)
  | Choice(a) -> mk_ar (mk_ar a mk_prop) a
  | DB(_,a) -> a
  | Lam(a,n) -> mk_ar a (tpof n)
  | Ap(f,n) ->
     begin
       let ab = tpof f in
       if is_ar ab then
         ty_get_r ab
       else
         raise (GenericSyntaxError("Non-function applied: " ^ (trm_str m)))
      end
  | _ -> raise (GenericSyntaxError("Unexpected type case - were logical constants normalized away? " ^ (trm_str m)))

let ueq x y = Ap(Ap(Eq(tpof(x)),x),y)

(*** Call this to check application is well typed ***)
let ap (m,n) =
  let ab = tpof m in
  let c = tpof n in
  if is_ar ab && ty_get_l ab = c then
    Ap(m,n)
  else
    raise (GenericSyntaxError("Ill typed application (" ^ (trm_str m) ^ " : " ^ (stp_str ab) ^ ") @ (" ^ (trm_str n) ^ " : " ^ (stp_str c) ^ ")"))

(** Prints type m as a Coq-formatted string on the out_channel c  **)
let rec print_stp_coq c m h p =
  if is_base m then
    let x = ty_get_no m in
    let x = try (Hashtbl.find h (no_basename x)) with Not_found -> failwith("print_stp_coq can't find coqname of "^ (no_basename x)) in
    Printf.fprintf c "%s" x
  else if m = mk_prop then
    Printf.fprintf c "o"
  else if is_ar m then
    begin
      let a = ty_get_l m in
      let b = ty_get_r m in
      if p then Printf.fprintf c "(";
      print_stp_coq c a h true;
      Printf.fprintf c " --> ";
      print_stp_coq c b h false;
      if p then Printf.fprintf c ")"
    end

(*
let rec print_stp_isar c m h p =
  match m with
    | Base x ->
	      let x = try (Hashtbl.find h x) with Not_found -> failwith("print_stp_isar can't find coqname of "^x) in
          Printf.fprintf c "%s" x
    | Prop ->
        Printf.fprintf c "o"
    | Ar(a,b) ->
        begin
	        if p then Printf.fprintf c "(";
	        print_stp_isar c a h true;
	        Printf.fprintf c " => ";
	        print_stp_isar c b h false;
	        if p then Printf.fprintf c ")"
        end
*)
let rec print_stp_isar c m p =
  if is_base m then
    let x = ty_get_no m in
    if x <> tyname_dollar_i then
      Printf.fprintf c "%s" (no_basename x)
    else
      Printf.fprintf c "i"(*FIXME this may clash with a base type that's really called "i"*)
  else if m = mk_prop then
    Printf.fprintf c "o"
  else if is_ar m then
    begin
      (*	        if p then*) Printf.fprintf c "(";
      let a = ty_get_l m in
      let b = ty_get_r m in
      print_stp_isar c a true;
      Printf.fprintf c "=>";
      print_stp_isar c b false;
      (*	        if p then*) Printf.fprintf c ")";
      flush c
    end

let rec print_stp_coq2 c m p =
  if is_base m then
    Printf.fprintf c "set"
  else if m = mk_prop then
    Printf.fprintf c "prop"
  else if is_ar m then
    begin
      let a = ty_get_l m in
      let b = ty_get_r m in
      if p then Printf.fprintf c "(";
      print_stp_coq2 c a true;
      Printf.fprintf c " > ";
      print_stp_coq2 c b false;
      if p then Printf.fprintf c ")"
    end


(*** Shifting, Substitution, Normalization ***)

let rec shift m i j =
  match m with
    DB(k,_) when k < i -> m
  | DB(k,a) -> DB(k + j,a)
  | Lam(a1,m2) -> Lam(a1,shift m2 (i + 1) j)
  | Ap(m1,m2) -> Ap(shift m1 i j,shift m2 i j)
  | _ -> m

let rec subst m i n =
  match m with
    DB(k,_) when k < i -> m
  | DB(k,_) when k = i -> n
  | DB(k,a) -> DB(k - 1,a)
  | Lam(a1,m2) -> Lam(a1,subst m2 (i + 1) (shift n 0 1))
  | Ap(m1,m2) -> Ap(subst m1 i n,subst m2 i n)
  | _ -> m

(*** Simultaneous Substitution ***)
(*** Assumes no dangling deBruijn indices. ***)
let rec simulsubst m s =
  match m with
    DB(k,_) ->
      let n = List.nth s k in
      if (m = n) then m else n
  | Lam(a1,m1) ->
      let n1 = simulsubst m1 ((DB(0,a1))::(List.map (fun n -> shift n 0 1) s)) in
      if (m1 = n1) then m else Lam(a1,n1)
  | Ap(m1,m2) ->
      let n1 = simulsubst m1 s in
      let n2 = simulsubst m2 s in
      if ((m1 = n1) && (m2 = n2)) then m else Ap(n1,n2)
  | _ -> m

let rec namesubst m x n =
  match m with
    Name(y,a) when (x = y) -> n
  | Lam(a1,m1) -> Lam(a1,namesubst m1 x n)
  | Ap(m1,m2) -> Ap(namesubst m1 x n,namesubst m2 x n)
  | _ -> m

let gen_lam_body a m =
  match m with
  | Lam(_,m1) -> m1
  | _ -> Ap(shift m 0 1,DB(0,a))

let rec termNotFreeIn m i =
  match m with
    DB(j,_) when i = j -> false
  | Ap(m1,m2) -> (termNotFreeIn m1 i) && (termNotFreeIn m2 i)
  | Lam(a,m1) -> termNotFreeIn m1 (i + 1)
  | _ -> true

let rec termNotFreeInL m il =
  match m with
    DB(j,_) when (List.mem j il) -> false
  | Ap(m1,m2) -> (termNotFreeInL m1 il) && (termNotFreeInL m2 il)
  | Lam(a,m1) -> termNotFreeInL m1 (List.map (fun i -> i + 1) il)
  | _ -> true

let rec termNoDBs_rec m i =
  match m with
    DB(j,_) -> if (j < i) then true else false
  | Ap(m1,m2) -> (termNoDBs_rec m1 i) && (termNoDBs_rec m2 i)
  | Lam(a,m1) -> termNoDBs_rec m1 (i + 1)
  | _ -> true

let termNoDBs m = termNoDBs_rec m 0

let rec norm1 d m =
  match m with
    Ap(Lam(a,m1),m2) -> (* beta *)
      let (n1,_) = norm1 d m1 in
      let (n2,_) = norm1 d m2 in
      (subst n1 0 n2,true)
  | Lam(_,Ap(m1,DB(0,_))) when (termNotFreeIn m1 0) -> (* eta *)
      (shift m1 0 (- 1),true)
	(*** dneg ***)
  | Ap(Ap(Imp,Ap(Ap(Imp,m1),False)),False) -> (* double negation reduce *)
      let (n1,_) = norm1 d m1 in
      (n1,true)
  | Name(x,_) ->
      begin
	try
	  (Hashtbl.find d x,true)
	with
	| Not_found -> (m,false)
      end
  | Ap(m1,m2) ->
      let (n1,b1) = norm1 d m1 in
      let (n2,b2) = norm1 d m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = norm1 d m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)

(* beta-eta-delta-dneg *)    
let rec norm d m =
  let (m1,reduced) = norm1 d m in
  if reduced then (norm d m1) else m

let rec betanorm1 d m =
  match m with
    Ap(Lam(a,m1),m2) -> (* beta *)
      let (n1,_) = betanorm1 d m1 in
      let (n2,_) = betanorm1 d m2 in
      (subst n1 0 n2,true)
  | Name(x,_) ->
      begin
	try
	  (Hashtbl.find d x,true)
	with
	| Not_found -> (m,false)
      end
  | Ap(m1,m2) ->
      let (n1,b1) = betanorm1 d m1 in
      let (n2,b2) = betanorm1 d m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = betanorm1 d m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)
    
(* beta-delta *)    
let rec betanorm d m =
  let (m1,reduced) = betanorm1 d m in
  if reduced then (betanorm d m1) else m

let rec onlybetanorm1 m =
  match m with
    Ap(Lam(a,m1),m2) -> (* onlybeta *)
      let (n1,_) = onlybetanorm1 m1 in
      let (n2,_) = onlybetanorm1 m2 in
      (subst n1 0 n2,true)
  | Ap(m1,m2) ->
      let (n1,b1) = onlybetanorm1 m1 in
      let (n2,b2) = onlybetanorm1 m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = onlybetanorm1 m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)
    
(* beta (no delta) *)
let rec onlybetanorm m =
  let (m1,reduced) = onlybetanorm1 m in
  if reduced then (onlybetanorm m1) else m

(** Replaces all occurences of 'Neg' by 'implies False' **)
let rec negnorm1 m =
  match m with
  | Ap(Neg,m1) ->
      let (n1,_) = negnorm1 m1 in
      (imp n1 False,true)
  | Neg -> (Lam(mk_prop,imp (DB(0,mk_prop)) False),true)
  | Ap(m1,m2) ->
      let (n1,b1) = negnorm1 m1 in
      let (n2,b2) = negnorm1 m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = negnorm1 m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)

(** applies neg- and betanormalization**)
let onlynegnorm m =
  let (n,_) = negnorm1 m in onlybetanorm n

let rec logicnorm1 m =
  match m with
  | True -> (imp False False,true)
  | Ap(Neg,m1) ->
      let (n1,_) = logicnorm1 m1 in
      (imp n1 False,true)
  | Neg -> (Lam(mk_prop,imp (DB(0,mk_prop)) False),true)
  | Ap(Ap(Or,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (disj n1 n2,true)
  | Or -> (Lam(mk_prop,Lam(mk_prop,disj (DB(1,mk_prop)) (DB(0,mk_prop)))),true)
  | Ap(Ap(And,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (conj n1 n2,true)
  | And -> (Lam(mk_prop,Lam(mk_prop,conj (DB(1,mk_prop)) (DB(0,mk_prop)))),true)
  | Ap(Ap(Iff,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (iff n1 n2,true)
  | Iff -> (Lam(mk_prop,Lam(mk_prop,iff (DB(1,mk_prop)) (DB(0,mk_prop)))),true)
  | Ap(Exists(a),Lam(_,m1)) ->
      let (n1,_) = logicnorm1 m1 in
      (exists a n1,true)
  | Exists(a) ->
      let ao = mk_ar a mk_prop in
      (Lam(ao,exists a (Ap(DB(1,ao),DB(0,a)))),true)
  | Ap(m1,m2) ->
      let (n1,b1) = logicnorm1 m1 in
      let (n2,b2) = logicnorm1 m2 in
      if (b1 || b2) then
	(Ap(n1,n2),true)
      else
	(m,false)
  | Lam(a1,m1) ->
      let (n1,b1) = logicnorm1 m1 in
      if b1 then
	(Lam(a1,n1),true)
      else
	(m,false)
  | _ -> (m,false)

(* Reduce logical constants to ->, False, forall, =, choice *)
let rec logicnorm m =
  let (n,_) = logicnorm1 m in n

let ideclared = ref false
let basetypestobool = ref false

(*** conversion of pretrm ***)
let rec to_stp (m:pretrm) =
  match m with
    PPropTp -> mk_prop
  | PIndTp when !basetypestobool -> mk_prop
  | PName _ when !basetypestobool -> mk_prop
  | PIndTp ->
      if (!ideclared) then mk_base tyname_dollar_i
      else
       begin
        ideclared := true;
        raise DeclareInd
       end
  | PName x ->
     begin
       mk_base (basename_no x)
     end
  | PAr(a,b) -> mk_ar (to_stp a) (to_stp b)
  | PType -> raise Polymorphism
  | _ -> raise (GenericSyntaxError ((pretrm_str m) ^ " is not a simple type"))

let expected_tp m a b =
  match a with
    Some(aa) ->
      if (aa = b) then () else raise (ExpectedTypeError(m,aa,b))
  | _ -> ()

let rec to_trm (h:(string,(trm * stp) * bool ref) Hashtbl.t) (g:ctx) (m:pretrm) (a:stp option) =
  match m with
  | PAp(PName "Eps",a) -> let b = to_stp a in (Choice b,mk_ar (mk_ar b mk_prop) b)
  | PName "In" -> let a = mk_base tyname_set in (Name("In",mk_ar a (mk_ar a mk_prop)),mk_ar a (mk_ar a mk_prop))
  | PName "Subq" -> let a = mk_base tyname_set in (Lam(a,Lam(a,Ap(Forall(a),Lam(a,Ap(Ap(Imp,Ap(Ap(Name("In",mk_ar a (mk_ar a mk_prop)),DB(0,a)),DB(2,a))),Ap(Ap(Name("In",mk_ar a (mk_ar a mk_prop)),DB(0,a)),DB(1,a))))))),mk_ar a (mk_ar a mk_prop))
  | PName x ->
      begin(*** look in g, then in h, then fail ***)
	try
	  to_db m x g a 0
	with
	| Not_found ->
	    try
	      let (zz,o) = Hashtbl.find h x in
	      begin
		(match zz with (_,b) -> expected_tp m a b);
		o := true; (** Mark that it's occurred. - Chad, March 31, 2011 **)
		zz
	      end
	    with
	    | Not_found -> raise (GenericSyntaxError ("Unknown Name " ^ x))
      end
  | PTrue ->
      expected_tp m a mk_prop;
      (True,mk_prop)
  | PFalse ->
      expected_tp m a mk_prop;
      (False,mk_prop)
  | PNeg -> (Neg,oo)
  | POr ->
      expected_tp m a ooo;
      (Or,ooo)
  | PAnd ->
      expected_tp m a ooo;
      (And,ooo)
  | PIff ->
      expected_tp m a ooo;
      (Iff,ooo)
  | PAp(PAp(PExists,m0),m1) ->
      begin
	expected_tp m a mk_prop;
	let n0 = to_stp m0 in
	let (n1,a1) = to_trm h g m1 (Some(mk_ar n0 mk_prop)) in
	match ty_pred_over a1 with
	  Some(a1a) -> (Ap(Exists(a1a),n1),mk_prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,mk_ar (mk_base tyname_star) mk_prop))
      end
  | PAp(PAp(PForall,m0),m1) ->
      begin
	expected_tp m a mk_prop;
	let n0 = to_stp m0 in
	let (n1,a1) = to_trm h g m1 (Some(mk_ar n0 mk_prop)) in
	match ty_pred_over a1 with
	  Some(a1a) -> (Ap(Forall(a1a),n1),mk_prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,mk_ar (mk_base tyname_star) mk_prop))
      end
  | PAp(PExists,m1) ->
      begin
	expected_tp m a mk_prop;
	let (n1,a1) = to_trm h g m1 None in
	match ty_pred_over a1 with
	  Some(a1a) -> (Ap(Exists(a1a),n1),mk_prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,mk_ar (mk_base tyname_star) mk_prop))
      end
  | PAp(PForall,m1) ->
      begin
	expected_tp m a mk_prop;
	let (n1,a1) = to_trm h g m1 None in
	match ty_pred_over a1 with
	  Some(a1a) -> (Ap(Forall(a1a),n1),mk_prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,mk_ar (mk_base tyname_star) mk_prop))
      end
  | PAp(PAp(PNIff,m1),m2) ->
      expected_tp m a mk_prop;
      (preneg (preiff (to_trm_1 h g m1 (Some mk_prop)) (to_trm_1 h g m2 (Some mk_prop))),mk_prop)
  | PNIff ->
      expected_tp m a ooo;
      (Lam(mk_prop,Lam(mk_prop,preneg (preiff (DB(1,mk_prop)) (DB(0,mk_prop))))),ooo)
  | PImplies ->
      expected_tp m a ooo;
      (Lam(mk_prop,Lam(mk_prop,imp (DB(1,mk_prop)) (DB(0,mk_prop)))),ooo)
  | PRevImplies ->
      expected_tp m a ooo;
      (Lam(mk_prop,Lam(mk_prop,imp (DB(0,mk_prop)) (DB(1,mk_prop)))),ooo)
  | PNOr ->
      expected_tp m a ooo;
      (Lam(mk_prop,Lam(mk_prop,preneg (predisj (DB(1,mk_prop)) (DB(0,mk_prop))))),ooo)
  | PNAnd ->
      expected_tp m a ooo;
      (Lam(mk_prop,Lam(mk_prop,preneg (preconj (DB(1,mk_prop)) (DB(0,mk_prop))))),ooo)
  | PAp(PAp(PEq,m1),m2) ->
      expected_tp m a mk_prop;
      let (n1,b1) = to_trm h g m1 None in
      let n2 = to_trm_1 h g m2 (Some b1) in
      ((eq b1 n1 n2),mk_prop)
  | PEq ->
      begin
	match a with
	| Some(aa) ->
           if is_ar aa then
             begin
               let aaa = ty_get_r aa in
               match ty_pred_over aaa with
               | Some(b2) ->
                  if b2 = ty_get_l aa then
                    (Lam(b2,Lam(b2,eq b2 (DB(1,mk_prop)) (DB(0,mk_prop)))),aa)
                  else
	            raise (ExpectedTypeError(m,aa,mk_ar (mk_base tyname_star) (mk_ar (mk_base tyname_star) mk_prop)))
               | None ->
	          raise (ExpectedTypeError(m,aa,mk_ar (mk_base tyname_star) (mk_ar (mk_base tyname_star) mk_prop)))
             end
           else
	     raise (ExpectedTypeError(m,aa,mk_ar (mk_base tyname_star) (mk_ar (mk_base tyname_star) mk_prop)))
	| None ->
	    raise (GenericSyntaxError ("Cannot determine type of unapplied equality"));
      end
  | PAp(PAp(PNEq,m1),m2) ->
      expected_tp m a mk_prop;
      let (n1,b1) = to_trm h g m1 None in
      let n2 = to_trm_1 h g m2 (Some b1) in
      (preneg (eq b1 n1 n2),mk_prop)
  | PNEq ->
     begin
       match a with
	| Some(aa) ->
           if is_ar aa then
             begin
               let aaa = ty_get_r aa in
               match ty_pred_over aaa with
               | Some(b2) ->
                  if b2 = ty_get_l aa then
	            (Lam(b2,Lam(b2,preneg (eq b2 (DB(1,mk_prop)) (DB(0,mk_prop))))),aa)
                  else
	            raise (ExpectedTypeError(m,aa,mk_ar (mk_base tyname_star) (mk_ar (mk_base tyname_star) mk_prop)))
               | None ->
	          raise (ExpectedTypeError(m,aa,mk_ar (mk_base tyname_star) (mk_ar (mk_base tyname_star) mk_prop)))
             end
           else
	     raise (ExpectedTypeError(m,aa,mk_ar (mk_base tyname_star) (mk_ar (mk_base tyname_star) mk_prop)))
	| None ->
	   raise (GenericSyntaxError ("Cannot determine type of unapplied negated equality"));
      end
  | PAp(m1,m2) ->
      begin
	let (n1,a1) = to_trm h g m1 None in
        if is_ar a1 then
          let a1a = ty_get_l a1 in
          let a1b = ty_get_r a1 in
	  expected_tp m a a1b;
	  let n2 = to_trm_1 h g m2 (Some a1a) in
	  (Ap(n1,n2),a1b)
        else
          raise (GenericSyntaxError("Non-function applied: " ^ (trm_str n1)))
      end
  | PULam(xl,m1) ->
      begin
	match a with
	| Some(aa) -> to_ulam h g xl m1 aa
	| None -> raise (GenericSyntaxError("Cannot infer type omitted from lambda"))
      end
  | PLam(xl,m1) ->
      to_lam h g xl m1 a
  | PAll(xl,m1) ->
      expected_tp m a mk_prop;
      (to_all h g xl m1,mk_prop)
  | PEx(xl,m1) ->
      expected_tp m a mk_prop;
      (to_exists h g xl m1,mk_prop)
  | PExU(x,a1,m1) ->
      expected_tp m a mk_prop;
      begin
	let atp = to_stp a1 in
	match to_trm h ((x,atp)::g) m1 (Some mk_prop) with
	| (m1a,_) -> (Ap(Lam(mk_ar atp mk_prop,Ap(Exists(atp),Lam(atp,Ap(Ap(And,Ap(DB(1,mk_ar atp mk_prop),DB(0,atp))),Ap(Forall(atp),Lam(atp,Ap(Ap(Imp,Ap(DB(2,mk_ar atp mk_prop),DB(0,atp))),Ap(Ap(Eq(atp),DB(0,atp)),DB(1,atp))))))))),Lam(atp,m1a)),mk_prop)
      end
  | PChoice((x,xa),m1) ->
      let xaa = to_stp xa in
      let n1 = to_trm_1 h ((x,xaa)::g) m1 (Some mk_prop) in
      (choice xaa n1,xaa)
  | POf(m1,m2) ->
      let b = to_stp m2 in
      expected_tp m1 a b;
      to_trm h g m1 (Some b)
  | PDef(m1,_) ->
      to_trm h g m1 a
  | PLet(x,m1,m2) ->
      begin
	let (m1a,aa) = to_trm h g m1 None in
	let (m2b,bb) = to_trm h ((x,aa)::g) m2 a in
	(Ap(Lam(aa,m2b),m1a),bb)
      end
  | PTLet(x,a1,m1,m2) ->
      begin
	let (m1a,aa) = to_trm h g m1 (Some (to_stp a1)) in
	let (m2b,bb) = to_trm h ((x,aa)::g) m2 a in
	(Ap(Lam(aa,m2b),m1a),bb)
      end
  | _ -> raise (GenericSyntaxError ("Ill-formed term " ^ (pretrm_str m)))
and to_trm_1 h g m a = let (n,_) = to_trm h g m a in n
and to_ulam h (g:ctx) xl m a =
  match xl with
    (x::xr) ->
     begin
       if is_ar a then
          let a1 = ty_get_l a in
          let a2 = ty_get_r a in
	  let (n1,_) = to_ulam h ((x,a1)::g) xr m a2 in
	  (Lam(a1,n1),a)
       else
	 raise (ExpectedTypeError(m,a,mk_ar (mk_base tyname_underscore) (mk_base tyname_star)))
      end
  | [] -> to_trm h g m (Some a)
and to_lam h (g:ctx) xl m a =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	match a with
	| Some(aa) ->
           if is_ar aa && ty_get_l aa = xaa then
             let a2 = ty_get_r aa in
             let (n1,_) = to_lam h ((x,xaa)::g) xr m (Some a2) in
	     (Lam(xaa,n1),aa)
           else
	     raise (ExpectedTypeError(m,aa,mk_ar xaa (mk_base tyname_star)))
	| None ->
	    let (n1,b) = to_lam h ((x,xaa)::g) xr m None in
	    (Lam(xaa,n1),mk_ar xaa b)
      end
  | [] -> to_trm h g m a
and to_all h (g:ctx) xl m =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	let n1 = to_all h ((x,xaa)::g) xr m in
	forall xaa n1
      end
  | [] -> to_trm_1 h g m (Some mk_prop)
and to_exists h (g:ctx) xl m =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	let n1 = to_exists h ((x,xaa)::g) xr m in
	Ap(Exists(xaa),Lam(xaa,n1))
      end
  | [] ->
      to_trm_1 h g m (Some mk_prop)
and to_db m x g a i =
  match g with
    ((y,b)::gr) -> 
      if (x = y) then
	begin
	  expected_tp m a b;
	  (DB(i,b),b)
	end
      else
	to_db m x gr a (i + 1)
  | [] -> raise Not_found

let neg_body m =
  match m with
    Ap(Ap(Imp,n),False) -> Some n
  | _ -> None

let eq_body m =
  match m with
      Ap (Ap (Eq a, x), y) -> Some (a, x, y)
    | _ -> None

let neg_p m =
  match (neg_body m) with Some _ -> true | None -> false

(*This is like "head_spine" below, but accepts
  a bound to the number of "Ap"s it is to go
  through before stopping.*)
let bounded_head_spine n m =
  let rec head_spine_aux n m args =
    if n = 0 then (m, args)
    else
      match m with
          Ap (f, a) -> head_spine_aux (n - 1) f (a :: args)
        | _ -> (m, args)
  in
    head_spine_aux n m []

(*Unbounded form of "bounded_head_spine": it
  fully unfolds a term into the head (a non-applicative term)
  and the spine of terms it is applied to.*)
let head_spine m = bounded_head_spine (-1) m

let rec rtp a = if is_ar a then rtp (ty_get_r a) else a

let rec argtps_rtp_rec a =
  if is_ar a then
    let a1 = ty_get_l a in
    let a2 = ty_get_r a in
    let (al,r) = argtps_rtp_rec a2 in
    (a1::al,r)
  else
    ([],a)

let argtps_rtp a = argtps_rtp_rec a


(*List the constants that occur in a term, as name-type pairs.
  NOTE the resulting list doesn't contain duplicate constants.*)
let rec consts_of_trm acc : trm -> ctx = function
    Name (name, stp) ->
    begin
    try
      let stp' = List.assoc name acc
      in
        if stp' <> stp then failwith "Different types for same constant?"
        else acc
    with Not_found ->
      (name, stp) :: acc
    end
  | Lam (_, trm) -> consts_of_trm acc trm
  | Ap (trm1, trm2) ->
    let acc' = consts_of_trm acc trm1
    in consts_of_trm acc' trm2
  | False | Imp | Forall _ | Eq _ | Choice _
  | True | Neg | Or | And | Iff | Exists _
  | DB (_, _) -> acc

(*Produce a list of names (strings) of the base types that occur in a type.
  NOTE the resulting list doesn't contain duplicate names.*)
let rec base_types acc a : int list =
  if is_base a then
    let name = ty_get_no a in
    if List.mem name acc then acc
    else name :: acc
  else if is_ar a then
   let acc' = base_types acc (ty_get_l a)
   in base_types acc' (ty_get_r a)
  else
    acc

(*Lists the base types referenced in a term.
  NOTE the resulting list doesn't contain duplicate elements.*)
let rec base_types_of_trm acc : trm -> int list = function
    Name (name, stp) -> base_types acc stp
  | Lam (stp, trm) ->
    let acc' = base_types acc stp
    in base_types_of_trm acc' trm
  | Ap (trm1, trm2) ->
    let acc' = base_types_of_trm acc trm1
    in base_types_of_trm acc' trm2
  | Forall stp | Eq stp | Choice stp | Exists stp | DB (_, stp) ->
    base_types acc stp
  | False | Imp | True | Neg | Or | And | Iff -> acc

let fresh_prefix = "__"

let make_fresh_name i = fresh_prefix ^ string_of_int i
let is_fresh_name = StringE.starts_with fresh_prefix

let rec map_names f = function
  Name (x,a) -> f x a
| Lam (t,m) -> Lam(t, map_names f m)
| Ap (m,n) -> Ap(map_names f m, map_names f n)
| m -> m

let rec fold_names f acc = function
  Name (x,a) -> f acc x a
| Lam (t,m) -> let (acc', m') = fold_names f acc m in (acc', Lam(t, m'))
| Ap (m,n) ->
    let (acc' , m') = fold_names f acc  m in
    let (acc'', n') = fold_names f acc' n in
    (acc'', Ap(m', n'))
| m -> (acc, m)

let normalize_fresh_uni =
  map_names (fun x a -> Name((if is_fresh_name x then fresh_prefix else x), a))

let normalize_asc_fun p name ((m,i) as acc) x a =
  if p x
  then
  begin
    let (acc', x') =
      try (acc, List.assoc x m)
      with Not_found -> let i' = i+1 in (((x,i')::m,i'), i')
    in (acc', Name(name x', a))
  end
  else (acc, Name (x,a))

let normalize_fresh_asc m =
  fold_names (normalize_asc_fun is_fresh_name make_fresh_name) ([], 0) m

let normalize_asc m =
  fold_names (normalize_asc_fun (fun x -> true) (fun i -> "c" ^ string_of_int i)) ([], 0) m

let contains_fresh_names m = let ((_, i), _) = normalize_fresh_asc m in i > 0

(***
 gives a version with named vars and ~, ->, ! intended to be more readable for the humans.
 partially based on the printer code for Egal
 ***)
let next_var_name a names othernames =
  let basevarnames = ["x";"y";"z";"w";"u";"v"] in
  let predvarnames = ["p";"q";"r"] in
  let funcvarnames = ["f";"g";"h"] in
  let varnames =
    if rtp a = mk_prop then
      predvarnames
    else if is_ar a then
      funcvarnames
    else
      basevarnames
  in
  let numvarnames = List.length varnames in
  let var_name_of j =
    if j < numvarnames then
      List.nth varnames j
    else
      let k = j / numvarnames in
      let m = j mod numvarnames in
      (List.nth varnames m) ^ string_of_int k
  in
  let i = ref 0 in
  let x = ref (var_name_of 0) in
  try
    while true do
      if List.mem !x names || List.mem !x othernames then (incr i; x := var_name_of !i) else raise Exit
    done;
    ""
  with Exit -> !x

let trm_str_nice_paren q (s,p) = if p <= q then s else "(" ^ s ^ ")"

let rec binderp m =
  match m with
  | Lam(_,_) -> true
  | Ap(Forall(_),Lam(_,_)) -> true
  | _ -> false

let rec trm_str_nice_rec m names othernames =
  match m with
    Name(x,_) -> (x,0)
  | Lam(a12,DB(0,_)) when is_ar a12 && (ty_get_l a12 = ty_get_r a12) -> ("#1:" ^ (stp_str (ty_get_l a12)),0) (*** Church Numeral 1 Printed in a special way. - Chad, Feb 2, 2011 ***)
  | Lam(a12,Lam(a3,m)) when is_ar a12 && ty_get_l a12 = ty_get_r a12 && ty_get_l a12 = a3 && church_num_body m -> ("#" ^ string_of_int (church_num_body_val m) ^ ":" ^ stp_str (ty_get_l a12),0) (*** Church Numerals Printed in a special way. - Chad, Feb 2, 2011 ***)
  | False -> ("False",0)
  | Imp -> ("imp",0)
  | Forall(a) -> ("Pi:" ^ (stp_str a),0)
  | Eq(a) -> ("eq:" ^ (stp_str a),0)
  | Choice(a) -> ("Sepsilon:" ^ (stp_str a),0)
  | DB(i,_) ->
      begin
	try
	  let x = List.nth names i in
	  (x,0)
	with Failure(_) ->
	  ("^" ^ (string_of_int (i - List.length names)),0)
      end
  | Lam(a,m1) ->
      let x = next_var_name a names othernames in
      ("\\" ^ x ^ ":" ^ (stp_str a) ^ "." ^ (trm_str_nice_paren 1010 (trm_str_nice_rec m1 (x::names) othernames)),1)
  | Ap(Ap(Eq(_),m1),m2) ->
      if binderp m1 then (*** to properly use 'binderish' I would need a separate 'layout' type; I'll use binderp instead and hope it's OK ***)
	((trm_str_nice_paren (-1) (trm_str_nice_rec m1 names othernames)) ^ " = " ^ (trm_str_nice_paren 502 (trm_str_nice_rec m2 names othernames)),502)
      else
	((trm_str_nice_paren 502 (trm_str_nice_rec m1 names othernames)) ^ " = " ^ (trm_str_nice_paren 502 (trm_str_nice_rec m2 names othernames)),502)
  | Ap(Ap(Imp,Ap(Ap(Eq(_),m1),m2)),False) ->
      if binderp m1 then (*** to properly use 'binderish' I would need a separate 'layout' type; I'll use binderp instead and hope it's OK ***)
	((trm_str_nice_paren (-1) (trm_str_nice_rec m1 names othernames)) ^ " <> " ^ (trm_str_nice_paren 502 (trm_str_nice_rec m2 names othernames)),502)
      else
	((trm_str_nice_paren 502 (trm_str_nice_rec m1 names othernames)) ^ " <> " ^ (trm_str_nice_paren 502 (trm_str_nice_rec m2 names othernames)),502)
  | Ap(Ap(Imp,m1),False) ->
      ("~" ^ (trm_str_nice_paren 701 (trm_str_nice_rec m1 names othernames)),701)
  | Ap(Ap(Imp,m1),m2) ->
      if binderp m1 then (*** to properly use 'binderish' I would need a separate 'layout' type; I'll use binderp instead and hope it's OK ***)
	((trm_str_nice_paren (-1) (trm_str_nice_rec m1 names othernames)) ^ " -> " ^ (trm_str_nice_paren 801 (trm_str_nice_rec m2 names othernames)),800)
      else
	((trm_str_nice_paren 800 (trm_str_nice_rec m1 names othernames)) ^ " -> " ^ (trm_str_nice_paren 801 (trm_str_nice_rec m2 names othernames)),800)
  | Ap(Forall(a),Lam(_,m1)) ->
      let x = next_var_name a names othernames in
      ("!" ^ x ^ ":" ^ (stp_str a) ^ "." ^ (trm_str_nice_paren 1010 (trm_str_nice_rec m1 (x::names) othernames)),1)
  | Ap(m1,m2) ->
      if binderp m1 then (*** to properly use 'binderish' I would need a separate 'layout' type; I'll use binderp instead and hope it's OK ***)
	((trm_str_nice_paren (-1) (trm_str_nice_rec m1 names othernames)) ^ " " ^ (trm_str_nice_paren 0 (trm_str_nice_rec m2 names othernames)),1)
      else
	((trm_str_nice_paren 1 (trm_str_nice_rec m1 names othernames)) ^ " " ^ (trm_str_nice_paren 0 (trm_str_nice_rec m2 names othernames)),1)
(*** If logic has not been normalized away ***)
  | True -> ("True",0)
  | Neg -> ("not",0)
  | Or -> ("or",0)
  | And -> ("and",0)
  | Iff -> ("iff",0)
  | Exists(_) -> ("Sigma",0)

let trm_str_nice m =
  let nl = List.map (fun (x,_) -> x) (consts_of_trm [] m) in
  let (s,_) = trm_str_nice_rec m [] nl in
  s

(** Jan/Feb 2022 using Cezary Kaliszyk's ftm representation **)
(** ftm functions **)
open Ftm

let ty_f ty = ty and ty_f_rev ty = ty;;
(*
let ty_no_h=(Hashtbl.create 1000 : (stp, int) Hashtbl.t);;
let no_ty_h=(Hashtbl.create 1000 : (int, stp) Hashtbl.t);;
let ty_num=ref 0;;

let ty_f ty =
  try Hashtbl.find ty_no_h ty
  with Not_found ->
    incr ty_num;
    Hashtbl.add ty_no_h ty !ty_num;
    Hashtbl.add no_ty_h !ty_num ty;
    !ty_num
and ty_f_rev = Hashtbl.find no_ty_h;;
*)

let name_no_h=(Hashtbl.create 1000 : (string, int) Hashtbl.t);;
let no_name_h=(Hashtbl.create 1000 : (int, string) Hashtbl.t);;
let name_num=ref 0;;

let name_no name =
  try Hashtbl.find name_no_h name
  with Not_found ->
    incr name_num;
    Hashtbl.add name_no_h name !name_num;
    Hashtbl.add no_name_h !name_num name;
    !name_num
and name_no_rev = Hashtbl.find no_name_h;;

let mk_neg t = mk_norm_imp t mk_false
let fneg t = mk_neg t

let rec trm_ftm d m =
  match m with
  | Name(x,_) -> (* drop the type for the ftrm rep *)
     begin
       let xn = name_no x in
       try
         Hashtbl.find d xn
       with Not_found -> mk_name xn
     end
  | DB(i,_) -> mk_db i (* drop the type for the ftrm rep *)
  | Lam(a,m1) -> mk_norm_lam (ty_f a) (trm_ftm d m1)
  | False -> mk_false
  | Ap(Ap(Imp,m1),m2) -> mk_norm_imp (trm_ftm d m1) (trm_ftm d m2)
  | Ap(Forall(a),m1) -> mk_all (ty_f a) (trm_ftm d (gen_lam_body a m1))
  | Choice(a) -> mk_choice (ty_f a)
  | Ap(Ap(Eq(a),m1),m2) -> mk_norm_eq (ty_f a) (trm_ftm d m1) (trm_ftm d m2)
  | Ap(Ap(Iff,m1),m2) -> mk_norm_eq (ty_f mk_prop) (trm_ftm d m1) (trm_ftm d m2)
  | Imp -> trm_ftm d (Lam(mk_prop,Lam(mk_prop,Ap(Ap(Imp,DB(1,mk_prop)),DB(0,mk_prop)))))
  | Forall(a) -> trm_ftm d (Lam(mk_ar a mk_prop,Ap(Forall(a),DB(0,mk_ar a mk_prop))))
  | Eq(a) -> trm_ftm d (Lam(a,Lam(a,Ap(Ap(Eq(a),DB(1,a)),DB(0,a)))))
  | Iff -> trm_ftm d (Lam(mk_prop,Lam(mk_prop,Ap(Ap(Eq(mk_prop),DB(1,mk_prop)),DB(0,mk_prop)))))
  | True -> trm_ftm d (Ap(Ap(Imp,False),False))
  | Ap(Neg,m1) -> trm_ftm_neg d m1
  | Neg -> trm_ftm d (Lam(mk_prop,Ap(Neg,DB(0,mk_prop))))
  | Ap(Exists(a),Lam(_,m1)) -> trm_ftm_neg d (Ap(Forall(a),Lam(a,Ap(Neg,m1))))
  | Exists(a) -> trm_ftm d (Lam(mk_ar a mk_prop,Ap(Neg,Ap(Forall(a),Lam(a,Ap(Neg,Ap(DB(1,mk_ar a mk_prop),DB(0,a))))))))
  | Ap(Ap(Or,m1),m2) -> mk_norm_imp (trm_ftm_neg d m1) (trm_ftm d m2)
  | Ap(Ap(And,m1),m2) -> trm_ftm_neg d (Ap(Ap(Imp,m1),Ap(Ap(Imp,m2),False)))
  | Or -> trm_ftm d (Lam(mk_prop,Lam(mk_prop,Ap(Ap(Imp,Ap(Ap(Imp,DB(1,mk_prop)),False)),DB(0,mk_prop)))))
  | And -> trm_ftm d (Lam(mk_prop,Lam(mk_prop,Ap(Ap(Imp,Ap(Ap(Imp,DB(1,mk_prop)),Ap(Ap(Imp,DB(0,mk_prop)),False))),False))))
  | Ap(m1,m2) -> mk_norm_ap (trm_ftm d m1) (trm_ftm d m2)
and trm_ftm_neg d m = fneg(trm_ftm d m);;

let rec ftm_trm name_tp cx m =
  let maincases m =
    match get_tag m with
    | FT_DB -> let i = get_no m in DB(i,List.nth cx i)
    | FT_Name -> let x = get_no m in let x2 = name_no_rev x in Name(x2,Vector.get name_tp x)
    | FT_Ap -> let m1 = get_l m in let m2 = get_r m in Ap(ftm_trm name_tp cx m1,ftm_trm name_tp cx m2)
    | FT_Lam -> let a = get_no m in let m1 = get_l m in let a2 = ty_f_rev a in Lam(a2,ftm_trm name_tp (a2::cx) m1)
    | FT_Imp -> let m1 = get_l m in let m2 = get_r m in Ap(Ap(Imp,ftm_trm name_tp cx m1),ftm_trm name_tp cx m2)
    | FT_All -> let a = get_no m in let m1 = get_l m in let a2 = ty_f_rev a in Ap(Forall(a2),Lam(a2,ftm_trm name_tp (a2::cx) m1))
    | FT_False -> False
    | FT_Choice -> let a = get_no m in Choice(ty_f_rev a)
    | FT_Eq -> let a = get_no m in let m1 = get_l m in let m2 = get_r m in Ap(Ap(Eq(ty_f_rev a),ftm_trm name_tp cx m1),ftm_trm name_tp cx m2)
    | FT_None -> raise (Failure "FT_None")
  in
  (** get rid of double negations because proof reconstruction expects it **)
  if get_isneg m then Ap(Ap(Imp,maincases (get_nonnegated m)), False) else maincases m

let rec ftm_trm_2 name_tp cx m =
  let maincases m =
    match get_tag m with
    | FT_DB -> let i = get_no m in DB(i,List.nth cx i)
    | FT_Name -> let x = get_no m in let x2 = name_no_rev x in Name(x2,ty_f_rev (Hashtbl.find name_tp x))
    | FT_Ap -> let m1 = get_l m in let m2 = get_r m in Ap(ftm_trm_2 name_tp cx m1,ftm_trm_2 name_tp cx m2)
    | FT_Lam -> let a = get_no m in let m1 = get_l m in let a2 = ty_f_rev a in Lam(a2,ftm_trm_2 name_tp (a2::cx) m1)
    | FT_Imp -> let m1 = get_l m in let m2 = get_r m in Ap(Ap(Imp,ftm_trm_2 name_tp cx m1),ftm_trm_2 name_tp cx m2)
    | FT_All -> let a = get_no m in let m1 = get_l m in let a2 = ty_f_rev a in Ap(Forall(a2),Lam(a2,ftm_trm_2 name_tp (a2::cx) m1))
    | FT_False -> False
    | FT_Choice -> let a = get_no m in Choice(ty_f_rev a)
    | FT_Eq -> let a = get_no m in let m1 = get_l m in let m2 = get_r m in Ap(Ap(Eq(ty_f_rev a),ftm_trm_2 name_tp cx m1),ftm_trm_2 name_tp cx m2)
    | FT_None -> raise (Failure "FT_None")
  in
  (** get rid of double negations because proof reconstruction expects it **)
  if get_isneg m then Ap(Ap(Imp,maincases (get_nonnegated m)), False) else maincases m

let ftm_db_p i m =
  match get_tag m with
  | FT_DB -> get_no m = i
  | _ -> false

let rec ftm_str m =
  match get_tag m with
  | FT_DB -> let i = get_no m in Printf.sprintf "?%d" i
  | FT_Name -> let x = get_no m in Printf.sprintf "\"%s\"" (name_no_rev x)
  | FT_Ap -> let m1 = get_l m in let m2 = get_r m in Printf.sprintf "(Ap %s %s)" (ftm_str m1) (ftm_str m2)
  | FT_Lam -> let m1 = get_l m in Printf.sprintf "(Lam %s)" (ftm_str m1)
  | FT_Imp -> let m1 = get_l m in let m2 = get_r m in Printf.sprintf "(Imp %s %s)" (ftm_str m1) (ftm_str m2)
  | FT_All -> let m1 = get_l m in Printf.sprintf "(All %s)" (ftm_str m1)
  | FT_False -> "(False)"
  | FT_Choice -> let a = get_no m in Printf.sprintf "(Choice %d)" a
  | FT_Eq -> let m1 = get_l m in let m2 = get_r m in Printf.sprintf "(Eq %s %s)" (ftm_str m1) (ftm_str m2)
  | _ -> "?"

type fctx = (int * int) list

(*Lists the base types referenced in a term.
  NOTE the resulting list doesn't contain duplicate elements.*)
let rec base_types_of_trm_f acc (m : ftm) : int list =
  match get_tag m with
  | FT_Lam ->
     let a = get_no m in
     let trm = get_l m in
     let acc' = base_types acc (ty_f_rev a) in
     base_types_of_trm_f acc' trm
  | FT_All ->
     let a = get_no m in
     let trm = get_l m in
     let acc' = base_types acc (ty_f_rev a) in
     base_types_of_trm_f acc' trm
  | FT_Ap ->
     let trm1 = get_l m in
     let trm2 = get_r m in
     let acc' = base_types_of_trm_f acc trm1
     in base_types_of_trm_f acc' trm2
  | FT_Imp ->
     let trm1 = get_l m in
     let trm2 = get_r m in
     let acc' = base_types_of_trm_f acc trm1
     in base_types_of_trm_f acc' trm2
  | FT_Eq ->
     (*let a = get_no m in*)
     let trm1 = get_l m in
     let trm2 = get_r m in
     let acc' = base_types_of_trm_f acc trm1
     in base_types_of_trm_f acc' trm2
  | _ -> acc

(*List the constants that occur in a term, as name-type pairs.
  NOTE the resulting list doesn't contain duplicate constants.*)
let rec consts_of_ftm nh (acc:fctx) (m : ftm) : fctx =
  match get_tag m with
  | FT_Name ->
     let name = get_no m in
     begin
       try
         ignore (List.assoc name acc);
         acc
       with Not_found ->
         (name, Hashtbl.find nh name) :: acc
     end
  | FT_Lam ->
     let trm = get_l m in
     consts_of_ftm nh acc trm
  | FT_All ->
     let trm = get_l m in
     consts_of_ftm nh acc trm
  | FT_Ap ->
     let trm1 = get_l m in
     let trm2 = get_r m in
     let acc' = consts_of_ftm nh acc trm1
     in consts_of_ftm nh acc' trm2
  | FT_Imp ->
     let trm1 = get_l m in
     let trm2 = get_r m in
     let acc' = consts_of_ftm nh acc trm1
     in consts_of_ftm nh acc' trm2
  | FT_Eq ->
     let trm1 = get_l m in
     let trm2 = get_r m in
     let acc' = consts_of_ftm nh acc trm1
     in consts_of_ftm nh acc' trm2
  | _ -> acc

let ftm_closedp m =
  let rec ftm_closedp_r j =
    if j >= 0 then
      if get_fv0 m j then
	false
      else
	ftm_closedp_r (j-1)
    else
      true
  in
  ftm_closedp_r (get_maxv m)
