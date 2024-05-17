open String
open Preterm

type stp = Base of string | Prop | Ar of (stp * stp)

exception ExpectedTypeError of pretrm * stp * stp

type ctx = (string * stp) list

type trm =
    Name of string * stp
  | False | Imp | Forall of stp | Eq of stp | Choice of stp
  | True | Neg | Or | And | Iff | Exists of stp (*** These are normalized away. ***)
  | DB of int * stp
  | Lam of stp * trm
  | Ap of trm * trm

let oo = Ar(Prop,Prop)
let ooo = Ar(Prop,oo)
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
let iff x y = Ap(Ap(Eq(Prop),x),y)
let eq a x y = Ap(Ap(Eq(a),x),y)
let forall a m = Ap(Forall(a),Lam(a,m))
let exists a m = neg (forall a (neg m))
let choice a m = Ap(Choice(a),Lam(a,m))

let existsconst a = let ao = Ar(a,Prop) in Lam(ao,neg (forall a (neg (Ap(DB(1,ao),DB(0,ao))))))

let lpar p = if p then "(" else ""

let rpar p = if p then ")" else ""

let rec stp_str_rec a p =
  match a with
    Base(x) -> x
  | Prop -> "$o"
  | Ar(b,c) -> (lpar p) ^ (stp_str_rec b true) ^ ">" ^ (stp_str_rec c false) ^ (rpar p)

let stp_str a = stp_str_rec a false

let rec stp_contains a = function
    Ar(b, c) -> stp_contains a b || stp_contains a c
  | b -> a = b

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
  | Lam(Ar(a1,a2),DB(0,_)) when (a1 = a2) -> "#1:" ^ (stp_str a1) (*** Church Numeral 1 Printed in a special way. - Chad, Feb 2, 2011 ***)
  | Lam(Ar(a1,a2),Lam(a3,m)) when a1 = a2 && a1 = a3 && church_num_body m -> "#" ^ string_of_int (church_num_body_val m) ^ ":" ^ stp_str a1 (*** Church Numerals Printed in a special way. - Chad, Feb 2, 2011 ***)
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
  | False -> Prop
  | Imp -> ooo
  | Forall(a) -> Ar(Ar(a,Prop),Prop)
  | Eq(a) -> Ar(a,Ar(a,Prop))
  | Choice(a) -> Ar(Ar(a,Prop),a)
  | DB(_,a) -> a
  | Lam(a,n) -> Ar(a,tpof n)
  | Ap(f,n) ->
      begin
	match (tpof f) with
	  Ar(a,b) -> b
	| _ -> raise (GenericSyntaxError("Non-function applied: " ^ (trm_str m)))
      end
  | _ -> raise (GenericSyntaxError("Unexpected type case - were logical constants normalized away? " ^ (trm_str m)))

let ueq x y = Ap(Ap(Eq(tpof(x)),x),y)

(*** Call this to check application is well typed ***)
let ap (m,n) =
  match (tpof m,tpof n) with
  | (Ar(a,b),c) when a = c -> Ap(m,n)
  | (a,c) -> raise (GenericSyntaxError("Ill typed application (" ^ (trm_str m) ^ " : " ^ (stp_str a) ^ ") @ (" ^ (trm_str n) ^ " : " ^ (stp_str c) ^ ")"))


(** Prints type m as a Coq-formatted string on the out_channel c  **)
let rec print_stp_coq c m h p =
  match m with
  | Base x ->
      let x = try (Hashtbl.find h x) with Not_found -> failwith("print_stp_coq can't find coqname of "^x) in
      Printf.fprintf c "%s" x
  | Prop ->
      Printf.fprintf c "o"
  | Ar(a,b) ->
      begin
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
  match m with
    | Base x ->
        if x <> "$i" then
          Printf.fprintf c "%s" x
        else
          Printf.fprintf c "i"(*FIXME this may clash with a base type that's really called "i"*)
    | Prop ->
        Printf.fprintf c "o"
    | Ar(a,b) ->
        begin
(*	        if p then*) Printf.fprintf c "(";
	        print_stp_isar c a true;
	        Printf.fprintf c "=>";
	        print_stp_isar c b false;
(*	        if p then*) Printf.fprintf c ")";
	        flush c
        end

let rec print_stp_coq2 c m p =
  match m with
  | Base _ ->
      Printf.fprintf c "set"
  | Prop ->
      Printf.fprintf c "prop"
  | Ar(a,b) ->
      begin
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
  | Neg -> (Lam(Prop,imp (DB(0,Prop)) False),true)
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
  | Neg -> (Lam(Prop,imp (DB(0,Prop)) False),true)
  | Ap(Ap(Or,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (disj n1 n2,true)
  | Or -> (Lam(Prop,Lam(Prop,disj (DB(1,Prop)) (DB(0,Prop)))),true)
  | Ap(Ap(And,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (conj n1 n2,true)
  | And -> (Lam(Prop,Lam(Prop,conj (DB(1,Prop)) (DB(0,Prop)))),true)
  | Ap(Ap(Iff,m1),m2) ->
      let (n1,_) = logicnorm1 m1 in
      let (n2,_) = logicnorm1 m2 in
      (iff n1 n2,true)
  | Iff -> (Lam(Prop,Lam(Prop,iff (DB(1,Prop)) (DB(0,Prop)))),true)
  | Ap(Exists(a),Lam(_,m1)) ->
      let (n1,_) = logicnorm1 m1 in
      (exists a n1,true)
  | Exists(a) ->
      let ao = Ar(a,Prop) in
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
    PPropTp -> Prop
  | PIndTp when !basetypestobool -> Prop
  | PName _ when !basetypestobool -> Prop
  | PIndTp ->
      if (!ideclared) then Base("$i")
      else
       begin
        ideclared := true;
        raise DeclareInd
       end
  | PName x ->
     begin
       Base x
     end
  | PAr(a,b) -> Ar(to_stp a,to_stp b)
  | PType -> raise Polymorphism
  | _ -> raise (GenericSyntaxError ((pretrm_str m) ^ " is not a simple type"))

let expected_tp m a b =
  match a with
    Some(aa) ->
      if (aa = b) then () else raise (ExpectedTypeError(m,aa,b))
  | _ -> ()

let rec to_trm (h:(string,(trm * stp) * bool ref) Hashtbl.t) (g:ctx) (m:pretrm) (a:stp option) =
  match m with
  | PAp(PName "Eps",a) -> let b = to_stp a in (Choice b,Ar(Ar(b,Prop),b))
  | PName "In" -> let a = Base "set" in (Name("In",Ar(a,Ar(a,Prop))),Ar(a,Ar(a,Prop)))
  | PName "Subq" -> let a = Base "set" in (Lam(a,Lam(a,Ap(Forall(a),Lam(a,Ap(Ap(Imp,Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(2,a))),Ap(Ap(Name("In",Ar(a,Ar(a,Prop))),DB(0,a)),DB(1,a))))))),Ar(a,Ar(a,Prop)))
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
      expected_tp m a Prop;
      (True,Prop)
  | PFalse ->
      expected_tp m a Prop;
      (False,Prop)
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
	expected_tp m a Prop;
	let n0 = to_stp m0 in
	let (n1,a1) = to_trm h g m1 (Some(Ar(n0,Prop))) in
	match a1 with
	  Ar(a1a,Prop) -> (Ap(Exists(a1a),n1),Prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,Ar(Base("*"),Prop)))
      end
  | PAp(PAp(PForall,m0),m1) ->
      begin
	expected_tp m a Prop;
	let n0 = to_stp m0 in
	let (n1,a1) = to_trm h g m1 (Some(Ar(n0,Prop))) in
	match a1 with
	  Ar(a1a,Prop) -> (Ap(Forall(a1a),n1),Prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,Ar(Base("*"),Prop)))
      end
  | PAp(PExists,m1) ->
      begin
	expected_tp m a Prop;
	let (n1,a1) = to_trm h g m1 None in
	match a1 with
	  Ar(a1a,Prop) -> (Ap(Exists(a1a),n1),Prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,Ar(Base("*"),Prop)))
      end
  | PAp(PForall,m1) ->
      begin
	expected_tp m a Prop;
	let (n1,a1) = to_trm h g m1 None in
	match a1 with
	  Ar(a1a,Prop) -> (Ap(Forall(a1a),n1),Prop)
	| _ ->
	    raise (ExpectedTypeError(m1,a1,Ar(Base("*"),Prop)))
      end
  | PAp(PAp(PNIff,m1),m2) ->
      expected_tp m a Prop;
      (preneg (preiff (to_trm_1 h g m1 (Some Prop)) (to_trm_1 h g m2 (Some Prop))),Prop)
  | PNIff ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,preneg (preiff (DB(1,Prop)) (DB(0,Prop))))),ooo)
  | PImplies ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,imp (DB(1,Prop)) (DB(0,Prop)))),ooo)
  | PRevImplies ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,imp (DB(0,Prop)) (DB(1,Prop)))),ooo)
  | PNOr ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,preneg (predisj (DB(1,Prop)) (DB(0,Prop))))),ooo)
  | PNAnd ->
      expected_tp m a ooo;
      (Lam(Prop,Lam(Prop,preneg (preconj (DB(1,Prop)) (DB(0,Prop))))),ooo)
  | PAp(PAp(PEq,m1),m2) ->
      expected_tp m a Prop;
      let (n1,b1) = to_trm h g m1 None in
      let n2 = to_trm_1 h g m2 (Some b1) in
      ((eq b1 n1 n2),Prop)
  | PEq ->
      begin
	match a with
	  Some(Ar(b1,Ar(b2,Prop)) as aa) when (b1 = b2) ->
	    (Lam(b1,Lam(b1,eq b1 (DB(1,Prop)) (DB(0,Prop)))),aa)
	| Some(aa) ->
	    raise (ExpectedTypeError(m,aa,Ar(Base("*"),Ar(Base("*"),Prop))))
	| None ->
	    raise (GenericSyntaxError ("Cannot determine type of unapplied equality"));
      end
  | PAp(PAp(PNEq,m1),m2) ->
      expected_tp m a Prop;
      let (n1,b1) = to_trm h g m1 None in
      let n2 = to_trm_1 h g m2 (Some b1) in
      (preneg (eq b1 n1 n2),Prop)
  | PNEq ->
      begin
	match a with
	  Some(Ar(b1,Ar(b2,Prop)) as aa) when (b1 = b2) ->
	    (Lam(b1,Lam(b1,preneg (eq b1 (DB(1,Prop)) (DB(0,Prop))))),aa)
	| Some(aa) ->
	    raise (ExpectedTypeError(m,aa,Ar(Base("*"),Ar(Base("*"),Prop))))
	| None ->
	    raise (GenericSyntaxError ("Cannot determine type of unapplied negated equality"));
      end
  | PAp(m1,m2) ->
      begin
	let (n1,a1) = to_trm h g m1 None in
	match a1 with
	  Ar(a1a,a1b) ->
	    expected_tp m a a1b;
	    let n2 = to_trm_1 h g m2 (Some a1a) in
	    (Ap(n1,n2),a1b)
	| _ -> raise (GenericSyntaxError("Non-function applied: " ^ (trm_str n1)))
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
      expected_tp m a Prop;
      (to_all h g xl m1,Prop)
  | PEx(xl,m1) ->
      expected_tp m a Prop;
      (to_exists h g xl m1,Prop)
  | PExU(x,a1,m1) ->
      expected_tp m a Prop;
      begin
	let atp = to_stp a1 in
	match to_trm h ((x,atp)::g) m1 (Some Prop) with
	| (m1a,_) -> (Ap(Lam(Ar(atp,Prop),Ap(Exists(atp),Lam(atp,Ap(Ap(And,Ap(DB(1,Ar(atp,Prop)),DB(0,atp))),Ap(Forall(atp),Lam(atp,Ap(Ap(Imp,Ap(DB(2,Ar(atp,Prop)),DB(0,atp))),Ap(Ap(Eq(atp),DB(0,atp)),DB(1,atp))))))))),Lam(atp,m1a)),Prop)
      end
  | PChoice((x,xa),m1) ->
      let xaa = to_stp xa in
      let n1 = to_trm_1 h ((x,xaa)::g) m1 (Some Prop) in
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
	match a with
	  Ar(a1,a2) ->
	    let (n1,_) = to_ulam h ((x,a1)::g) xr m a2 in
	    (Lam(a1,n1),a)
	| _ ->
	    raise (ExpectedTypeError(m,a,Ar(Base("_"),Base("*"))))
      end
  | [] -> to_trm h g m (Some a)
and to_lam h (g:ctx) xl m a =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	match a with
	  Some(Ar(a1,a2) as aa) when (a1 = xaa) ->
	    let (n1,_) = to_lam h ((x,xaa)::g) xr m (Some a2) in
	    (Lam(xaa,n1),aa)
	| Some(aa) ->
	    raise (ExpectedTypeError(m,aa,Ar(xaa,Base("*"))))
	| None ->
	    let (n1,b) = to_lam h ((x,xaa)::g) xr m None in
	    (Lam(xaa,n1),Ar(xaa,b))
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
  | [] -> to_trm_1 h g m (Some Prop)
and to_exists h (g:ctx) xl m =
  match xl with
    ((x,xa)::xr) ->
      begin
	let xaa = to_stp xa in
	let n1 = to_exists h ((x,xaa)::g) xr m in
	Ap(Exists(xaa),Lam(xaa,n1))
      end
  | [] ->
      to_trm_1 h g m (Some Prop)
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

let rec rtp a =
  match a with
    Ar(a1,a2) -> rtp a2
  | _ -> a

let rec argtps_rtp_rec a =
  match a with
  | Ar(a1,a2) ->
      let (al,r) = argtps_rtp_rec a2 in
      (a1::al,r)
  | _ -> ([],a)

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
let rec base_types acc : stp -> string list = function
   Base name ->
   if List.mem name acc then acc
   else name :: acc
 | Prop -> acc
 | Ar (stp1, stp2) ->
   let acc' = base_types acc stp1
   in base_types acc' stp2

(*Lists the base types referenced in a term.
  NOTE the resulting list doesn't contain duplicate elements.*)
let rec base_types_of_trm acc : trm -> string list = function
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
  let varnames = if rtp a = Prop then predvarnames else match a with Ar(_,_) -> funcvarnames | _ -> basevarnames in
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
  | Lam(Ar(a1,a2),DB(0,_)) when (a1 = a2) -> ("#1:" ^ (stp_str a1),0) (*** Church Numeral 1 Printed in a special way. - Chad, Feb 2, 2011 ***)
  | Lam(Ar(a1,a2),Lam(a3,m)) when a1 = a2 && a1 = a3 && church_num_body m -> ("#" ^ string_of_int (church_num_body_val m) ^ ":" ^ stp_str a1,0) (*** Church Numerals Printed in a special way. - Chad, Feb 2, 2011 ***)
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
