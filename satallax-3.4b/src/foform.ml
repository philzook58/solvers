open Syntax

(*** First Order Formulas - Dec 2012 ***)
type fotrm =
    FOVar of string
  | FOFun of string * fotrm list
type foform = (*** assuming a single sort ***)
    FOEq of fotrm * fotrm (* term equivalence *)
  | FOPred of string * fotrm list
  | FOImp of foform * foform (* implication *)
  | FOEqu of foform * foform (* logical equivalence *)
  | FOAll of string * foform
  | FOFal (* false *)

exception NotFO

let foneg fof =
  match fof with
  | FOImp(m,FOFal) -> m
  | _ -> FOImp(fof,FOFal)

(*** These functions assume the type i which will act as the first order type is given. ***)
let rec foftp_p a i : int =
  match a with
  | Ar(b,c) when b = i -> 1 + foftp_p c i
  | _ when a = i -> 0
  | _ -> raise NotFO

let rec foptp_p a i : int =
  match a with
  | Ar(b,c) when b = i -> 1 + foptp_p c i
  | _ when a = Prop -> 0
  | _ -> raise NotFO

let rec trm_to_fotrm_rec m (ml:trm list) i vl =
  match m with
  (* TODO: change this to allow partially applied functions *)
  | Name(x,a) when foftp_p a i = List.length ml ->
    FOFun(x,List.map (fun m' -> trm_to_fotrm_rec m' [] i vl) ml)
  | DB(j,a) when a = i -> FOVar(List.nth vl j)
  | Ap(m1,m2) -> trm_to_fotrm_rec m1 (m2::ml) i vl
  | _ -> raise NotFO

let rec trm_to_foatom_rec m ml i vl =
  match m with
  | Name(x,a) when foptp_p a i = List.length ml ->
    FOPred(x,List.map (fun m' -> trm_to_fotrm_rec m' [] i vl) ml)
  | Ap(m1,m2) -> trm_to_foatom_rec m1 (m2::ml) i vl
  | _ -> raise NotFO

let rec trm_to_foform_rec p i vl eqoequiv =
  match p with
  | False -> FOFal
  | Ap(Ap(Imp,p1),p2) -> FOImp(trm_to_foform_rec p1 i vl eqoequiv,trm_to_foform_rec p2 i vl eqoequiv)
  | Ap(Forall(a),Lam(_,p1)) when a = i ->
      let x = "X" ^ (string_of_int (List.length vl)) in
      FOAll(x,trm_to_foform_rec p1 i (x::vl) eqoequiv)
  | Ap(Ap(Eq(Prop),p1),p2) when eqoequiv -> FOEqu(trm_to_foform_rec p1 i vl eqoequiv,trm_to_foform_rec p2 i vl eqoequiv)
  | Ap(Ap(Eq(a),m1),m2) when a = i -> FOEq(trm_to_fotrm_rec m1 [] i vl,trm_to_fotrm_rec m2 [] i vl)
  | _ -> trm_to_foatom_rec p [] i vl

(*** These functions try to determine if there is a type from which the formula can be viewed as first order ***)
(*** 'None' means it is propositional -- so no type is required. ***)
let rec trm_to_foatom_stp_rec m ml vl =
  match m with
  | Name(x,Ar(i,b)) when 1 + foptp_p b i = List.length ml -> (*** Must be an arrow type because we handle propositional constants below ***)
      (FOPred(x,List.map (fun m' -> trm_to_fotrm_rec m' [] i vl) ml),Some i)
  | Ap(m1,m2) -> trm_to_foatom_stp_rec m1 (m2::ml) vl
  | _ -> raise NotFO

let rec trm_to_foform_stp_rec p vl eqoequiv =
  match p with
  | False -> (FOFal,None)
  | Ap(Ap(Imp,p1),p2) ->
    begin
      match (trm_to_foform_stp_rec p1 vl eqoequiv) with
      | (p1',Some i) -> (FOImp(p1',trm_to_foform_rec p2 i vl eqoequiv),Some i)
      | (p1',None) ->
	  begin
	    match (trm_to_foform_stp_rec p2 vl eqoequiv) with
	    | (p2',Some i) -> (FOImp(p1',p2'),Some i)
	    | (p2',None) -> (FOImp(p1',p2'),None)
	  end
    end
  | Ap(Forall(i),Lam(_,p1)) -> (*** a quantifier determines the type ***)
      let x = "X" ^ (string_of_int (List.length vl)) in
      (FOAll(x,trm_to_foform_rec p1 i (x::vl) eqoequiv),Some i)
  | Ap(Ap(Eq(Prop),p1),p2) when eqoequiv -> (*** Treat eq(o) as equivalence ***)
    begin
      match (trm_to_foform_stp_rec p1 vl eqoequiv) with
      | (p1',Some i) -> (FOEqu(p1',trm_to_foform_rec p2 i vl eqoequiv),Some i)
      | (p1',None) ->
	  begin
	    match (trm_to_foform_stp_rec p2 vl eqoequiv) with
	    | (p2',Some i) -> (FOEqu(p1',p2'),Some i)
	    | (p2',None) -> (FOEqu(p1',p2'),None)
	  end
    end
  | Ap(Ap(Eq(i),m1),m2) -> (*** an equation determines the type ***)
      (FOEq(trm_to_fotrm_rec m1 [] i vl,trm_to_fotrm_rec m2 [] i vl),Some i)
  | Name(x,Prop) -> (*** Propositional constants don't determine the type ***)
      (FOPred(x,[]),None)
  | Ap(m1,m2) -> (*** This will necessarily determine the type ***)
      trm_to_foatom_stp_rec m1 [m2] vl
  | _ -> raise NotFO

(*** Takes a trm p and either returns a pair of a foform with optionally a simple type
     or raises NotFO ***)
let trm_to_foform_stp p eqoequiv = trm_to_foform_stp_rec p [] eqoequiv


let rec printf_fotrm s m =
  match m with
  | FOVar(x) -> Printf.fprintf s "%s" x
  | FOFun(f,[]) -> Printf.fprintf s "c%s" f
  | FOFun(f,(a::al)) ->
      begin
	Printf.fprintf s "f%s(" f;
	printf_fotrm s a;
	List.iter (fun t -> Printf.fprintf s ","; printf_fotrm s t) al;
	Printf.fprintf s ")";
      end

let rec printf_fof s m =
  match m with
  | FOEq(t1,t2) ->
      Printf.fprintf s "(";
      printf_fotrm s t1;
      Printf.fprintf s " = ";
      printf_fotrm s t2;
      Printf.fprintf s ")";
  | FOPred(p,[]) ->
      Printf.fprintf s "q%s" p;
  | FOPred(p,(a::al)) ->
      Printf.fprintf s "r%s(" p;
      printf_fotrm s a;
      List.iter (fun t -> Printf.fprintf s ","; printf_fotrm s t) al;
      Printf.fprintf s ")";
  | FOImp(m1,FOFal) -> (*** handle this as negation because => $false seems to confuse E ***)
      Printf.fprintf s "(~ ";
      printf_fof s m1;      
      Printf.fprintf s ")";
  | FOImp(m1,m2) ->
      Printf.fprintf s "(";
      printf_fof s m1;
      Printf.fprintf s " => ";
      printf_fof s m2;
      Printf.fprintf s ")";
  | FOEqu(m1,m2) ->
      Printf.fprintf s "(";
      printf_fof s m1;
      Printf.fprintf s " <=> ";
      printf_fof s m2;
      Printf.fprintf s ")";
  | FOAll(x,m1) ->
      Printf.fprintf s "( ! [%s] : " x;
      printf_fof s m1;
      Printf.fprintf s ")";
  | FOFal ->
      Printf.fprintf s "$false"


(*** Output FOF as Sexpr -- just for debugging BEGIN ***)
let rec printf_fstrm s m =
  match m with
  | FOVar(x) -> Printf.fprintf s "|%s|" x
  | FOFun(f,[]) -> Printf.fprintf s "|%s|" f
  | FOFun(f,(a::al)) ->
      begin
	Printf.fprintf s "(|%s| " f;
	printf_fstrm s a;
	List.iter (fun t -> Printf.fprintf s " "; printf_fstrm s t) al;
	Printf.fprintf s ")";
      end

let rec printf_fs s m =
  match m with
  | FOEq(t1,t2) ->
      Printf.fprintf s "(= ";
      printf_fstrm s t1;
      Printf.fprintf s " ";
      printf_fstrm s t2;
      Printf.fprintf s ")";
  | FOPred(p,[]) ->
      Printf.fprintf s "|%s|" p;
  | FOPred(p,(a::al)) ->
      Printf.fprintf s "(|%s| " p;
      printf_fstrm s a;
      List.iter (fun t -> Printf.fprintf s " "; printf_fstrm s t) al;
      Printf.fprintf s ")";
  | FOImp(m1,m2) ->
      Printf.fprintf s "(=> ";
      printf_fs s m1;
      Printf.fprintf s " ";
      printf_fs s m2;
      Printf.fprintf s ")";
  | FOEqu(m1,m2) ->
      Printf.fprintf s "(<=> ";
      printf_fs s m1;
      Printf.fprintf s " ";
      printf_fs s m2;
      Printf.fprintf s ")";
  | FOAll(x,m1) ->
      Printf.fprintf s "(ALL |%s| " x;
      printf_fs s m1;
      Printf.fprintf s ")";
  | FOFal ->
      Printf.fprintf s "FALSE"
(*** Output FOF as Sexpr -- just for debugging END ***)
