open Smt;;
open Util;;
open Io;;

let not_ordered = Cons(LB false, LB false)
let weakly_ordered = Cons(LB true, LB false)
let strictly_ordered = Cons(LB true, LB true)

let strictly = smt_cdr
let weakly = smt_car

let compose trit1 trit2 =
  smt_split trit1 (fun ge1 gt1 ->
    if ge1 = LB false || gt1 = LB true then Cons(ge1,gt1)
    else
      smt_split trit2 (fun ge2 gt2 ->
        if ge2 = LB false then Dup(Bool,gt1)
        else if gt2 = LB true then Dup(Bool,ge1)
        else
          smt_let Bool gt1 (fun gt1 ->
            smt_let Bool ge1 (fun ge1 ->
              Cons(gt1 |^ (ge1 &^ ge2), gt1 |^ (ge1 &^ gt2))
            )
          )
      )
  )

let rec smt_order e1 e2 =
  match e1, e2 with
  | LI i1, LI i2  -> Cons(LB(i1 >= i2), LB(i1 > i2))
  | LR r1, LR r2  -> Cons(LB(r1 >= r2), LB(r1 > r2))
  | _ ->
    Delay(fun solver ->
      let e1 = solver#refer_base e1 in
      let e2 = solver#refer_base e2 in
      Cons(e1 >=^ e2, e1 >^ e2)
    )


(*
 * A preorder ${\gsim}: A\times A\to \Prop$ is implemented by
 * $f~a~b = (p,q)$ s.t.\ $p\Iff a \gsim b$, $q \Iff a > b$.
 *)

(* The lexicographic extension. *)
let lex_extension order =
  let rec sub eqs gts xs ys context =
    match xs, ys with
    | [], []  -> let gts = context#refer Bool gts in Cons(gts |^ eqs, gts)
    | [], _   -> let gts = context#refer Bool gts in Cons(gts, gts)
    | _, []   -> let gts = context#refer Bool (gts |^ eqs) in Cons(gts, gts)
    | x::xs, y::ys  ->
      let eq,gt = context#expand_pair (order x y) in
      let eqs = context#refer Bool eqs in
      sub (eq &^ eqs) ((gt &^ eqs) |^ gts) xs ys context
  in
  fun xs ys ->
    match xs,ys with
    | [],[]   -> weakly_ordered
    | [],_    -> not_ordered
    | _,[]    -> strictly_ordered
    | [x],[y] -> order x y
    | _     -> Delay(sub (LB true) (LB false) xs ys)

(* Filtered lexicographic extension. *)
let filtered_lex_extension filter order =
  let rec xrest eqs gts flt i xs context =
    match xs with
    | [] ->
      let eqs = context#refer Bool eqs in
      let gts = context#refer Bool gts in
      Cons(eqs |^ gts, gts |^ (eqs &^ flt))
    | x::xs -> xrest eqs gts (flt |^ filter i) (i+1) xs context
  in
  let rec yrest ges gts i =
    function
    | [] -> Cons(ges, gts)
    | y::ys -> yrest (ges &^ smt_not (filter i)) gts (i+1) ys
  in
  let rec sub eqs gts i xs ys context =
    match xs, ys with
    | [],_  -> let gts = context#refer Bool gts in yrest (eqs |^ gts) gts i ys
    | _,[]  -> xrest eqs gts (LB false) i xs context
    | x::xs, y::ys  ->
      let eq,gt = context#expand_pair (order x y) in
      let eqs = context#refer Bool eqs in
      sub ((smt_not (filter i) |^ eq) &^ eqs)
        ((filter i &^ gt &^ eqs) |^ gts) (i+1) xs ys context
  in
  fun xs ys ->
    match xs,ys with
    | [],_  -> yrest (LB true) (LB false) 1 ys
    | _,[]  -> Delay((xrest (LB true) (LB false) (LB false) 1 xs))
    | _   -> Delay((sub (LB true) (LB false) 1 xs ys))

(* Lexicographic extension with permutation. *)
let permuted_lex_extension perm mapped order xs ys =
  Delay(fun context ->
    let elemcomp = Array.of_list (List.map2 (fun x y -> context#expand_pair (order x y)) xs ys) in
    let min = Array.length elemcomp in
    let rec sub eqs gts k =
      if k > min then
        let gts = context#refer Bool gts in
        Cons(gts |^ eqs, gts)
      else
        let v_eq = context#temp_variable Bool in
        let v_gt = context#temp_variable Bool in
        context#add_assertion (v_gt =>^ mapped k);
        for i = 1 to min do
          let p = perm i k in
          let (curr_eq,curr_gt) = elemcomp.(i-1) in
          context#add_assertion (Not v_eq |^ smt_not p |^ curr_eq);
          context#add_assertion (Not v_gt |^ smt_not p |^ curr_gt);
        done;
        let eqs = context#refer Bool eqs in
        sub (eqs &^ (smt_not (mapped k) |^ v_eq))
          (gts |^ (eqs &^ v_gt))
          (k+1)
    in
    sub (LB true) (LB false) 1
  )

(* Lexicographic extension with permutation. *)
let permuted_lex_extension2 xperm yperm xmapped ymapped order xs ys =
  let xa = Array.of_list xs in
  let ya = Array.of_list ys in
  let xn = Array.length xa in
  let yn = Array.length ya in
  let min = if xn < yn then xn else yn in
  let rec sub eqs gts k context =
    if k > min then
      let gts = context#refer Bool gts in
      if xn = yn then Cons(gts |^ eqs, gts)
      else if xn < yn then
        Cons(gts |^ (eqs &^ smt_not (ymapped k)), gts)
      else
        let eqs = context#refer Bool eqs in
        Cons(gts |^ eqs, gts |^ (eqs &^ xmapped k))
    else
      let v_eq = context#temp_variable Bool in
      let v_gt = context#temp_variable Bool in
      context#add_assertion (v_gt =>^ xmapped k);
      context#add_assertion (v_eq =>^ (xmapped k =^ ymapped k));
      for i = 1 to xn do
        let xp = xperm i k in
        for j = 1 to yn do
          let yp = yperm j k in
          let (curr_ge,curr_gt) = context#expand_pair (order xa.(i-1) ya.(j-1)) in
          context#add_assertion (Not v_eq |^ smt_not xp |^ smt_not yp |^ curr_ge);
          context#add_assertion (Not v_gt |^ smt_not xp |^ smt_not yp |^ curr_gt);
        done
      done;
      let eqs = context#refer Bool eqs in
      sub (eqs &^ v_eq) (gts |^ (eqs &^ v_gt)) (k+1) context
  in
  Delay(sub (LB true) (LB false) 1)


let rec isome ifilter i n =
  if i <= n then
    ifilter i |^ isome ifilter (i+1) n
  else
    LB false
let rec jnone jfilter j m =
  if j <= m then
    smt_not (jfilter j) &^ jnone jfilter (j+1) m
  else
    LB true

(*
 * Filtered multiset ordering:
 * $X >^\mul_P Y$ iff $\{ x\in X \mid P(x) \} >^\mul \{ y\in Y \mid P(y) \}$.
 *)
let filtered_mset_extension_body ifilter jfilter nxs nys compa =
  match nxs, nys with
  | _, 0  -> Cons(LB true, isome ifilter 1 nxs)
  | 0, _  -> Cons(jnone jfilter 1 nys, LB false)
  | 1, 1  ->
    let fx = ifilter 1 in
    let fy = jfilter 1 in
    smt_if fx (smt_if fy compa.(0).(0) strictly_ordered) (smt_if fy not_ordered weakly_ordered)
  | _ ->
    let sub context =
      (* proposition variable for $X \gsim^\Mul_P Y$ *)
      let a = context#temp_variable Bool in
      (* proposition variable s.t. $a\wedge b \Iff X \sim^\Mul_P Y$ *)
      let b = context#temp_variable Bool in
      (*
       *  $c_{ij}$ means that $x_i$ and $y_j$ are compared.
       *  corresponds to $\gamma_{ij}$ of \cite{STACG07}
       *)
      let c = Array.make_matrix nxs nys (LB false) in
      (*
       *  $e_i$ means that $x_i$ is equally-compared, or it is filtered out.
       *  corresponds to $\epsilon_i$ of \cite{STACG07}
       *)
      let e = Array.make nxs (LB false) in
      (* declaring and defining temporal variables *)
      for i = 0 to nxs - 1 do
        for j = 0 to nys - 1 do
          c.(i).(j) <- context#temp_variable Bool;
        done;
        e.(i) <- context#temp_variable Bool;
      done;
    
      for j = 0 to nys - 1 do
        (*
         * if $y_j$ is not filtered and $X \gsim^\mul_P Y$,
         * then some $x_i$ is compared with $y_j$.
         *)
        context#add_assertion
          (Array.fold_left
            (fun p cc -> p |^ cc.(j))
            (smt_not a |^ smt_not (jfilter (j+1)))
            c
          );
      done;
    
      for i = 0 to nxs - 1 do
        let fx = ifilter (i+1) in
        (* if$x_i$ is filtered out, then set $e_i$. *)
        context#add_assertion (fx |^ e.(i));
        (* if $b$, then $x_i$ is equally-compared or filtered. *)
        context#add_assertion (b =>^ e.(i));
        (* if $x_i$ is equally-compared, then exactly one $y_j$ corresponds. *)
        context#add_assertion (Not e.(i) |^ smt_not fx |^ ES1(Array.to_list c.(i)));
        for j = 0 to nys - 1 do
          (* if $x_i$ and $y_j$ are compared, then $x_i$ must not be filtered. *)
          context#add_assertion (c.(i).(j) =>^ fx);
          (* comparing $x_i$ and $y_j$. *)
          let (eq,gt) = context#expand_pair compa.(i).(j) in
          (* if $x_i$ and $y_j$ are equally-compared, then $x_i \sim y_j$ must hold. *)
          context#add_assertion (Not c.(i).(j) |^ Not e.(i) |^ eq);
          (* if $x_i$ and $y_j$ are inequally-compared, then $x_i > y_j$ must hold. *)
          context#add_assertion (Not c.(i).(j) |^ e.(i) |^ gt);
        done;
      done;
      (* bugfix: not strict if all are equally-ordered *)
      context#add_assertion (Array.fold_left (fun p ee -> p |^ Not ee) b e);
      Cons(a, a &^ smt_not b)
    in
    Delay(sub)



let filtered_mset_extension : 'a. _ -> _ -> ('a -> 'a -> exp) -> 'a list -> 'a list -> exp =
  fun ifilter jfilter order xs ys ->
  let nxs = List.length xs in
  let nys = List.length ys in
  let xa = Array.of_list xs in
  let ya = Array.of_list ys in
  let compa = Array.init nxs (fun i -> Array.init nys (fun j -> order xa.(i) ya.(j))) in
  filtered_mset_extension_body ifilter jfilter nxs nys compa

let filtered_mset_extension2 xfilter yfilter order xs ys =
  let nxs = List.length xs in
  let nys = List.length ys in
  let xa = Array.of_list xs in
  let ya = Array.of_list ys in
  let compa = Array.init nxs (fun i -> Array.init nys (fun j -> order xa.(i) ya.(j))) in
  let ifilter i = xfilter xa.(i-1) in
  let jfilter j = yfilter ya.(j-1) in
  filtered_mset_extension_body ifilter jfilter nxs nys compa

let mset_extension : 'a. ('a -> 'a -> exp) -> 'a list -> 'a list -> exp =
  let triv _ = LB true in
  fun order xs ys -> filtered_mset_extension triv triv order xs ys
