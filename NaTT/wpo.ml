open Util
open Sym
open Term
open Trs
open Dp
open Smt
open Preorder
open Strategy
open Params
open Io
open Wpo_info

exception Continue

type edge_mode = EdgeNone | EdgeDirect | EdgePost

(* delete common elements from ss and ts *)
let delete_common : 'a. ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list * 'a list =
  fun eq ->
  let rec sub ss1 ss ts =
    match ss with
    | [] -> ss1, ts
    | s :: ss ->
      match delete_one eq [] s ts with
      | Some ts -> sub ss1 ss ts
      | None -> sub (s::ss1) ss ts
  in
  sub []

let delete_variables : 'f 'a. (#sym as 'f,'a) wterm list -> ('f,'a) wterm list =
  let rec sub ss1 =
    function
    | []  -> ss1
    | WT(f,_,_) as s :: ss ->
      if f#is_var then sub ss1 ss else sub (s::ss1) ss
  in
  fun ss -> sub [] ss

let ac_unmark_name name =
  if marked_name name then unmark_name name else name

(* SMT variables *)
let usable_v i = "u" ^ string_of_int i
let usable_p_v i = "uP" ^ string_of_int i
let gt_v i = "gt#" ^ string_of_int i
let ge_v i = "ge#" ^ string_of_int i
let gt_r_v i = "gt" ^ string_of_int i
let ge_r_v i = "ge" ^ string_of_int i
let gt_e_v i j = "gt#" ^ string_of_int i ^ "#" ^ string_of_int j
let gt_post_e_v i j = "gtp#" ^ string_of_int i ^ "#" ^ string_of_int j
let gt_p_v i = "gtP" ^ string_of_int i (* probabilistic rules *)
let ge_p_v i = "geP" ^ string_of_int i
let supply_index v i = v ^ "_" ^ string_of_int i

let prec_ge_v fname gname = "pge_" ^ fname ^ "_" ^ gname
let prec_ge fname gname = EV(prec_ge_v fname gname)


module type WPO_PARAMS = sig
  type a
  val p : order_params
end

module Make(P : WPO_PARAMS) = struct
  type a = P.a
  let p = P.p

  let wpo lookup vo wo spo =
  (*** argument comparison ***)
  let lexperm_compargs =
    match p.status_mode with
    | S_empty ->
      fun _ _ _ _ _ -> weakly_ordered
    | _ ->
      if p.prec_mode = PREC_quasi then
        fun finfo ginfo ->
          if finfo == ginfo then
            permuted_lex_extension finfo#perm finfo#mapped
          else
            permuted_lex_extension2 finfo#perm ginfo#perm finfo#mapped ginfo#mapped
      else
        fun finfo ginfo ->
          if finfo == ginfo then
            permuted_lex_extension finfo#perm finfo#mapped
          else
            fun _ _ _ -> not_ordered
  in
  let statused_compargs finfo ginfo order ss ts =
    match ss, ts with
    | [], []  -> weakly_ordered
    | [], _   -> Cons(ginfo#is_quasi_const, LB false)
    | _, []   -> Cons(LB true, smt_not finfo#is_quasi_const)
    | _ ->
      Delay (fun context ->
        let (lge,lgt) =
          context#expand_pair (lexperm_compargs finfo ginfo order ss ts) 
        in
        let (mge,mgt) =
          context#expand_pair (filtered_mset_extension finfo#permed ginfo#permed order ss ts)
        in
        Cons
        ( (finfo#mset_status &^ ginfo#mset_status &^ mge) |^
          (finfo#lex_status  &^ ginfo#lex_status  &^ lge),
          (finfo#mset_status &^ ginfo#mset_status &^ mgt) |^
          (finfo#lex_status  &^ ginfo#lex_status  &^ lgt)
        )
      )
  in
  (* compargs for normal function symbols *)
  let default_compargs =
    if p.ext_mset then
      if p.ext_lex then
        statused_compargs
      else
        fun finfo ginfo -> filtered_mset_extension finfo#permed ginfo#permed
    else if p.ext_lex then
      lexperm_compargs
    else
      fun _ _ _ _ _ -> weakly_ordered
  in
  (*** compargs for AC symbols ***)
  let small_head =
    fun h s -> strictly (spo h (wterm_root s))
  in
  let no_small_head =
    fun h s -> smt_not (small_head h s)
  in
  let comparg_ac =
    fun order h ss ts ->
    Delay (fun context ->
      let ss, ts = delete_common ac_eq ss ts in
      let nss = List.length ss in
      let nts = List.length ts in
      (* variables in ss may not contribute to other than length *)
      let ss = delete_variables ss in
      (* for efficiency *)
      let nxs = List.length ss in
      let nys = nts in
      let xa = Array.of_list ss in
      let ya = Array.of_list ts in
      let compa = Array.init nxs
        (fun i -> Array.init nys
          (fun j -> context#refer Smt.(Prod(Bool,Bool)) (order xa.(i) ya.(j)))
        )
      in
      compose
      (
        let ifilter i = no_small_head h xa.(i-1) in
        let jfilter j = no_small_head h ya.(j-1) in
        filtered_mset_extension_body ifilter jfilter nxs nys compa
      )
      (
        if nss > nts then
          strictly_ordered
        else if nss < nts then
          not_ordered
        else
          let ifilter i = small_head h xa.(i-1) in
          let jfilter j = small_head h ya.(j-1) in
          filtered_mset_extension_body ifilter jfilter nxs nys compa
      )
    )
  in
  (* For AC-RPO.
   * $(cw,cs,ts) \in emb_candidates f ss$ indicates that f(ts) is
   * a strict embedding of \pi(f(ss)) if cs && cw holds, and
   * \pi(f(ss)) iteself if not cs but cw.
   *)
  let emb_candidates =
    let rec sub2 =
      fun fname precond preargs ret afl_g p_g i ->
      function
      | [] -> ret
      | (WT(h,vs,_) as u)::us ->
        (* If u survives after argfilter, then it can pop out.
           If moreover g survives, then the pop-out is strict embedding.
         *)
        let ret =
          (precond &^ p_g i, afl_g, preargs @ (if h#name = fname then vs else [u])) :: ret
        in
        sub2 fname precond preargs ret afl_g p_g (i+1) us
    in
    fun context ->
    let rec sub =
      fun fname precond preargs ret postargs ->
      if precond = LB false then ret else
      match postargs with
      | [] ->
        (* the whole argument is \pi(f(ss)) if the precondition holds *)
        (precond, LB false, preargs) :: ret
      | (WT(g,ts,_) as t)::ss ->
        if fname = g#name then
          (* this argument should be flattened *)
          sub fname precond preargs ret (ts @ ss)
        else (
        let mapper (tcw,tcs,ts') = (tcw,tcs,ts' @ [t]) in
        let ret = List.map mapper ret in
        if g#is_var then
          (* a variable must remain *)
          sub fname precond (preargs @ [t]) ret ss
        else
          let ginfo = lookup g in
          let p_g = ginfo#permed in
          let afl_g = smt_not ginfo#collapse in
          (* pop-out an argument *)
          let precond = context#refer Smt.Bool precond in
          let ret = sub2 fname precond preargs ret afl_g p_g 1 ts in
          (* t may remain, only if its root symbol is not collapsed *)
          sub fname (precond &^ afl_g) (preargs @ [t]) ret ss
      )
    in
    fun fname args -> sub fname (LB true) [] [] args
  in
  let rec ac_rpo_compargs order fname f ss ts =
    Delay (fun context ->
      let mapper (scw,scs,ss') =
        (context#refer Smt.Bool scw, context#refer Smt.Bool scs, ss')
      in
      let sss = List.map mapper (emb_candidates context fname ss) in
      let tss = List.map mapper (emb_candidates context fname ts) in
      let rec step2 =
        fun ge gt ss' tss ->
      match tss with
      | [] ->
        (* ge to all proper embedding is a condition for gt *)
        Cons(ge, ge &^ gt)
      | (tcw,tcs,ts') :: tss ->
        if tcw = LB false then
          (* this is not even a weak embedding, so don't care *)
          step2 ge gt ss' tss
        else if tcs = LB false then
          (* this is at best \pi(t), so go real comparison *)
          smt_split (comparg_ac order f ss' ts') (fun ge2 gt2 ->
            let (ge,gt) = (ge &^ (tcw =>^ ge2), gt |^ (tcw =>^ gt2)) in
            step2 ge gt ss' tss
          )
        else
          smt_split (ac_rpo_compargs order fname f ss' ts') (fun ge3 gt3 ->
            let (ge,gt) =
              (ge &^ (tcw =>^ smt_if tcs gt3 ge3),
               gt |^ (tcw =>^ (smt_not tcs &^ gt3)))
            in
            step2 ge gt ss' tss
          )
      in
      let rec step1 ge gt sss =
      match sss with
      | [] ->
        Cons(ge,gt)
      | (scw,scs,ss') :: sss ->
        if scw = LB false then
          (* this is not even a weak embedding, so don't care *)
          step1 ge gt sss
        else if scs = LB false then
          (* this is at best only weak embedding, so go to the next step *)
          smt_split (step2 (LB true) (LB false) ss' tss) (fun ge2 gt2 ->
            let (ge,gt) = (ge |^ (scw &^ ge2), gt |^ (scw &^ gt2)) in
            step1 ge gt sss
          )
        else
          smt_split (ac_rpo_compargs order fname f ss' ts) (fun ge3 gt3 ->
            (* if this is strict embedding, weak order results strict order *)
            step1 (ge |^ (scw &^ ge3)) (gt |^ (scw &^ smt_if scs ge3 gt3)) sss
          )
      in
      step1 (LB false) (LB false) sss
    )
  in
  let flat_compargs =
    fun f g order ss ts ->
      let fname = ac_unmark_name f#name in
      let gname = ac_unmark_name g#name in
      if fname = gname then
        ac_rpo_compargs order fname f ss ts
      else not_ordered
  in
  (* compargs for f and g *)
  let compargs = fun f g (finfo:wpo_sym) ginfo ->
    match f#ty, g#ty with
    | Fun, Fun -> default_compargs finfo ginfo
    | Th "C", Th "C" -> fun order ss ts ->
      smt_if (finfo#mapped 1)
        (smt_if (ginfo#mapped 1) (mset_extension order ss ts) strictly_ordered)
        (smt_if (ginfo#mapped 1) weakly_ordered not_ordered)
    | Th "A", Th "A"
    | Th "AC", Th "AC"  -> fun order ss ts ->
      smt_if (finfo#mapped 1)
        (smt_if (ginfo#mapped 1) (flat_compargs f g order ss ts) strictly_ordered)
        (smt_if (ginfo#mapped 1) weakly_ordered not_ordered)
    | _ -> fun _ _ _ -> not_ordered
  in
  (*** RPO-like recursive checks ***)

  let order_by_some_arg =
    (* returns:
      some_ge <=> $s_i \gsim t$ for some $i \in \sigma(f)$
      some_gt <=> $s_i \gt t$ for some $i \in \sigma(f)$
    *)
    let rec sub i some_ge some_gt order fperm ss t =
      match ss with
      | []  -> Cons(some_ge, some_gt)
      | s::ss ->
        smt_split (order s t) (fun curr_ge curr_gt ->
          sub (i+1) 
          (some_ge |^ (fperm i &^ curr_ge))
          (some_gt |^ (fperm i &^ curr_gt)) order fperm ss t
        )
    in
    if p.status_mode = S_empty then
      fun _ _ _ _ -> Cons(LB false, LB false)
    else
      fun order fperm ss t -> sub 1 (LB false) (LB false) order fperm ss t
  in
  let order_all_args =
    (* returns:
      all_ge <=> $s \gsim t_j$ for all $j \in \sigma(g)$
      all_gt <=> $s \gt t_j$ for all $j \in \sigma(g)$
    *)
    if p.status_mode = S_empty then
      fun _ _ _ _ -> Cons(LB true, LB true)
    else
      let rec sub j all_ge all_gt order s gperm ts =
        match ts with
        | []  -> Cons(all_ge, all_gt)
        | t::ts ->
          smt_split (order s t) (fun curr_ge curr_gt ->
            smt_let Bool curr_gt
            (fun curr_gt ->
              sub (j+1)
              (all_ge &^ (gperm j =>^ curr_ge))
              (all_gt &^ (gperm j =>^ curr_gt)) order s gperm ts
            )
          )
      in
      fun order s gperm ts -> sub 1 (LB true) (LB true) order s gperm ts
  in
  let rec wpo1 =
    fun (WT(f,ss,sw) as s) (WT(g,ts,tw) as t) ->
    if ac_eq s t then
      weakly_ordered
    else
      compose (wo sw tw) (wpo2 s t)
  and wpo2 =
    fun (WT(f,ss,_) as s) (WT(g,ts,_) as t) ->
    if f#is_var then
      if g#is_var then
        vo f g
      else
        let ginfo = lookup g in
        smt_split (order_all_args wpo1 s ginfo#permed ts) (
          fun all_ge all_gt ->
          smt_split (spo f g) (fun sge sgt ->
            let col_g = ginfo#collapse in
            Cons((col_g &^ all_ge) |^ (all_gt &^ sge), all_gt &^ (col_g |^ sgt))
          ) 
        )
    else
    match ss,ts with
    | [s1], [t1] when f#equals g ->
      let fltp = (lookup f)#permed 1 in
      smt_split (wpo2 s1 t1) (fun rge rgt -> Cons(fltp =>^ rge, fltp &^ rgt))
    | _ -> 
    let finfo = lookup f in
    smt_split (order_by_some_arg wpo1 finfo#permed ss t) (
      fun some_ge some_gt ->
      smt_let Bool some_ge (fun some_ge ->
        let col_f = finfo#collapse in
        let some_gt = smt_if col_f some_gt some_ge in
        if some_gt = LB true then
          strictly_ordered
        else if g#is_var then
          Cons(some_ge, some_gt)
        else
          let ginfo = lookup g in
          smt_split (order_all_args wpo1 s ginfo#permed ts) (
            fun all_ge all_gt ->
            let col_g = ginfo#collapse in
            if all_gt = LB false then
              Cons(some_ge |^ (col_g &^ all_ge), some_gt)
            else
              smt_split (
                  compose (spo f g) (compargs f g finfo ginfo wpo1 ss ts)
                ) (fun rest_ge rest_gt ->
                smt_let Bool all_gt (fun all_gt ->
                  let cond = smt_not col_f &^ smt_not col_g &^ all_gt in 
                  let ge = some_ge |^ (col_g &^ all_ge) |^ (cond &^ rest_ge) in
                  let gt = some_gt |^ (col_g &^ all_gt) |^ (cond &^ rest_gt) in
                  Cons(ge,gt)
                )
              )
          )
      )
    )
  in
  fun annotate s t ->
  Delay(fun context -> wpo1 (annotate context s) (annotate context t))
end

class t =
  fun p (trs : trs) (estimator : Estimator.t) (dg : dg) ->
  let dim = Array.length p.w_templates in
  let solver = create_solver p.smt_params in
  (* Signature as the set of function symbols with their informations. *)
  let sigma : (string,wpo_sym) Hashtbl.t = Hashtbl.create 256 in
  let lookup_name name =
    try Hashtbl.find sigma name with  _ -> raise (Internal name)
  in
  let lookup f = lookup_name f#name in

  (* weight order *)
  let interpreter = new Weight.interpreter p in

  (*** Precedence ***)
  let pmin = LI 0 in
  let pmax = ref (LI 0) in
  let add_prec_default fname finfo =
    let fp = solver#new_variable_base ("p_" ^ fname) in
    finfo#set_prec fp;
    solver#add_assertion (pmin <=^ fp);
    solver#add_assertion (fp <=^ !pmax);
  in
  let add_prec_ac fname finfo =
    if marked_name fname then begin
      (* marked AC symbols have the precedence of unmarked one *)
    end else begin
      add_prec_default fname finfo;
    end;
  in
  let add_prec =
    match p.prec_mode with
    | PREC_none -> fun _ _ -> ()
    | _ when p.prec_partial -> fun fname (finfo : wpo_sym) ->
      finfo#set_prec_ge (prec_ge fname);
      finfo#set_prec_gt (fun gname -> prec_ge fname gname &^ smt_not (prec_ge gname fname));
      ignore (Hashtbl.fold (fun gname ginfo dones ->
        let fg = solver#new_variable (prec_ge_v fname gname) Bool in
        let gf = solver#new_variable (prec_ge_v gname fname) Bool in
        List.iter (fun hname ->
          let fh = prec_ge fname hname in
          let hf = prec_ge hname fname in
          let gh = prec_ge gname hname in
          let hg = prec_ge hname gname in
          solver#add_assertion ((fh &^ hg) =>^ fg);
          solver#add_assertion ((gh &^ hf) =>^ gf);
          solver#add_assertion ((hg &^ gf) =>^ hf);
          solver#add_assertion ((fg &^ gh) =>^ fh);
          solver#add_assertion ((hf &^ fg) =>^ hg);
          solver#add_assertion ((gf &^ fh) =>^ gh);
        ) dones;
        gname::dones
      ) sigma [])
    | _ -> fun fname finfo ->
      (if finfo#base#is_associative then add_prec_ac else add_prec_default) fname finfo
  in
  (* Precedence over symbols *)
  let var_prec x = "vprec_" ^ x#name in
  let quantify_prec =
    if p.prec_quantify then
      fun vs e ->
      smt_context_for_all (fun context ->
        List.iter (fun v ->
          let ev = context#new_variable_base (var_prec v) in
          context#add_assertion (LI 0 <=^ ev);
          context#add_assertion (ev <=^ !pmax);
        ) vs;
        e
      )
    else fun _ e -> e
  in
  let (spo, spo_open, co_spo, co_spo_open) =
    let prec f =
      if f#is_var then EV(var_prec f) else (lookup f)#prec
    in
    let spo_total (f:#sym) (g:#sym) =
      if f#is_var then
        Cons((if g#is_var then LB(f#equals g) else pmin =^ (lookup g)#prec), LB false)
      else if g#is_var then
        Cons((lookup f)#prec =^ !pmax, LB false)
      else
        let pf = (lookup f)#prec in
        let pg = (lookup g)#prec in
        Cons(pf >=^ pg, pf >^ pg)
    in
    let spo_total_open =
      if p.prec_quantify then
        fun (f:#sym) (g:#sym) ->
        let pf = prec f in
        let pg = prec g in
        Cons(pf >=^ pg, pf >^ pg)
      else spo_total
    in
    let spo_partial (f:#sym) (g:#sym) =
      if f#equals g then Cons(LB true, LB false)
      else if f#is_var || g#is_var then Cons(LB false,LB false)
      else
        let finfo = lookup f in
        let gname = g#name in
        Cons(finfo#prec_ge gname, finfo#prec_gt gname)
    in
    let co_spo_partial (g:#sym) (f:#sym) =
      if g#equals f then Cons(LB true, LB false)
      else if g#is_var || f#is_var then Cons(LB false,LB false)
      else
        let finfo = lookup f in
        let gname = g#name in
        Cons(smt_not (finfo#prec_gt gname), smt_not (finfo#prec_ge gname))
    in
    let spo_equiv (f:#sym) (g:#sym) =
      Cons(
        ( if f#equals g then LB true
          else if f#is_var || g#is_var then LB false
          else (lookup f)#prec =^ (lookup g)#prec
        ), LB false
      )
    in
    let spo_equiv_open =
      if p.prec_quantify then
        fun (f:#sym) (g:#sym) -> Cons(prec f =^ prec g, LB false)
      else spo_equiv
    in
    let co_spo_equiv (g:#sym) (f:#sym) =
      Cons(
        LB true,
        ( if g#equals f then LB false
          else if g#is_var || f#is_var then LB false
        	else (lookup g)#prec <>^ (lookup f)#prec
        )
      )
    in
    let co_spo_equiv_open =
      if p.prec_quantify then
        fun (g:#sym) (f:#sym) -> Cons(LB true, prec g <>^ prec f)
      else co_spo_equiv
    in
    let spo_strict (f:#sym) (g:#sym) =
      if f#equals g then
        Cons(LB true, LB false)
      else if f#is_var || g#is_var then
        Cons(LB false, LB false)
      else
        let gt = (lookup f)#prec >^ (lookup g)#prec in
        Cons(gt,gt)
    in
    let co_spo_strict (g:#sym) (f:#sym) =
      if g#equals f then
        Cons(LB true, LB false)
      else if g#is_var || f#is_var then
        Cons(LB false, LB false)
      else
        let ge = (lookup g)#prec >=^ (lookup f)#prec in
        Cons(ge,ge)
    in
    let spo_triv _ _ = Cons (LB true, LB false) in
    match p.prec_mode with
    | PREC_none -> (spo_triv, spo_triv, spo_triv, spo_triv)
    | _ when p.prec_partial -> (spo_partial, spo_partial, co_spo_partial, co_spo_partial)
    | PREC_quasi -> (spo_total, spo_total_open, spo_total, spo_total_open)
    | PREC_equiv -> (spo_equiv, spo_equiv_open, co_spo_equiv, co_spo_equiv_open)
    | PREC_strict -> (spo_strict, spo_strict, co_spo_strict, spo_total_open)
   in

  (*** Usable rules ***)
  let using_usable = p.usable && (not p.dp || dg#minimal) in
  let usable =
    if using_usable then
      fun i -> EV(usable_v i)
    else
      k_comb (LB true)
  in
  let usable_p =
    if using_usable then
      fun i -> EV(usable_p_v i)
    else
      k_comb (LB true)
  in
  let permed finfo = finfo#permed in
  let depend_w finfo i = smt_not (interpreter#constant_at finfo#base i) in
  let rec set_usable filt flag s =
    smt_list_for_all flag (estimator#find_matchable s) &^ set_usable_inner filt flag s
  and set_usable_inner filt flag (Node(f,ss)) =
    if f#is_var then
      smt_list_for_all (set_usable_inner filt flag) ss
    else
      let finfo = lookup f in
      let rec sub i ss =
        match ss with
        | [] -> LB true
        | s::ss -> (filt finfo i =>^ set_usable filt flag s) &^ sub (i+1) ss
      in
      sub 1 ss
  in

  (*** Status ***)
  let add_perm =
    let sub_lex =
      let sub_permed fname finfo n =
        match finfo#status_mode with
        | S_none
        | S_total -> finfo#set_permed (k_comb (LB true))
        | S_empty -> finfo#set_permed (k_comb (LB false))
        | S_partial ->
          if n = 0 then
            finfo#set_permed (k_comb (LB false))
          else (
            let permed_v i = supply_index ("permed_" ^ fname) i in
            let permed_e i = EV(permed_v i) in
            for i = 1 to n do
              solver#add_variable (permed_v i) Bool;
            done;
            finfo#set_permed permed_e;
          )
      in
      let sub_perm fname finfo n =
        match finfo#status_mode with
        | S_none -> finfo#set_perm (fun i k -> LB (i = k))
        | S_empty -> finfo#set_perm (fun _ _ -> LB false)
        | S_total
        | S_partial ->
          if n = 0 then
            finfo#set_perm (fun _ _ -> LB false)
          else if n = 1 then
            finfo#set_perm (fun i _ -> finfo#permed i)
          else (
            let perm_v i k = supply_index (supply_index ("st_" ^ fname) i) k in
            for i = 1 to n do
              for k = 1 to n do
                solver#add_variable (perm_v i k) Bool;
              done;
            done;
            finfo#set_perm (fun i k -> EV(perm_v i k));
          )
      in
      let sub_mapped fname finfo n to_n =
        match finfo#status_mode with
        | S_none
        | S_total -> finfo#set_mapped (k_comb (LB true));
        | S_empty -> finfo#set_mapped (k_comb (LB false));
        | S_partial ->
          let mapped_v k = supply_index ("mapped_" ^ fname) k in
          let mapped_e k = EV(mapped_v k) in
          for k = 1 to n do
            solver#add_variable (mapped_v k) Bool;
          done;
          solver#add_assertion (OD (List.map mapped_e to_n));
          finfo#set_mapped mapped_e;
      in
      fun fname finfo n to_n ->
        sub_permed fname finfo n;
        sub_perm fname finfo n;
        sub_mapped fname finfo n to_n;
        for i = 1 to n do
          let p_i = finfo#permed i in
          if p.status_copy then begin
            for j = 1 to n do
              solver#add_assertion (finfo#perm i j =>^ p_i);
            done;
            solver#add_assertion (p_i =>^ smt_list_exists (finfo#perm i) to_n);
          end else begin
            let (zero,one) = solver#expand_pair (ZeroOne (List.map (finfo#perm i) to_n)) in
            solver#add_assertion (p_i =>^ one);
            solver#add_assertion (p_i |^ zero);
          end;
          let m_i = finfo#mapped i in
          let mapper j = finfo#perm j i in
          let (zero,one) = solver#expand_pair (ZeroOne (List.map mapper to_n)) in
          solver#add_assertion (m_i =>^ one);
          solver#add_assertion (m_i |^ zero);
        done;
    in
    let sub_c =
      let sub_perm finfo =
        finfo#set_perm (
        match finfo#status_mode with
        | S_empty -> k_comb (k_comb (LB false))
        | _ -> fun i j -> if i = j then finfo#permed i else LB false
        )
      in
      let sub_permed fname finfo =
        match finfo#status_mode with
        | S_empty -> finfo#set_permed (k_comb (LB false));
        | _ ->
          let permed_v = "permed_" ^ fname in
          let permed_e _ = EV(permed_v) in
          solver#add_variable permed_v Bool;
          finfo#set_permed permed_e;
      in
      fun fname finfo ->
        sub_perm finfo;
        sub_permed fname finfo;
        finfo#set_mapped finfo#permed;
    in
    fun fname finfo to_n ->
      finfo#set_status_mode
        (if p.status_nest > 0 && trs#nest_of fname > p.status_nest then S_empty
         else p.status_mode);
      match finfo#base#ty with
      | Th th ->
        if th = "C" || th = "AC" then begin
          (* We assume weights are theory compatible *)
          sub_c fname finfo;
        end else begin
          sub_lex fname finfo finfo#base#arity to_n;
        end
      | _ -> sub_lex fname finfo finfo#base#arity to_n;
  in

  let add_mset_status =
    let sub =
      if not p.ext_mset then
        fun _ -> LB false
      else if p.ext_lex then
        fun fname -> solver#new_variable ("mset_" ^ fname) Bool
      else
        fun _ -> LB true
    in
    fun fname finfo ->
      match finfo#base#ty with
      | Th "C"
      | Th "AC" -> finfo#set_mset_status (LB true);
      | _ -> if finfo#base#arity > 1 then finfo#set_mset_status (sub fname);
  in

  (* collapsing argument filters *)
  let add_collapse =
    if p.collapse then
      fun finfo n to_n ->
        if n = 0 then finfo#set_collapse (LB false)
        else
          let f = finfo#base in
          let v = "col_" ^ f#name in
          solver#add_variable v Bool;
          finfo#set_collapse (EV v);
          solver#add_assertion (EV v =>^ ES1 (List.map finfo#permed to_n)); 
          solver#add_assertion (EV v =>^ (smt_list_for_all (fun i -> finfo#permed i =>^ interpreter#collapses_at f i) to_n));
    else
      fun finfo _ _ -> finfo#set_collapse (LB false)
  in

  (*** preparing for function symbols ***)
  let add_symbol f =
    let fname = f#name in
    let finfo = new wpo_sym f in

    let n = f#arity in
    let to_n = int_list 1 n in

    add_prec fname finfo;

    add_perm fname finfo to_n;

    add_collapse finfo n to_n;

    (* for status *)
    add_mset_status fname finfo;

    for i = 1 to n do
      let pi = finfo#permed i in
      (* permed position must be weakly simple *)
      solver#add_assertion (smt_not pi |^ interpreter#weak_simple_at finfo#base i);
    done;

    Hashtbl.add sigma f#name finfo;
  in

(*** WPO ***)
  (* quantifying variable orderings *)
  let wpo_var x y = Cons(LB false, LB false) in
  let wpo_ge_var_name x y = "ge_" ^ x ^ "_" ^ y in
  let wpo_ge_var x y = EV(wpo_ge_var_name x y) in
  let wpo_gt_var_name x y = "gt_" ^ x ^ "_" ^ y in
  let wpo_gt_var x y = EV(wpo_gt_var_name x y) in
  let wpo_var_open =
    if p.wpo_quantify then
      fun x y ->
      let xname = x#name in
      let yname = y#name in
      Cons(wpo_ge_var xname yname, wpo_gt_var xname yname)
    else wpo_var
  in
  let quantify_wpo =
    if p.wpo_quantify then
      let rec add_wpo_vars context =
        let rec sub xname = function
          | [] -> ()
          | y::ys ->
            let yname = y#name in
            let ge_xy = context#new_variable (wpo_ge_var_name xname yname) Smt.Bool in
            let gt_xy = context#new_variable (wpo_gt_var_name xname yname) Smt.Bool in
            let ge_yx = context#new_variable (wpo_ge_var_name yname xname) Smt.Bool in
            let gt_yx = context#new_variable (wpo_gt_var_name yname xname) Smt.Bool in
            context#add_assertion (gt_xy =>^ (ge_xy &^ smt_not ge_yx));
            context#add_assertion (gt_yx =>^ (ge_yx &^ smt_not ge_xy));
            List.iter (fun z ->
              let zname = z#name in
              context#add_assertion (ge_xy &^ wpo_ge_var yname zname =>^ wpo_ge_var xname zname);
              context#add_assertion (ge_xy &^ wpo_gt_var yname zname =>^ wpo_gt_var xname zname);
              context#add_assertion (gt_xy &^ wpo_ge_var yname zname =>^ wpo_gt_var xname zname);
            ) ys;
            sub xname ys;
        in
        function
        | [] -> ()
        | x::xs -> sub x#name xs; add_wpo_vars context xs
      in
      fun vs e -> smt_context_for_all (fun context -> add_wpo_vars context vs; e)
    else fun _ e -> e
  in
  let (order_closed,co_order_closed,order_open,co_order_open) =
    let wo = interpreter#order in
    let co_wo = interpreter#co_order in
    let wo_open = interpreter#order_open in
    let co_wo_open = interpreter#co_order_open in
    if p.prec_mode = PREC_none && p.status_mode = S_empty then (
        (fun s t -> wo (interpreter#eval s) (interpreter#eval t)),
        (fun t s -> co_wo (interpreter#eval t) (interpreter#eval s)),
        (fun s t -> wo_open (interpreter#eval_open s) (interpreter#eval_open t)),
        (fun t s -> co_wo_open (interpreter#eval_open t) (interpreter#eval_open s))
      )
    else
      let module Wpo = Make(struct
          type a = Weight.cmpoly array
          let p = p
        end)
      in
      let module Wpo_Open = Make(struct
          type a = exp array
          let p = p
        end)
      in
      let a = interpreter#annotate in
      let wpo = Wpo.wpo lookup wpo_var wo spo a in
      let co_wpo = Wpo.wpo lookup wpo_var co_wo co_spo a in
      let a_open = interpreter#annotate_open in
      let wpo_open = Wpo_Open.wpo lookup wpo_var_open wo_open spo_open a_open in
      let co_wpo_open = Wpo_Open.wpo lookup wpo_var_open co_wo_open co_spo_open a_open in
      (wpo,co_wpo,wpo_open,co_wpo_open)
  in
  let quantify_w =
    if p.w_quantify then interpreter#quantify else fun _ e -> e
  in
	let quantify vs e = quantify_wpo vs (quantify_prec vs (quantify_w vs e)) in
  let order_rule =
    let closed rule =
      smt_let Bool (smt_list_exists (fun (s,t) -> strictly (co_order_closed t s)) rule#conds) (
        fun co_cond ->
        smt_split (order_closed rule#l rule#r) (
          fun ge gt ->
          Cons(co_cond |^ ge, co_cond |^ gt)
        )
      )
    in
    let quantified rule =
      let co_cond = smt_list_exists (fun (s,t) -> strictly (co_order_open t s)) rule#conds in
      let orient = order_open rule#l rule#r in
      let vs = rule#vars in
      Cons(
        quantify vs (co_cond |^ weakly orient),
        quantify vs (co_cond |^ strictly orient)
      )
    in
    if p.wpo_quantify || p.prec_quantify || p.w_quantify then
      if p.quantify_unconditional then quantified
      else fun rule ->
        if rule#is_conditional then quantified rule
        else closed rule
    else closed
  in
  let (order,co_order) =
    let sub1 ord t s =
      let vars = union_vars (vars t) s in
      let orient = ord t s in
      Cons(quantify vars (weakly orient), quantify vars (strictly orient))
    in
    if p.wpo_quantify || p.prec_quantify || p.w_quantify then
      (sub1 order_open, sub1 co_order_open)
    else (order_closed, co_order_closed)
  in
object (x)

  inherit Wpo_printer.t p solver sigma interpreter

  val mutable initialized = false
  val mutable use_scope = p.use_scope
  val mutable use_scope_last_size = 0
  val mutable dp_flag_table = Hashtbl.create 256
  val mutable edge_flag_table = Hashtbl.create 256
  val mutable post_edge_flag_table = Hashtbl.create 256
  val mutable rule_flag_table = Hashtbl.create 256
  val mutable prule_flag_table = Hashtbl.create 4

  method using_usable = using_usable

  method init =
    initialized <- true;
    debug (puts " Initializing.");
    solver#init;

    interpreter#init solver trs dg;

    (* generating the signature *)

    if p.prec_mode <> PREC_none then
      (* set max precedence *)
      pmax := LI (trs#get_fun_count);

    Hashtbl.clear sigma;
    trs#iter_funs add_symbol;

    if p.prec_mode <> PREC_none then begin
      (* special treatment of associative symbols *)
      let iterer fname finfo =
        if finfo#base#is_associative then begin
          (* marked associative symbols have the precedence of unmarked one *)
          if marked_name fname then begin
            finfo#set_prec (lookup_name (unmark_name fname))#prec;
          end;
        end;
      in
      Hashtbl.iter iterer sigma;
    end;

  (** adds a probabilistic rule *)
  method private add_prule i =
    if not (Hashtbl.mem prule_flag_table i) then
    try
      debug2 (putc ' ' << put_int i);
      Hashtbl.add prule_flag_table i ();
      let prule = trs#find_prule i in
      let lw = get_weight (interpreter#annotate solver prule#l) in
      let lw = Weight.smult (LI(prule#sum)) lw in
      let folder acc coeff r =
        let w = get_weight (interpreter#annotate solver r) in
        let w = Weight.smult (LI coeff) w in
        Weight.add_vec acc w
      in
      let rw = prule#fold_rs folder (Weight.zero_vec dim) in
      let (ge,gt) = solver#expand_pair (interpreter#order lw rw) in
      if using_usable then begin
        solver#add_assertion (usable_p i =>^ ge);
        solver#add_definition (gt_p_v i) Bool gt;
      end else begin
        solver#add_assertion gt;
      end;
    with Inconsistent -> ()
  method private add_prules =
    if trs#is_probabilistic then begin
      debug (endl << puts "  Initializing probabilistic rules:");
      if using_usable then begin
        trs#iter_prules (fun i _ ->
          if not (Hashtbl.mem prule_flag_table i) then begin
            solver#add_variable (usable_p_v i) Bool;
          end;
        );
      end;
      trs#iter_prules (fun i _ -> x#add_prule i);
    end;

  method private add_rule i =
    if not (Hashtbl.mem rule_flag_table i) then
    try
      debug (puts " " << put_int i);
      Hashtbl.add rule_flag_table i ();
      let rule = trs#find_rule i in
      if using_usable then begin (* usable rules technique is applicable *)
        if p.dp then begin
          let filt =
            if dim = 0 then permed (* trivial weight *)
            else depend_w
          in
          solver#add_assertion (usable i =>^ set_usable filt usable rule#r);
          solver#add_assertion (usable i =>^ weakly (order_rule rule));
        end else begin (* incremental rule removal *)
          let (ge,gt) = solver#expand_pair (order_rule rule) in
          solver#add_assertion (usable i =>^ ge);
          solver#add_definition (gt_r_v i) Bool gt;
        end
      end else if p.dp then begin (* usable rules cannot be applied *)
        solver#add_assertion (weakly (order_rule rule));
      end else begin (* direct reduction order proof *)
        solver#add_assertion (strictly (order_rule rule));
      end;
    with Inconsistent -> ();

  method private add_rules current_usables =
    debug (endl << puts "	Initializing rules:");
    if using_usable then begin
      List.iter (fun i ->
        if not (Hashtbl.mem rule_flag_table i) then
          solver#add_variable (usable_v i) Bool;
      ) current_usables;
    end;
    List.iter x#add_rule current_usables;

  method private add_dp i =
    if not (Hashtbl.mem dp_flag_table i) then begin
      Hashtbl.add dp_flag_table i ();
      debug (puts " #" << put_int i << flush);
      let dp = dg#find_dp i in
      let (ge,gt) = solver#expand_pair (order_rule dp) in
      solver#add_definition (ge_v i) Bool ge;
      solver#add_definition (gt_v i) Bool gt;
      (* flag usable rules *)
      if using_usable then begin
        solver#add_assertion (set_usable depend_w usable dp#r);
        solver#add_assertion (set_usable permed usable dp#r);
      end;
    end;
  method private add_dps dps =
    debug (endl << puts "	Initializing DPs:");
    List.iter x#add_dp dps

  method private add_edge i j =
    if not (Hashtbl.mem edge_flag_table (i,j)) then begin
      Hashtbl.add edge_flag_table (i,j) ();
      debug (puts " #" << put_int i << puts "-->#" << put_int j << flush);
      let s = rename_vars (fun v -> "pre_" ^ v) (dg#find_dp i)#r in
      let t = rename_vars (fun v -> "post_" ^ v) (dg#find_dp j)#l in
      solver#add_definition (gt_e_v i j) Bool (strictly (order_rule (rule s t)));
    end;

  method private add_post_edge i j =
    if not (Hashtbl.mem post_edge_flag_table (i,j)) then begin
      Hashtbl.add post_edge_flag_table (i,j) ();
      debug (puts " #" << put_int i << puts "-->#" << put_int j << flush);
      let dp = dg#find_dp i in
      let l = dp#l in
      let r = dp#r in
      let t = rename_vars (fun v -> "post_" ^ v) (dg#find_dp j)#l in
      let v = solver#new_variable (gt_post_e_v i j) Bool in
      solver#add_assertion (v =^ strictly (order_rule (crule l r [(r,t)])));
    end;

  method reset =
    solver#reset;
    Hashtbl.clear dp_flag_table;
    Hashtbl.clear rule_flag_table;
    Hashtbl.clear edge_flag_table;
    Hashtbl.clear post_edge_flag_table;
    initialized <- false;
    debug (puts "solver reset" << endl);

  method push ?(edge=EdgeNone) current_usables dps =
    if initialized then begin
      if p.use_scope_ratio > 0 then
        let curr_size = trs#get_size in
        if (use_scope_last_size - curr_size) * p.use_scope_ratio > curr_size then
        begin
          x#reset;
          x#init;
        end;
    end else begin
      x#init;
    end;
    x#add_rules current_usables;
    x#add_prules;
    x#add_dps dps;
    debug endl;
    ( match edge with
      | EdgeDirect ->
        debug (puts "	Initializing edges:");
        List.iter (fun i -> dg#iter_succ (fun j -> x#add_edge i j) i) dps;
        debug endl;
      | EdgePost ->
        debug (puts "	Initializing post edges:");
        List.iter (fun i -> dg#iter_succ (fun j -> x#add_post_edge i j) i) dps;
        debug endl;
      | EdgeNone -> ()
    );
    if use_scope then
      solver#push;

  method pop =
    if use_scope then
      solver#pop
    else
      x#reset;

  method remove_nodes current_usables scc =
    comment (put_order p << putc '.' << flush);
    try
      x#push current_usables scc;
      comment (putc '.' << flush);
      let folder i ret =
        solver#add_assertion (EV (ge_v i));
        EV (gt_v i) |^ ret
      in
      solver#add_assertion (List.fold_right folder scc (LB false));
      comment (putc '.' << flush);
      solver#check;
      comment (puts " succeeded." << endl);
      proof (x#output_proof << x#output_usables usable current_usables);
      cpf (MyXML.enter "acRedPairProc"); (* CAUTION: manually leave later *)
      cpf (x#output_cpf << MyXML.enter "dps" << MyXML.enter "rules");
      let folder i (rest,removed) =
        if solver#get_bool (EV(gt_v i)) then (
          cpf ((dg#find_dp i)#output_xml);
          dg#remove_dp i;
          (rest, i :: removed)
        ) else (i::rest,removed)
      in
      let (rest,removed) = List.fold_right folder scc ([],[]) in
      proof (puts "    Removed DPs:" << Abbrev.put_ints " #" removed << endl);
      cpf (MyXML.leave "rules" << MyXML.leave "dps" << x#put_usables_cpf usable trs current_usables);
      x#pop;
      Some rest
    with Inconsistent ->
      comment (puts " ");
      x#pop;
      None

  method remove_rules current_usables =
    try
      comment (puts "Direct " << put_order p << puts " ." << flush);
      x#push current_usables [];
      trs#iter_prules (fun i _ -> x#add_prule i);

      comment (putc '.' << flush);

      if using_usable then begin
        (* usable i should be true until i is removed. *)
        List.iter (fun i -> solver#add_assertion (usable i)) current_usables;
        solver#add_assertion
          (smt_list_exists (fun i -> EV(gt_r_v i)) current_usables |^
           trs#fold_prules (fun i _ ret -> ret |^ EV(gt_p_v i)) (LB false)
          );
      end;
      comment (putc '.' << flush);
      solver#check;

      cpf (MyXML.enter "acRuleRemoval"); (* CAUTION: enter but won't leave *)
      cpf x#output_cpf;
      cpf (MyXML.enter "trs" << MyXML.enter "rules");
      if using_usable then begin
        comment (puts " removes:");
        List.iter
        (fun i ->
          if solver#get_bool (EV(gt_r_v i)) then begin
            cpf ((trs#find_rule i)#output_xml);
            trs#remove_rule i;
            comment (puts " " << put_int i);
          end;
        ) current_usables;
        trs#iter_prules
        (fun i _ ->
          if solver#get_bool (EV(gt_p_v i)) then begin
            trs#remove_prule i;
            comment (puts " p" << put_int i);
          end;
        );
        comment endl;
      end else begin
        comment (puts " removes all." << endl);
        List.iter trs#remove_rule current_usables;
        trs#iter_prules (fun i _ -> trs#remove_prule i);
      end;
      proof x#output_proof;
      cpf (MyXML.leave "rules" << MyXML.leave "trs");
      x#pop;
      true
    with Inconsistent -> x#pop; false

  method remove_edges current_usables scc =
    comment (put_order p << putc '.' << flush);
    try
      x#push ~edge:EdgePost current_usables scc;
      comment (putc '.' << flush);
      List.iter (fun i -> solver#add_assertion (EV (ge_v i))) scc;
      solver#add_assertion (
        smt_list_exists (fun i ->
          smt_list_exists (fun j ->
            EV (gt_post_e_v i j)
          ) (dg#succ i)
        ) scc
      );
      comment (putc '.' << flush);
      solver#check;
      comment (puts " succeeded." << endl);
      proof (x#output_proof << x#output_usables usable current_usables);
      proof (puts "    Removed edges:");
      List.iter (fun i ->
        dg#iter_succ (fun j ->
          if solver#get_bool (EV(gt_post_e_v i j)) then begin
            dg#remove_edge i j;
            proof (puts " #" << put_int i << puts "-->#" << put_int j);
          end;
        ) i
      ) scc;
			proof endl;
      x#pop;
      true
    with Inconsistent ->
      comment (puts " ");
      x#pop;
      false

  method remove_post_edges current_usables scc =
    comment (put_order p << putc '.' << flush);
    try
      x#push ~edge:EdgePost current_usables scc;
      comment (putc '.' << flush);
      List.iter (fun i -> solver#add_assertion (EV (ge_v i))) scc;
      solver#add_assertion (
        smt_list_exists (fun i ->
          smt_list_exists (fun j ->
            EV (gt_post_e_v i j)
          ) (dg#succ i)
        ) scc
      );
      comment (putc '.' << flush);
      solver#check;
      comment (puts " succeeded." << endl);
      proof (x#output_proof << x#output_usables usable current_usables);
      proof (puts "    Removed edges:");
      List.iter (fun i ->
        dg#iter_succ (fun j ->
          if solver#get_bool (EV(gt_post_e_v i j)) then begin
            dg#remove_edge i j;
            proof (puts " #" << put_int i << puts "-->#" << put_int j);
          end;
        ) i
      ) scc;
			proof endl;
      x#pop;
      true
    with Inconsistent ->
      comment (puts " ");
      x#pop;
      false

  method co_order t s =
    try
      comment (puts "Co-" << put_order p << puts " ." << flush);
      x#init;
      comment (putc '.' << flush);
      debug (endl << puts "	Asserting rules:");
      trs#iter_rules (fun i rule ->
        debug (putc ' ' << put_int i);
        solver#add_assertion (weakly (order_rule rule));
        debug (putc '.' << flush);
      );
      debug (endl << puts "	Asserting co-ordering.");
      solver#add_assertion (strictly (co_order t s));
      comment (putc '.' << flush);
      solver#check;
      comment (puts " succeeded." << endl);
      cpf x#output_cpf;
      proof x#output_proof;
      true
    with Inconsistent -> false
end;;
