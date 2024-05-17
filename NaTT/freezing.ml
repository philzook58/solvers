open Util
open Sym
open Term
open Trs
open Dp
open Params

let freeze (a : #sym_detailed) nargs (trs : #trs) (dg : #dg) =
  let aarity_tbl = Hashtbl.create 64 in
  let aarity fname =
    try Hashtbl.find aarity_tbl fname
    with Not_found -> 0
  in
  let set_aarity ord fname d =
    try let aa = Hashtbl.find aarity_tbl fname in
      if ord aa d then Hashtbl.replace aarity_tbl fname d;
    with Not_found ->
      Hashtbl.add aarity_tbl fname d;
  in
  let rec dig d (Node(f,ss)) =
    if a#equals f then begin
      dig (d + 1) (List.hd ss);
      List.iter (dig 0) (List.tl ss);
    end else begin
      if f#ty = Fun then set_aarity (<) f#name d;
      List.iter (dig 0) ss;
    end
  in
  let iterer _ rule = dig 0 rule#l; dig 0 rule#r; in
  trs#iter_rules iterer;
  dg#iter_dps iterer;

  let rec dig_hd d (Node(f,ss)) =
    if a#equals f then begin
      dig_hd (d + 1) (List.hd ss);
    end else begin
      if f#ty = Fun then set_aarity (>) f#name d;
    end
  in
  let iterer _ rule = dig_hd 0 rule#l; in
  trs#iter_rules iterer;
  dg#iter_dps iterer;

  let freeze_top (f,ss,d,aa) =
    let f' = if d > 0 then new sym_freezed a f d else f in
    Node(f',ss)
  in
  let rec freeze_term s = freeze_top (freeze_sub s)
  and freeze_sub (Node(f,ss)) =
    if a#equals f then
      match ss with
      | [] -> raise (Internal "freeze")
      | t::ss ->
        let (g, ts, d, aa) as t' = freeze_sub t in
        let ss = List.map freeze_term ss in
        if d < aa then
          (g, ts @ ss, d + 1, aa)
        else
          (f, freeze_top t'::ss, 0, 0)
    else
      (f, List.map freeze_term ss, 0, aarity f#name)
  in
  trs#iter_rules (fun i rule -> trs#replace_rule i (map_rule freeze_term rule));
  dg#iter_dps (fun i dp -> dg#replace_dp i (map_rule freeze_term dp));

  let varlist name start count =
    let last = start + count - 1 in
    let rec sub i =
      if i > last then []
      else var (name ^ string_of_int i) :: sub (i+1)
    in
    sub start
  in
  let iterer fname aa =
    if aa > 0 then begin
      let f = trs#find_sym_name fname in
      let n = f#arity in
      let args = ref (varlist "_" 1 n) in
      let r = ref (app (f :> sym) !args) in
      for i = 1 to aa do
        let fi = trs#get_sym_name (freeze_name a#name fname i) Fun in
        fi#set_arity (n + i * nargs);
        let new_args = varlist "_" (n + i * nargs) nargs in
        let l = app (a :> sym) (!r :: new_args) in
        args := !args @ new_args;
        r := app (fi :> sym) !args;
        trs#add_rule (weak_rule l !r);
      done;
    end;
  in
  Hashtbl.iter iterer aarity_tbl;;

exception Next

let auto_freeze (trs : #trs) (dg : #dg) =
  let folder (a:sym_detailed) a_s =
    try
      if a#ty <> Fun || a#is_const then begin
        raise Next;
      end;
      let nargs = if a#arity > 0 then a#arity - 1 else raise Next in
      let sub good bad =
        let rec sub2 d (Node(f,ss)) =
          if a#equals f then begin
            sub2 (d+1) (List.hd ss);
            List.iter (sub2 0) (List.tl ss);
          end else begin
            if d > 0 then
              if f#ty <> Fun || trs#defines f then bad d else good d;
            List.iter (sub2 0) ss;
          end
        in
        sub2 0
      in
      let iterer_l _ lr = sub (fun _ -> ()) (fun _ -> raise Next) lr#l in
      trs#iter_rules iterer_l;
      dg#iter_dps iterer_l;

      let ngoods = ref 0 in
      let nbads = ref 0 in
      let add r n = r := !r + n in
      let iterer_r _ lr = sub (add ngoods) (add nbads) lr#r in
      trs#iter_rules iterer_r;
      dg#iter_dps iterer_r;

      debug (fun pr ->
        pr#endl;
        pr#puts "evaluating ";
        a#output pr;
        pr#puts ": ";
        pr#put_int !ngoods;
        pr#puts " vs. ";
        pr#put_int !nbads;
      );

      if !ngoods = 0 (*|| !ngoods < !nbads*) then begin
        raise Next;
      end;
      freeze a nargs trs dg;
      a::a_s
    with Next -> a_s
  in
(*
  let compare_occurrence fname gname =
    (trs#find_sym gname).occurence - (trs#find_sym fname).occurence
  in
  let app_candidates = List.sort compare_occurrence trs#get_defsyms in
*)
  debug (fun pr -> pr#enter 2;);
  let ret = trs#fold_syms folder [] in
  debug (fun pr -> pr#leave 2;);
  ret
