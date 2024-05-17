open Io
open Sym
open Term

exception Inconsistent

class ['a] t =
  let rec subst1 (x:#named) (Node(f,ss) as s) (Node(g,ts)) =
    let ts' = List.map (subst1 x s) ts in
    if x#equals g then Node(f,ss@ts') else Node(g,ts')
  in
  object (x:'x)
    val table : (string, 'a term) Hashtbl.t = Hashtbl.create 16
    method private get_table = table
    method mem : 'b. (#named as 'b) -> bool =
      fun f -> Hashtbl.mem table f#name
    method find : 'b. (#named as 'b) -> 'a term =
      fun f -> Hashtbl.find table f#name
    method add : 'b. (#named as 'b) -> 'a term -> unit =
      fun f s ->
        try if not (term_eq (x#find f) s) then raise Inconsistent
        with Not_found -> Hashtbl.add table f#name s
    method replace : 'b. (#named as 'b) -> 'a term -> 'x =
      fun f s ->
        let iterer gname t = Hashtbl.replace table gname (subst1 f s t) in
        Hashtbl.iter iterer table;
        if not (x#mem f) then Hashtbl.add table f#name s;
        x
    method compose (y:'x) =
      let (z:'x) = x#copy in
      let z_table = z#get_table in
      let iterer fname s = Hashtbl.replace z_table fname (y#subst s) in
      Hashtbl.iter iterer z_table;
      let iterer gname t =
        if not (Hashtbl.mem z_table gname) then Hashtbl.add z_table gname t
      in
      Hashtbl.iter iterer y#get_table;
      z
    method copy = {< table = Hashtbl.copy table >}
    method subst (Node(f,ss)) =
      let ss' = List.map x#subst ss in
      if f#is_var then
        try let Node(g,ts) = x#find f in Node(g,ts@ss')
        with Not_found -> Node(f,ss')
      else Node(f,ss')
    method output : 'a. (#Io.printer as 'a) -> unit = fun pr ->
      if Hashtbl.length table = 0 then begin
        pr#puts "[ ]";
      end else begin
        let iterer fname s =
          put_name fname pr;
          pr#puts " := ";
          output_term pr s;
          pr#puts "; ";
        in
        pr#puts "[ ";
        Hashtbl.iter iterer table;
        pr#putc ']';
      end;
  end;;

let of_list ps =
  let ret = new t in
  List.iter (fun (v,s) -> ignore (ret#replace v s)) ps;
  ret

let singleton f s = (new t)#replace f s

let unify : (#named as 'a) term -> 'a term -> 'a t option =
  let rec sub1 (unifier : 'a t) (Node((f:'a),ss) as s) (Node(g,ts) as t) =
    if f#is_var then
      if VarSet.mem f#name (varset t) then None else Some(unifier#replace f t)
    else if g#is_var then
      if VarSet.mem g#name (varset s) then None else Some(unifier#replace g s)
    else if f#equals g then
      sub2 unifier ss ts
    else None
  and sub2 unifier ss ts =
    match ss, ts with
    | [], [] -> Some(unifier)
    | (s::ss), (t::ts) ->
      (
        match sub1 unifier (unifier#subst s) (unifier#subst t) with
        | None -> None
        | Some(unifier) -> sub2 unifier ss ts
      )
    | _ -> None
  in
  fun s t -> sub1 (new t) s t

let matches : (#named as 'a) term -> 'a term -> 'a t option =
  let rec sub1 (matcher :'a t) (Node((f:#sym),ss) as s) (Node(g,ts)) =
    if g#is_var then
      try matcher#add g s; Some(matcher)
      with Inconsistent -> None
    else if f#equals g then
      sub2 matcher ss ts
    else None
  and sub2 matcher ss ts =
    match ss, ts with
    | [], [] -> Some(matcher)
    | (s::ss), (t::ts) ->
      (
        match sub1 matcher s t with
        | None -> None
        | Some(matcher) -> sub2 matcher ss ts
      )
    | _ -> None
  in
  fun s t -> sub1 (new t) s t

let vrename v =
  let renamer f = new sym_unmarked f#ty (f#name ^ "_{" ^ v ^ "}") in
  let rec rename renamer (Node(f,ss)) =
    let ss' = List.map (rename renamer) ss in
    Node((if f#is_var then renamer f else f), ss')
  in
  rename renamer

