let verbosity = Array.of_list [true;true;true;true;false;false;false]

let warning m = if verbosity.(0) then m Io.cerr else ()
let comment m = if verbosity.(1) then m Io.cerr else ()
let problem m = if verbosity.(2) then m Io.cerr else ()
let proof m = if verbosity.(3) then m Io.cerr else ()
let log m = if verbosity.(4) then m Io.cerr else ()
let debug m = if verbosity.(5) then m Io.cerr else ()
let debug2 m = if verbosity.(6) then m Io.cerr else ()

module Hashed = functor (Base : sig type t end) ->
  struct
    type t = Base.t
    let compare = compare
    let hash = Hashtbl.hash
    let equal = (=)
  end

module IntSet = Set.Make(Int)

module StrSet = Set.Make(String)

module LexList = functor (Elt : Map.OrderedType) ->
  struct
    type t = Elt.t list
    let rec compare xs ys =
      match (xs, ys) with
      | [], [] -> 0
      | _ , [] -> 1
      | [], _  -> -1
      | x::xs, y::ys ->
        match Elt.compare x y with
        | 0 -> compare xs ys
        | c -> c
  end

exception Success
exception Unknown
exception Nonterm
exception Unsound of string
exception Internal of string
exception No_support of string

let k_comb x _ = x

let rec int_list m n = if m > n then [] else m :: int_list (m+1) n

let int_array m n = Array.of_list (int_list m n)

let foldl_nonnil z one f =
  let rec sub acc = function
    | [] -> acc
    | x :: xs -> sub (f acc x) xs
  in
  function
  | [] -> z
  | x :: xs -> sub (one x) xs

let put_list elem punc emp list os =
  let rec sub = function
    | [] -> ()
    | x::xs -> punc os; elem x os; sub xs
  in
  match list with
  | [] -> emp os; ()
  | x::xs -> elem x os; sub xs

let rec list_remove f =
  function
  | []  -> raise Not_found
  | x::xs -> if f x then xs else x :: list_remove f xs

(* string s begins with t *)
let begins s t =
  let n = String.length s in
  let m = String.length t in
  n >= m &&
  let rec sub i =
    i = m ||
    s.[i] = t.[i] &&
    sub (i+1)
  in
  sub 0

(* direct product of lists *)
let list_prod_filter : 'a 'b 'c. ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list =
  let sub1 : 'b 'c. ('b -> 'c option) -> 'c list -> 'b list -> 'c list = fun fx ->
    let rec sub zs ys =
      match ys with
      | []  -> zs
      | y::ys -> sub (match fx y with Some z -> z::zs | None -> zs) ys
    in sub
  in
  let sub2 : 'a 'b 'c. ('a -> 'b -> 'c option) -> 'b list -> 'c list -> 'a list -> 'c list = fun f ys ->
    let rec sub zs xs =
      match xs with
      | []  -> zs
      | x::xs -> sub (sub1 (f x) zs ys) xs
    in sub
  in
  fun f xs ys -> sub2 f ys [] xs

let list_prod : 'a 'b 'c. ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list =
  fun f xs ys -> list_prod_filter (fun x y -> Some (f x y)) xs ys

let list_times : 'a 'b. 'a list -> 'b list -> ('a * 'b) list =
  fun xs ys -> list_prod (fun x y -> (x,y)) xs ys

let list_product_fold_filter f = List.fold_right (list_prod_filter f)

let list_product lists = List.fold_right (list_prod (fun x y -> x :: y)) lists [[]]

(* length n sublists *)
let rec subsequences xs =
  match xs with
  | [] -> [[]]
  | x::xs -> let yss = subsequences xs in List.map (fun ys -> x::ys) yss @ yss

let remdups =
  let rec sub acc xs =
  match xs with
  | [] -> acc
  | x::xs -> if List.mem x acc then sub acc xs else sub (x::acc) xs
  in
  fun xs -> sub [] xs

type ('a,'b) sum = Inl of 'a | Inr of 'b

let separate_list f =
  let rec sub ls rs xs =
    match xs with
    | [] -> (ls,rs)
    | x::xs -> match f x with Inl l -> sub (l::ls) rs xs | Inr r -> sub ls (r::rs) xs
  in
  sub [] []

class type output =
  object
    method output : out_channel -> unit
  end;;
class type output_xml =
  object
    inherit output
    method output_xml : out_channel -> unit
  end;;

