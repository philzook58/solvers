open Util
open Io

class virtual named = object (x)
  method virtual name : string
  method equals : 'b. (<name : string; ..> as 'b) -> bool =
    fun y -> x#name = y#name
end

type symtype = Var | Fun | Th of string

let (put_name,put_name_pad) =
  let rec sub name n i pr =
    if i < n then begin
      match name.[i] with
      | '\\'  -> pr#puts "\\\\"; sub name n (i+1) pr;
      | '#' -> pr#puts "\\#"; sub name n (i+1) pr;
      | '^' -> pr#puts "\\^"; sub name n (i+1) pr;
      | ' ' -> pr#putc name.[i+1]; sub name n (i+2) pr;
      | c   -> pr#putc c; sub name n (i+1) pr;
    end;
  in
  ( ( fun name -> sub name (String.length name) 0),
    ( fun min name pr ->
      let n = String.length name in
      for i = n to min do pr#putc ' ' done;
      sub name n 0 pr
    )
  )

class virtual sym ty0 = object (x:'x)
  inherit named
  val mutable ty = ty0
  method is_var = ty = Var
  method is_fun = not x#is_var
  method is_theoried = match ty with Th _ -> true | _ -> false
  method is_associative = ty = Th "AC" || ty = Th "A"
  method is_commutative = ty = Th "AC" || ty = Th "C"
  method ty = ty
  method set_ty ty' = ty <- ty'
  method output : 'b. (#outputter as 'b) -> unit = put_name x#name
  method output_pad : 'b. int -> (#outputter as 'b) -> unit = fun min os -> put_name_pad min x#name os
  method virtual output_xml : 'b. (#printer as 'b) -> unit
end

class sym_unmarked ty0 name = object (x:'x)
  inherit sym ty0
  method name = name
  method output_xml : 'b. (#printer as 'b) -> unit =
    if x#is_var then MyXML.enclose_inline "var" x#output
    else MyXML.enclose_inline "name" x#output
end

let var_sym name = new sym_unmarked Var name

let mark_name name = " #" ^ name
let marked_name name = name.[0] = ' ' && name.[1] = '#'
let unmark_name name = String.sub name 2 (String.length name - 2)


class sym_marked ty0 name0 = object
  inherit sym ty0
  val mutable name = name0
  method name = mark_name name
  method output_xml =
    MyXML.enclose_inline "sharp" (MyXML.enclose_inline "name" (put_name name))
end

let mark_sym (f:#sym) = new sym_marked f#ty f#name

let freeze_name fname gname i = fname ^ "❆" ^ string_of_int i ^ "_" ^ gname

class sym_freezed (f:#sym) (g:#sym) i =
  let name = freeze_name f#name g#name i in
  object
    inherit sym f#ty
    method name = name
    method output_xml : 'b. (#printer as 'b) -> unit =
      MyXML.enclose_inline "name" (
        f#output << puts "&middot;" <<
        g#output << MyXML.enclose "sup" (put_int i)
      )
  end

class sym_fresh ty i =
  let name = "†" ^ string_of_int i in
  object (x:'x)
    inherit sym ty
    method name = name
    method output_xml : 'b. (#printer as 'b) -> unit =
      MyXML.enclose_inline (if x#is_var then "var" else "name") (
        puts "_" << put_int i
      )
  end

