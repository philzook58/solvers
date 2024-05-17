class virtual outputter =
  object (x)
    method virtual puts : string -> unit
    method virtual putc : char -> unit
    method virtual flush : unit
    method virtual close : unit
    method put_int i = x#puts (string_of_int i)
    method put_hex i = x#puts (Printf.sprintf "%X" i)
    method put_float f = x#puts (string_of_float f)
    method put_bool b = x#puts (if b then "true" else "false")
    method endl = x#putc '\n'; x#flush;
  end

class wrap_out os =
  object
    inherit outputter
    method puts = output_string os
    method putc = output_char os
    method flush = flush os
    method close = close_out os
  end

class virtual inputter =
  object
    method virtual ready : bool
    method virtual input_line : string
  end

class wrap_in is =
  object
    inherit inputter
    method ready = true
    method input_line = input_line is
  end

class virtual t =
  object
    inherit outputter
    inherit inputter
  end

class virtual printer =
  object (x)
    inherit outputter
    method enter (_:int) = ()
    method leave (_:int) = ()
    method enter_inline = ()
    method leave_inline = ()
  end

class virtual printable =
  object (x)
    method virtual print : 'a. (#printer as 'a) -> unit
  end

class virtual output =
  object (x)
    inherit printable
    method virtual output : 'a. (#outputter as 'a) -> unit
    method print = x#output
  end


class pretty_printer (base : #outputter) maxdepth =
  object (x)
    inherit printer
    val mutable depth = 0
    val mutable indent = fun () -> ()
    method puts = indent (); base#puts
    method putc = indent (); base#putc
    method flush = base#flush
    method close = base#close
    method enter n = depth <- depth + n
    method leave n = depth <- depth - n
    method enter_inline = x#enter maxdepth
    method leave_inline = x#leave maxdepth
    method endl =
      if depth < maxdepth then begin
        base#endl;
        indent <- x#indent;
      end else begin
        base#putc ' ';
      end
    method private indent () =
      for i = 1 to min depth maxdepth do
        base#putc ' ';
      done;
      indent <- fun () -> ()

  end

class pretty_wrap_out os =
  object (x)
    inherit pretty_printer (new wrap_out os) 64
  end

class finalized finalizer =
  let rfin = ref ignore in
  let fin x = rfin := ignore; finalizer x; in
  object (x)
    initializer
      rfin := fin;
      Gc.finalise fin x;
      at_exit (fun _ -> !rfin x)
  end

let null =
  object
    inherit t
    inherit printer
    method puts s = ()
    method putc c = ()
    method flush = ()
    method close = ()
    method ready = false
    method input_line = ""
  end

let cerr = new pretty_wrap_out stderr
let cout = new pretty_wrap_out stdout

let (<<) f g pr = f pr; g pr

let puts s pr = pr#puts s
let putc c pr = pr#putc c
let put_int i pr = pr#put_int i
let put_bool b pr = pr#put_bool b
let endl pr = pr#endl
let flush pr = pr#flush
let nop pr = pr
let enter n pr = pr#enter n
let leave n pr = pr#leave n
let indent n m pr = enter n pr; m pr; leave n
let inline n m pr = pr#enter_inline; m pr; pr#leave_inline
