open Util

let continuous_int i j = abs(i - j) < 2
let continuous_index (i,_) (j,_) = continuous_int i j
let output_index pr (i,_) = pr#output_int i
let output_space pr = pr#output_char ' '

class ['a] t (pr : #Io.printer) body prefix infix continuous =
	object (self)
		val mutable curr = None
		method put =
			match curr with
			| None -> ()
			| Some(len,x) ->
				if len < 2 then prefix pr else infix pr;
				body x pr;
		method add (y:'a) =
			match curr with
			| None ->
				curr <- Some(0,y);
				self
			| Some(len,x) ->
				if continuous x y then begin
					if len = 0 then self#put;
					curr <- Some(len + 1, y);
				end else begin
					self#put;
					curr <- Some(0,y);
				end;
				self
		method close =
			self#put;
			curr <- None;
	end

class for_int pr prefix =
	[int] t pr Io.put_int (Io.puts prefix) (Io.puts "..") continuous_int

let put_ints prefix is pr =
	let folder abbr i = abbr#add i in
	(List.fold_left folder (new for_int pr prefix) (List.sort compare is))#close

let put_int_set prefix iset pr =
	let folder i abbr = abbr#add i in
	(IntSet.fold folder iset (new for_int pr prefix))#close
