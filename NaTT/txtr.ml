open Xml
open Io
open Util

type 'a state =
| Parse of 'a * (string * (string * string) list * xml list)
| Fatal of (outputter -> unit)
| Mismatch of string list

let return v elm = Parse(v,elm)

let delay = return ()

let fatal pr _ = Fatal pr

let none _ = Mismatch []

let put_tag tag = putc '<' << puts tag << putc '>'
let put_end_tag tag = puts "</" << puts tag << puts ">"

let describe (tag,_,xmls) =
	match xmls with
	| [] -> put_end_tag tag
	| PCData str :: _ -> puts "text \"" << puts str << putc '"'
	| Element(tag,_,_) :: _ -> put_tag tag

let mandatory p elm =
	match p elm with
	| Mismatch cands -> Fatal (
			puts "expecting " <<
			put_list put_tag (puts ", ") (puts "nothing") cands <<
			puts " but encountered " <<
			describe elm
		)
	| ret -> ret

let optional p elm =
	match p elm with
	| Parse(v,elm') -> Parse(Some v, elm')
	| Mismatch _ -> Parse(None, elm)
	| Fatal err -> Fatal err

let default v p elm =
	match p elm with
	| Mismatch _ -> Parse(v, elm)
	| ret -> ret

let string elm =
	match elm with
	| (tag, atts, PCData v :: xmls) -> Parse(v,(tag,atts,xmls))
	| (tag, atts, xmls) -> Parse("",(tag,atts,xmls))

let int ((tag,atts,xmls) as elm) =
	try (
		match xmls with
		| PCData str :: xmls' -> Parse(int_of_string str,(tag,atts,xmls'))
		| _ -> raise (Invalid_argument "")
	) with _ -> Fatal (puts "expecting an integer but encountered " << describe elm)

let attribute name (tag,atts,xmls) =
	let rec sub pre = function
	| [] -> Mismatch ["@"^name]
	| (name',v) as p :: post ->
		if name = name' then Parse(v, (tag, List.rev_append pre post, xmls))
		else sub (p::pre) post
	in
	sub [] atts

let int_attribute name elm =
	match attribute name elm with
	| Parse(v,elm') -> (
		try Parse(int_of_string v, elm') with _ ->
			Fatal (puts "attribute \"" << puts name <<
				puts "\" is expected to be integer but is \"" << puts v << putc '"'
			)
	)
	| Mismatch cands -> Mismatch cands
	| Fatal err -> Fatal err

let bool_attribute name elm =
	match attribute name elm with
	| Parse(v,elm') ->
		if v = "true" then Parse(true,elm')
		else if v = "false" then Parse(false,elm')
		else Fatal (puts "attribute \"" << puts name << puts "\" is expected to be Boolean but is \"" << puts v << putc '"')
	| Mismatch cands -> Mismatch cands
	| Fatal err -> Fatal err	

let validated_attribute name pat =
	let r = Re.Posix.compile_pat ("^" ^ pat ^ "$") in
	fun elm ->
	match attribute name elm with
	| Parse(v,elm') as ret ->
		if Re.matches r v <> [] then ret
		else Fatal (puts "attribute \"" << puts name << puts "\" should match \"" << puts pat << puts "\" but has value \"" << puts v << putc '"')
	| err -> err

let bind p1 p2 elm =
	match p1 elm with
	| Parse(x,elm') -> mandatory (p2 x) elm'
	| Mismatch cands -> Mismatch cands
	| Fatal err -> Fatal err

let (>>=) = bind

let many_i ?(minOccurs = 0) ?(maxOccurs = -1) =
	let rec sub i acc p elm =
		if i = maxOccurs then Parse(List.rev acc, elm)
		else
			match if i < minOccurs then mandatory (p i) elm else p i elm with
			| Parse(v,elm') -> sub (i+1) (v::acc) p elm'
			| Mismatch _ -> Parse(List.rev acc, elm)
			| Fatal err -> Fatal err
	in
	sub 0 []
let many ?(minOccurs = 0) ?(maxOccurs = -1) p =
	many_i ~minOccurs:minOccurs ~maxOccurs:maxOccurs (fun i -> p)

let (<|>) p1 p2 elm =
	match p1 elm with
	| Mismatch cands -> (
		match p2 elm with
		| Mismatch cands' -> Mismatch (cands @ cands')
		| ret -> ret
	)
	| ret -> ret

let element tag p = function
	| (parentTag, atts, Element ((tag',_,_) as elm) :: xmls) when tag = tag' -> (
		match mandatory p elm with
		| Parse(v,(_,[],[])) -> Parse(v,(parentTag,atts,xmls))
		| Parse(_,((_,[],_) as elm')) ->
			Fatal (puts "expecting </" << puts tag << puts "> but encountered " << describe elm')
		| Parse(_,(_,(att,_)::_,[])) ->
			Fatal (puts "unexpected attribute \"" << puts att << putc '"')
		| err -> err
	)
	| _ -> Mismatch [tag]

let any (parentTag,atts,xmls) = match xmls with
	| [] -> Mismatch ["*"]
	| xml::xmls' -> Parse(xml,(parentTag,atts,xmls'))

let parse p xml =
	match mandatory p ("",[],[xml]) with
	| Parse(v,_) -> v
	| Fatal out -> (out << endl) (cerr:>outputter); raise (Invalid_argument "TXtr error")

let parse_string p str =
	try parse p (Xml.parse_string str) with
		Error e -> cerr#puts (Xml.error e); raise (Error e)

let parse_in p f =
	try parse p (Xml.parse_in f) with
		Error e -> cerr#puts (Xml.error e); raise (Error e)

let parse_file p f =
	try parse p (Xml.parse_file f) with
		Error e -> cerr#puts (Xml.error e); raise (Error e)