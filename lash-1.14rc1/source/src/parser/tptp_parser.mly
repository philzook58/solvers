/* File: tptp_parser.mly */
/* tptp_parser.mly file written by Frank Theiss for Chris Benzmueller's LEO-II */
/* Adapted by Michael Faerber to new TPTP syntax - Aug 2018 */
%{
open Lexing
open Formula

let print_error startpos endpos msg =
	if startpos.pos_lnum = endpos.pos_lnum then
		Printf.printf "line %d, characters %d-%d: %s\n"
		startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		(endpos.pos_cnum - endpos.pos_bol)
		msg
	else
		Printf.printf "line %d, character %d - line %d, character %d: %s\n"
		startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol)
		msg

%}

%token Unrecognized

%token LBrkt
%token RBrkt
%token LParen
%token RParen
%token Comma
%token Period
%token Colon

%token Ampersand
%token At
%token Vline
%token Star
%token Plus
%token Arrow
%token Tilde
%token Caret
%token Question
%token Exclamation
%token Equal
%token Nequal

%token Iff
%token Implies
%token If
%token Niff
%token Nor
%token Nand

%token Pi
%token Sigma
%token AtPlus
%token AtMinus
%token Fforall
%token Eexists
%token Assign
%token Longarrow

%token Thf
%token Fof
%token Cnf

%token Dollar_thf
%token Dollar_fof
%token Dollar_cnf
%token Dollar_fot

%token Include

%token <string> Upper_word
%token <string> Lower_word
%token <string> Single_quoted
%token <string> Dollar_word
%token <string> Dollar_dollar_word
%token <string> Distinct_object

%token <string> Real
%token <string> Unsigned_integer
%token <string> Signed_integer

%token EOF

%start tptp_file
%start tptp_input
%start formula_data
%type <Formula.formula list> tptp_file
%type <Formula.formula> tptp_input formula_data

%%
/* Tail recursive, formulae are processed in reverse order */
/* tptp_file :
*    tptp_input tptp_file { Tptp_config.accumulator $1 $2 }
*  | null { [] }
*/

/* Not tail recursive, formulae are processed from first to last */
tptp_file :
    tptp_input { Tptp_config.accumulator2 $1 []; [] }
  | tptp_file tptp_input { Tptp_config.accumulator2 $2 $1; [] }
  | null { [] }

tptp_input :
    annotated_formula {$1}
  | file_include {$1}
  | error { let startpos = Parsing.rhs_start_pos 1 in
	    let endpos = Parsing.rhs_end_pos 1 in
            print_error startpos endpos "syntax error";
            failwith "Syntax Error"}          
;

annotated_formula : 
    thf_annotated {$1}
  /*
  | fof_annotated {$1}
  | cnf_annotated {$1}
  */

thf_annotated :
    Thf LParen name Comma formula_role Comma thf_formula annotations RParen Period
    {Appl (Symbol "$$thf",[$3;$5;$7;$8])}

/*
fof_annotated :
    Fof LParen name Comma formula_role Comma fof_formula annotations RParen Period
    {Appl (Symbol "$$fof",[$3;$5;$7;$8])}

cnf_annotated :
    Cnf LParen name Comma formula_role Comma cnf_formula annotations RParen Period
    {Appl (Symbol "$$cnf", [$3;$5;$7;$8])}
*/

annotations :
    Comma source optional_info {Appl (Symbol "$$annotations", [$2;$3])}
  | null {$1}

formula_role :
    Lower_word { Symbol $1 }
  /* TODO: remove these?
  | Thf { Symbol "thf" }
  | Fof { Symbol "fof" }
  | Cnf { Symbol "cnf" }
  | Include { Symbol "include" }
  */



/**** THF formulae */

thf_formula :
    thf_logic_formula { $1 }
  | thf_atom_typing { $1 }
  /* TODO: subtype */
  | thf_sequent { $1 }

thf_logic_formula :
    thf_unitary_formula { $1 }
  | thf_unary_formula { $1 }
  | thf_binary_formula { $1 }
  | thf_defined_infix { $1 }

thf_binary_formula :
    thf_binary_nonassoc { $1 }
  | thf_binary_assoc { $1 }
  | thf_binary_type { $1 }

thf_binary_nonassoc :
    thf_unit_formula nonassoc_connective thf_unit_formula
    {Appl ($2,[$1;$3])}

thf_binary_assoc :
    thf_or_formula    { Appl (Symbol "|", $1) }
  | thf_and_formula   { Appl (Symbol "&", $1) }
  | thf_apply_formula { $1 }

thf_or_formula :
    thf_unit_formula Vline thf_unit_formula {[$1;$3]}
  | thf_or_formula Vline thf_unit_formula {List.append $1 [$3]}

thf_and_formula :
    thf_unit_formula Ampersand thf_unit_formula {[$1;$3]}
  | thf_and_formula Ampersand thf_unit_formula {List.append $1 [$3]}

thf_apply_formula :
    thf_unit_formula At thf_unit_formula { SymbolAt ($1, $3) }
  | thf_apply_formula At thf_unit_formula { SymbolAt ($1, $3) }

thf_unit_formula :
    thf_unitary_formula { $1 }
  | thf_unary_formula { $1 }
  | thf_defined_infix { $1 }

thf_preunit_formula :
    thf_unitary_formula { $1 }
  | thf_prefix_unary { $1 }

thf_unitary_formula :
    thf_quantified_formula { $1 }
  | thf_atomic_formula { $1 }
  | variable { $1 }
  | LParen thf_logic_formula RParen { $2 }

thf_quantified_formula :
    thf_quantification thf_unit_formula
    {Appl (Symbol "$$quantified", $1 @ [$2])}

thf_quantification :
    thf_quantifier LBrkt thf_variable_list RBrkt Colon
    {[$1;Appl (Symbol "$$tuple", $3)]}

thf_variable_list :
    thf_typed_variable { [ $1 ] }
  | thf_typed_variable Comma thf_variable_list { $1 :: $3 }

thf_typed_variable :
    variable Colon thf_top_level_type { Appl (Symbol "$$typed_var", [$1;$3]) }

thf_unary_formula :
    thf_prefix_unary { $1 }
  | thf_infix_unary { $1 }

thf_prefix_unary :
    unary_connective thf_preunit_formula {Appl ($1, [$2])}
  | th1_unary_connective At thf_top_level_type At thf_preunit_formula {Appl ($1, [$5])}

thf_infix_unary :
    thf_unitary_term infix_inequality thf_unitary_term { Appl ($2, [$1;$3]) }

thf_atomic_formula :
    thf_plain_atomic { $1 }
  | thf_defined_atomic { $1 }
  | thf_system_atomic { $1 }
  | thf_fof_function { $1 }

thf_plain_atomic :
    constant { $1 }
  | thf_tuple { $1 }

thf_defined_atomic :
    defined_constant { $1 }
/* TODO?
  | thf_conditional { $1 }
  | thf_let { $1 }
*/
  | LParen thf_conn_term RParen { $2 }
  | defined_term { $1 }

thf_defined_infix :
    thf_unitary_term defined_infix_pred thf_unitary_term { Appl ($2, [$1;$3]) }

thf_system_atomic :
    system_constant { $1 }

thf_fof_function :
    functorr LParen thf_arguments RParen {Appl ($1, $3)}
  | defined_functor LParen thf_arguments RParen {Appl ($1, $3)}
  | system_functor LParen thf_arguments RParen {Appl ($1, $3)}


/* TODO: lots of stuff missing here, related to $let and $ite */


thf_unitary_term :
    thf_atomic_formula { $1 }
  | variable { $1 }
  | LParen thf_logic_formula RParen { $2 }

thf_tuple :
    LBrkt RBrkt { Appl (Symbol "$$tuple", []) }
  | LBrkt thf_formula_list RBrkt { Appl (Symbol "$$tuple", $2) }

thf_formula_list :
    thf_logic_formula { [$1] }
  | thf_logic_formula Comma thf_formula_list { $1::$3 }

thf_conn_term :
    nonassoc_connective { $1 }
  | assoc_connective { $1 }
  | infix_equality { $1 }
  | thf_unary_connective { $1 }


thf_arguments :
    thf_formula_list { $1 }

thf_atom_typing :
     untyped_atom Colon thf_top_level_type { Appl (Symbol "$$type_formula", [$1;$3]) }
  |  LParen thf_atom_typing RParen { $2 }

thf_top_level_type :
    thf_unitary_type { $1 }
  | thf_mapping_type { $1 }
  /* TODO
  | thf_apply_type { $1 }
  */

thf_unitary_type :
    thf_unitary_formula { $1 }

thf_apply_type :
    thf_apply_formula { $1 }

thf_binary_type :
    thf_mapping_type { $1 }
  | thf_xprod_type { $1 }
  | thf_union_type { $1 }

thf_mapping_type :
    thf_unitary_type Arrow thf_unitary_type { Appl (Symbol ">", [$1;$3]) }
  | thf_unitary_type Arrow thf_mapping_type { Appl (Symbol ">", [$1;$3]) }

thf_xprod_type :
    thf_unitary_type Star thf_unitary_type { Appl (Symbol "*", [$1;$3]) }
  | thf_xprod_type Star thf_unitary_type { Appl (Symbol "*", [$1;$3]) }

thf_union_type :
    thf_unitary_type Plus thf_unitary_type { Appl (Symbol "+", [$1;$3]) }
  | thf_union_type Plus thf_unitary_type { Appl (Symbol "+", [$1;$3]) }

/* TODO: thf_subtype */

thf_sequent :
    thf_tuple gentzen_arrow thf_tuple { Appl ($2, [$1;$3]) }
  | LParen thf_sequent RParen { $2 }



/**** Connectives - THF */

thf_quantifier :
    fof_quantifier { $1 }
  | th0_quantifier { $1 }
  | th1_quantifier { $1 }

th1_quantifier :
    Pi { Symbol "!>" }
  | Sigma { Symbol "?*" }

th0_quantifier :
    Caret { Symbol "^" }
  | AtPlus  { Symbol "@+" }
  | AtMinus { Symbol "@-" }

thf_unary_connective :
    unary_connective { $1 }
  | th1_unary_connective { $1 }

th1_unary_connective :
  | Fforall { Symbol "!!" }
  | Eexists { Symbol "??" }
  /* TODO: here are some connectives missing */



/**** Connectives - FOF */

fof_quantifier :
    Question { Symbol "?" }
  | Exclamation { Symbol "!" }

nonassoc_connective :
    Iff { Symbol "<=>" }
  | Implies { Symbol "=>" }
  | If { Symbol "<=" }
  | Niff { Symbol "<~>" }
  | Nor { Symbol "~|" }
  | Nand { Symbol "~&" }

assoc_connective :
    Vline { Symbol "|" }
  | Ampersand { Symbol "&" }

unary_connective :
    Tilde { Symbol "~" }

gentzen_arrow :
    Longarrow { Symbol "-->" }

assignment :
    Assign { Symbol ":=" }



/**** Types for THF and TFF */

type_constant :
    type_functor { $1 }

type_functor :
    atomic_word { $1 }

defined_type :
    atomic_defined_word { $1 }

system_type :
    atomic_system_word { $1 }



/**** For all language types */

untyped_atom :
    constant { $1 }
  | system_constant { $1 }

defined_infix_pred :
    infix_equality { $1 }

infix_equality :
    Equal { Symbol "=" }

infix_inequality :
    Nequal { Symbol "!=" }

constant :
    functorr { $1 }

functorr :
    atomic_word { $1 }

system_constant :
    system_functor { $1 }

system_functor :
    atomic_system_word { $1 }

defined_constant :
    defined_functor { $1 }

defined_functor :
    atomic_defined_word { $1 }

defined_term :
    number { $1 }
  | Distinct_object { Symbol $1 }

variable :
    Upper_word { Symbol $1 }



/*
thf_type_formula :
    thf_unitary_formula Colon thf_top_level_type { Appl (Symbol "$$type_formula", [$1;$3]) }
  | constant Colon thf_top_level_type { Appl (Symbol "$$type_formula", [$1;$3]) }

thf_letrec :
    Assign LBrkt thf_letrec_list RBrkt Colon thf_unitary_formula { Appl (Symbol "$$letrec", [Appl (Symbol "$$tuple", $3);$6]) }

thf_letrec_list :
    thf_defined_var { [$1] }
  | thf_defined_var Comma thf_letrec_list { $1::$3 }

thf_defined_var :
    thf_variable assignment thf_logic_formula { Appl ($2, [$1;$3]) }
  | LParen thf_defined_var RParen { $2 }

thf_definition :
    thf_defn_constant assignment thf_logic_formula { Appl ($2, [$1;$3])  }
  | LParen thf_definition RParen { $2 }

thf_defn_constant :
    constant { $1 }
  | thf_type_formula { $1 }
*/



/**** FOF formulae */

/*
fof_formula :
    binary_formula { $1 }
  | unitary_formula { $1 }

binary_formula :
    nonassoc_binary { $1 }
  | assoc_binary { $1 }

nonassoc_binary :
    unitary_formula nonassoc_connective unitary_formula { Appl ($2, [$1;$3]) }

assoc_binary :
    or_formula { Appl (Symbol "|", $1) }
  | and_formula { Appl (Symbol "&", $1) }

or_formula :
    unitary_formula Vline unitary_formula { [$1;$3] }
  | or_formula Vline unitary_formula { List.append $1 [$3] }

and_formula :
    unitary_formula Ampersand unitary_formula { [$1;$3] }
  | and_formula Ampersand unitary_formula { List.append $1 [$3] }

unitary_formula :
    quantified_formula { $1 }
  | unary_formula { $1 }
  | atomic_formula { $1 }
  | LParen fof_formula RParen { $2 }

quantified_formula :
    fof_quantifier LBrkt variable_list RBrkt Colon unitary_formula { Appl (Symbol "$$quantified", [$1;Appl (Symbol "$$tuple", $3);$6]) }

variable_list :
    variable { [ $1 ] }
  | variable Comma variable_list { $1 :: $3 }

unary_formula :
    unary_connective unitary_formula { Appl ($1, [$2]) }
  | fol_infix_unary { $1 }
*/

/* CNF formulae */

/*
cnf_formula :
    LParen disjunction RParen { Appl (Symbol "|", $2) }
  | disjunction { Appl (Symbol "|", $1) }

disjunction :
    literal { [ $1 ] }
  | disjunction Vline literal { List.append $1 [$3] }

literal :
    atomic_formula { Appl (Symbol "$$poslit", [$1]) }
  | Tilde atomic_formula { Appl (Symbol "$$neglit", [$2]) }
  | fol_infix_unary { Appl (Symbol "$$poslit", [$1]) }
*/



/**** First order atoms */

/*
atomic_formula :
    plain_atomic_formula { $1 }
  | defined_atomic_formula { $1 }
  | system_atomic_formula { $1 }

plain_atomic_formula :
    plain_term { $1 }

defined_atomic_formula :
    defined_plain_formula { $1 }
  | defined_infix_formula { $1 }

defined_plain_formula :
    defined_plain_term { $1 }

defined_infix_formula :
    term defined_infix_pred term { Appl ($2, [$1;$3]) }

system_atomic_formula :
    system_term { $1 }
*/


/**** First order terms */

/*
term :
    function_term { $1 }
  | variable { $1 }

function_term :
    plain_term { $1 }
  | defined_term { $1 }
  | system_term { $1 }

plain_term :
    constant { $1 }
  | fof_functor LParen arguments RParen { Appl ($1, $3) }

defined_atomic_term :
    defined_plain_term { $1 }

defined_plain_term :
    defined_constant { $1 }
  | defined_functor LParen arguments RParen { Appl ($1, $3) }

functorr :
    atomic_word { $1 }

system_term :
    system_constant { $1 }
  | system_functor LParen arguments RParen { Appl ($1, $3) }

arguments :
    term { [$1] }
  | term Comma arguments { $1::$3 }
  */


/**** Formula sources */

source :
    general_term { $1 }

general_term :
    general_data { $1 }
  | general_data Colon general_term { Appl (Symbol ":", [$1;$3]) }
  | general_list { Appl (Symbol "$$tuple", $1) }

general_data :
    atomic_word { $1 }
  | atomic_word LParen general_terms RParen { Appl ($1, $3) }
  | variable { $1 }
  | number { $1 }
  | formula_data { $1 }
  | Distinct_object { Symbol $1 }

formula_data :
    Dollar_thf LParen thf_formula RParen { Appl (Symbol "$thf", [$3]) }
  /*
  | Dollar_fof LParen fof_formula RParen { Appl (Symbol "$fof", [$3]) }
  | Dollar_cnf LParen cnf_formula RParen { Appl (Symbol "$cnf", [$3]) }
  | Dollar_fot LParen term RParen { Appl (Symbol "$fot", [$3]) }
  */

general_list :
    LBrkt RBrkt { [] }
  | LBrkt general_terms RBrkt { $2 }

general_terms :
    general_term { [$1] }
  | general_term Comma general_terms {$1::$3 }

optional_info :
    Comma useful_info { Appl (Symbol "$$useful_info", [$2]) }
  | null { $1 }

useful_info :
    general_list { Appl (Symbol "$$tuple", $1) }



/**** Include directives */

file_include :
    Include LParen file_name formula_selection RParen Period { Appl (Symbol "$$include", [$3;$4]) }

formula_selection :
    Comma LBrkt name_list RBrkt { Appl (Symbol "$$formula_selection", [Appl (Symbol "$$tuple",$3)]) }
  | null { $1 }

name_list :
    name { [$1] }
  | name Comma name_list { $1::$3 }



/**** General purpose */

name :
    atomic_word {$1}
  /* TODO: change to integer here */
  | Unsigned_integer {Symbol $1}

atomic_word :
    Lower_word { Symbol $1 }
  | Single_quoted { Symbol $1 }
  /* TODO: remove these?
  | Thf { Symbol "thf" }
  | Fof { Symbol "fof" }
  | Cnf { Symbol "cnf" }
  | Include { Symbol "include" }
  */

atomic_defined_word :
    Dollar_word { Symbol $1 }
  /* TODO: remove these?
  | Dollar_thf { Symbol "$thf" }
  | Dollar_fof { Symbol "$fof" }
  | Dollar_cnf { Symbol "$cnf" }
  | Dollar_fot { Symbol "$fot" }
  */

atomic_system_word :
    Dollar_dollar_word { Symbol $1 }

number :
    Real { Symbol $1 }
  /* TODO: switch to integer, add rational */
  | Signed_integer { Symbol $1 }
  | Unsigned_integer { Symbol $1 }

file_name :
    Single_quoted { Symbol $1 }

null : { Appl (Symbol "$$null",[]) };
