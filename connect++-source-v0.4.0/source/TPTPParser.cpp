/*

Copyright © 2023-24 Sean Holden. All rights reserved.

*/
/*

This file is part of Connect++.

Connect++ is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License as published by the 
Free Software Foundation, either version 3 of the License, or (at your 
option) any later version.

Connect++ is distributed in the hope that it will be useful, but WITHOUT 
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for 
more details.

You should have received a copy of the GNU General Public License along 
with Connect++. If not, see <https://www.gnu.org/licenses/>. 

*/

/**
* Corresponds to v8.1.0.0 of the TPTP definition on 2-8-22.
*
* WARNING!
*
* You should probably REALLY not touch this unless you're very 
* familiar indeed with the Spirit library in Boost, which is what's 
* used to build the parser.
*
* The good news is that you should never have to, because I'm a 
* lovely man and have done all the hard work so you don't have to.
* Essentially the class TPTPParser wraps everything up and a call 
* to TPTPParser::parse_tptp_from_file does a great deal (all!) of the work 
* for you. This happens in StackProver::read_from_tptp_file, and at 
* that point all the indices for Terms etc and the Matrix should be 
* built.
*
* Final note: yes this could be simpler, but the aim is to follow the 
* actual TPTP specification as closely as possible. The naming should 
* support this -- names are chosen as much as possible to correspond
* to the TPTP documentation.
*/

#include "TPTPParser.hpp"

/**
* \brief The tptp_parser namespace contains a lot of stuff that's 
*        essentially just global.
*
* "What is this madness!?" I hear you cry.
*
* Well, writing this is made very straightforward if you allow 
* semantic actions to construct the results of the parse in what 
* are essentially global data structures. Hiding them in a namespace 
* takes some of the sting and uglyness away. Doing it differently 
* is, I claim, just making life more difficult -- this way, the 
* TPTPParser class can just pull things out of the eventual 
* globals -- the user doesn't have to be any the wiser and 
* they end up using the TermIndex, Matrix and so on quite happily, 
* because those are the actual end result.
*
* The boost library does actually have good support for doing all 
* this in a nice OO way. Yes, I've tried that too. I came to the 
* conclusion that the current approach yields *much* more 
* readable code.
*/
namespace tptp_parser {
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //--------------------------------------------------------------
  // Pointers allowing semantic actions to act on a variable
  // index and so on. This is a bit ugly, but much easier than
  // trying to use boost::bind to do everything through member 
  // functions.
  //--------------------------------------------------------------
  VariableIndex* var_index_p;
  FunctionIndex* fun_index_p;
  TermIndex* t_index_p;
  PredicateIndex* p_index_p;
  //--------------------------------------------------------------
  // Store the information regarding anything that needs to 
  // be included.
  //--------------------------------------------------------------
  vector<FileIncludeItem> file_includes;
  //--------------------------------------------------------------
  // You may want to selectively include things from a file.
  // This stores the formula names that you actually want to 
  // include. If it's empty, include everything. The 
  // function that reads the formula name 
  // sets the Boolean, which is then used by the function that 
  // actually adds a clause or formula.
  //--------------------------------------------------------------
  set<string> to_include;
  bool include_this_item;
  //--------------------------------------------------------------
  // Recursive file includes require some book-keeping.
  //--------------------------------------------------------------
  fs::path include_file_path;
  //--------------------------------------------------------------
  // You only want the problem status from the original file.
  //--------------------------------------------------------------
  bool is_first_status = true;
  string status;
  //--------------------------------------------------------------
  vector<string> all_defined;
  vector<string> all_system;
  set<string> distinct_objects;
  //--------------------------------------------------------------
  // You only want to add = once, the first time you see it.
  //--------------------------------------------------------------
  bool equals_added;
  Predicate* equals_p;
  //--------------------------------------------------------------
  // You want to know whether a conjecture has been found.
  //--------------------------------------------------------------
  bool conjecture_found = false;
  bool negated_conjecture_found = false;
  bool conjecture_true = false;
  bool conjecture_false = false;
  bool found_true_axiom = false;
  bool found_false_axiom = false; 
  bool negated_conjecture_exists = false;
  bool has_axioms = false;
  bool has_axioms_remaining = false;
  bool cnf_only = false;
  size_t number_of_negated_conjecture_clauses = 0;
  size_t number_of_simplified_negated_conjecture_clauses = 0;
  //--------------------------------------------------------------
  // You also want to keep track of clause roles.
  //--------------------------------------------------------------
  string current_clause_role;
  vector<string> clause_roles;
  //--------------------------------------------------------------
  // And you want to keep track of the formula roles and names.
  //--------------------------------------------------------------
  string current_formula_role;
  vector<string> formula_roles;
  string current_formula_name;
  vector<string> formula_names;
  //--------------------------------------------------------------
  // Used by semanic actions that construct literals and clauses.
  //--------------------------------------------------------------
  bool neg_lit;
  Literal current_lit;
  Clause current_clause;
  vector<Clause> all_clauses;
  //--------------------------------------------------------------
  // Used by the semantic actions that construct FOL formulas.
  //--------------------------------------------------------------
  FOF current_formula(FOFType::Empty);
  vector<FOF> all_formulas;
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  // Parser implementation in Boost Spirit.
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //---------------------------------------------------------------------
  //--------------------------------------------------------------
  // Basic rules. The TPTP definition seems to have some 
  // redundancy, so synonyms are grouped together. Aside from
  // that, this is essentially the relevant parts of the TPTP
  // definition at:
  //
  // http://www.tptp.org/TPTP/SyntaxBNF.html#dollar_word
  //
  // but from the bottom up, and with some minor differences
  // because some things don't play nicely -- see further 
  // comments below.
  //--------------------------------------------------------------
  //--------------------------------------------------------------
  // Character classes...
  //--------------------------------------------------------------
  qi::rule<Iter, char()> percentage_sign =
      qi::char_('%');
  qi::rule<Iter, char()> double_quote =
      qi::char_('"');
  qi::rule<Iter, char()> do_char =
      qi::char_(' ', '!')
      | qi::char_('#', '[')
      | qi::char_(']', '~')
      | ( lit('\\') >> ( qi::char_('"') | qi::char_('\\') ) );
  qi::rule<Iter, char()> single_quote =
      qi::char_('\'');
  qi::rule<Iter, char()> sq_char =
      qi::char_(' ', '&')
      | qi::char_('(', '[')
      | qi::char_(']', '~')
      | ( lit('\\') >> ( qi::char_('\'') | qi::char_('\\') ) );   ;
  qi::rule<Iter, char()> sign =
      qi::char_("+-");
  qi::rule<Iter, char()> dot =
      qi::char_('.');
  qi::rule<Iter, char()> exponent =
      qi::char_("Ee");
  qi::rule<Iter, char()> slash_char =
      qi::char_('/');
  qi::rule<Iter, char()> slosh_char =
      qi::char_('\\');
  qi::rule<Iter, char()> zero_numeric =
      qi::char_('0');
  qi::rule<Iter, char()> non_zero_numeric =
      qi::char_('1','9');
  qi::rule<Iter, char()> numeric =
      qi::char_('0','9');
  qi::rule<Iter, char()> lower_alpha =
      qi::char_('a','z');
  qi::rule<Iter, char()> upper_alpha =
      qi::char_('A','Z');
  qi::rule<Iter, char()> alpha_numeric =
      lower_alpha
      | upper_alpha
      | numeric
      | qi::char_('_');
  qi::rule<Iter, char()> dollar =
      qi::char_('$');
  qi::rule<Iter, char()> printable_char =
      qi::char_(' ', '~');
  // Strictly speaking, should be \n instead of eol.
  qi::rule<Iter, char()> viewable_char =
      printable_char | eol;
  //--------------------------------------------------------------
  // Numbers...
  //--------------------------------------------------------------
  qi::rule<Iter, string()> slash =
      slash_char;
  qi::rule<Iter, string()> slosh =
      slosh_char;

  qi::rule<Iter, string()> unsigned_exp_integer =
      +(numeric);
  qi::rule<Iter, string()> signed_exp_integer =
      sign >> unsigned_exp_integer;
  qi::rule<Iter, string()> exp_integer =
      signed_exp_integer
      | unsigned_exp_integer;
  qi::rule<Iter, string()> dot_decimal =
      dot >> +(numeric);
  qi::rule<Iter, string()> positive_decimal =
      non_zero_numeric >> *(numeric);
  qi::rule<Iter, string()> decimal =
      zero_numeric | positive_decimal;
  qi::rule<Iter, string()> decimal_fraction =
      decimal >> dot_decimal;
  qi::rule<Iter, string()> decimal_exponent =
      (decimal | decimal_fraction) >> exponent >> exp_integer;
  qi::rule<Iter, string()> unsigned_integer =
      decimal;
  qi::rule<Iter, string()> signed_integer =
      sign >> unsigned_integer;
  qi::rule<Iter, string()> integer =
      signed_integer | unsigned_integer;
  qi::rule<Iter, string()> unsigned_rational =
      decimal >> slash >> positive_decimal;
  qi::rule<Iter, string()> signed_rational =
      sign >> unsigned_rational;
  qi::rule<Iter, string()> rational =
      signed_rational | unsigned_rational;
  qi::rule<Iter, string()> unsigned_real =
      decimal_fraction | decimal_exponent;
  qi::rule<Iter, string()> signed_real =
      sign >> unsigned_real;
  qi::rule<Iter, string()> real =
      signed_real | unsigned_real;
  //--------------------------------------------------------------
  // Syntax, not character classes...
  //--------------------------------------------------------------
  // Note that you may need to explicitly use these with ... % vline
  // notation.
  qi::rule<Iter, string()> vline =
      ascii::string("|");
  qi::rule<Iter, string()> star =
      ascii::string("*");
  qi::rule<Iter, string()> plus =
      ascii::string("+");
  qi::rule<Iter, string()> arrow =
      ascii::string(">");
  qi::rule<Iter, string()> less_sign =
      ascii::string("<");
  qi::rule<Iter, string()> hash =
      ascii::string("#");
  //--------------------------------------------------------------
  // Comments and so on...
  //--------------------------------------------------------------
  qi::rule<Iter, string()> lower_word =
      lower_alpha >> *(alpha_numeric);
  qi::rule<Iter, string()> formula_role =
      ascii::string("axiom")
      | ascii::string("hypothesis")
      | ascii::string("definition")
      | ascii::string("assumption")
      | ascii::string("lemma")
      | ascii::string("theorem")
      | ascii::string("corollary")
      | ascii::string("conjecture")
      | ascii::string("negated_conjecture")
      | ascii::string("plain")
      | ascii::string("type")
      | ascii::string("fi_domain")
      | ascii::string("fi_functors")
      | ascii::string("fi_predicates")
      | ascii::string("unknown");
  //--------------------------------------------------------------
  // upper_word and synonyms...
  //--------------------------------------------------------------
  qi::rule<Iter, string()> upper_word =
      upper_alpha
      >> *(alpha_numeric);
  qi::rule<Iter, string()> variable =
      upper_word;
  qi::rule<Iter, string()> dollar_dollar_word =
      dollar
      >> dollar
      >> *(alpha_numeric);
  qi::rule<Iter, string()> dollar_word =
      dollar
      >> *(alpha_numeric);
  qi::rule<Iter, string()> distinct_object =
      double_quote
      >> *(do_char) 
      >> double_quote;
  //--------------------------------------------------------------
  // single_quoted and synonyms...
  //--------------------------------------------------------------
  qi::rule<Iter, string()> single_quoted =
      lit('\'')      // Don't use single_quote as need to strip them.
      >> sq_char
      >> *(sq_char)
      >> lit('\'');
  qi::rule<Iter, string()> file_name =
      single_quoted;
  qi::rule<Iter> null =
      eps;
  // Added to allow extraction of problem status.
  qi::rule<Iter, string()> comment_status =
    ascii::string("Theorem")
    | ascii::string("ContradictoryAxioms")
    | ascii::string("CounterSatisfiable")
    | ascii::string("Satisfiable")
    | ascii::string("Unsatisfiable")
    | ascii::string("Unknown")
    | ascii::string("Open");
  // Added to allow extraction of problem status.
  qi::rule<Iter, string(), ascii::space_type> status_comment =
    qi::char_('%')
    >> ascii::string("Status")
    >> qi::char_(':')
    >> comment_status[CommentStatus()]
    >> lexeme[*(printable_char)]
    >> eol;
  // Added to allow extraction of problem status.
  qi::rule<Iter, string()> standard_comment =
    qi::char_('%')
    >> *(printable_char)
    >> eol;
  // Modified to allow extraction of problem status.
  qi::rule<Iter, string(), ascii::space_type> comment_line =
    status_comment
    | standard_comment;
  qi::rule<Iter, string()> not_star_slash =
      *(*(qi::char_ - qi::char_('*'))
      >> qi::char_('*')
      >> *(qi::char_('*'))
      >> (qi::char_ - (qi::char_('/') | qi::char_('*'))))
      >> *(qi::char_ - qi::char_('*'));
  qi::rule<Iter, string()> comment_block =
      qi::char_('/')
      >> qi::char_('*')
      >> not_star_slash
      >> qi::char_('*') >> *(qi::char_('*')) >> qi::char_('/');
  qi::rule<Iter, string(), ascii::space_type> comment =
      comment_line | comment_block;
  qi::rule<Iter, string()> atomic_defined_word =
      dollar_word;
  qi::rule<Iter, string()> atomic_system_word =
      dollar_dollar_word;
  qi::rule<Iter, string()> system_functor =
      atomic_system_word;
  qi::rule<Iter, string()> system_constant =
      system_functor;
  qi::rule<Iter, string()> number =
      integer | rational | real;
  //--------------------------------------------------------------
  // atomic_word and synonyms...
  //--------------------------------------------------------------
  qi::rule<Iter, string()> atomic_word =
      lower_word
      | single_quoted;
  qi::rule<Iter, string()> predicate =
      atomic_word;
  qi::rule<Iter, string()> functor =
      atomic_word;
  qi::rule<Iter, string()> constant =
      functor;
  qi::rule<Iter, string()> proposition =
      predicate;
  qi::rule<Iter, string()> name =
      atomic_word | integer;
  qi::rule<Iter, string()> defined_predicate =
       ascii::string("$distinct")
       | ascii::string("$less")
       | ascii::string("$lesseq")
       | ascii::string("$greater")
       | ascii::string("$greatereq")
       | ascii::string("$box_P")
       | ascii::string("$box_int")
       | ascii::string("$greater")
       | ascii::string("$box")
       | ascii::string("$dia_P")
       | ascii::string("$dia_i")
       | ascii::string("$dia_int")
       | ascii::string("$dia");
  qi::rule<Iter, string()> defined_proposition =
      ascii::string("$true")
      | ascii::string("$false")
      | defined_predicate;
  //--------------------------------------------------------------
  // Various others.
  //--------------------------------------------------------------
  qi::rule<Iter, string()>
  defined_functor =
      ascii::string("$uminus")
      | ascii::string("$sum")
      | ascii::string("$difference")
      | ascii::string("$product")
      | ascii::string("$quotient")
      | ascii::string("$quotient_e")
      | ascii::string("$quotient_t")
      | ascii::string("$quotient_f")
      | ascii::string("$remainder_e")
      | ascii::string("$remainder_t")
      | ascii::string("$remainder_f")
      | ascii::string("$floor")
      | ascii::string("$ceiling")
      | ascii::string("$truncate")
      | ascii::string("$round")
      | ascii::string("$to_int")
      | ascii::string("$to_rat")
      | ascii::string("$to_real");
  qi::rule<Iter, string()> defined_constant =
      defined_functor;
  qi::rule<Iter, string()> defined_term =
      number | distinct_object;
  qi::rule<Iter, string()> infix_equality =
      ascii::string("=");
  qi::rule<Iter, string()> infix_inequality =
    ascii::string("!=");
  qi::rule<Iter, string()> defined_infix_pred =
    infix_equality;
  //--------------------------------------------------------------
  // Non-logical
  //--------------------------------------------------------------

  // To add...

  //--------------------------------------------------------------
  // First order connectives and related.
  //--------------------------------------------------------------
  qi::rule<Iter, string()>
   fof_quantifier =
     ascii::string("!")
     | ascii::string("?");
  qi::rule<Iter, string()>
    nonassoc_connective =
     ascii::string("<=>")
     | ascii::string("=>")
     | ascii::string("<=")
     | ascii::string("<~>")
     | lexeme[ ascii::string("~") >> vline ]
     | ascii::string("~&");
  qi::rule<Iter, string()>
    assoc_connective =
     vline
     | ascii::string("&");
  qi::rule<Iter, string()>
    unary_connective =
     ascii::string("~");
  //--------------------------------------------------------------
  // Include...
  //
  // This is part of the top-most definition for TPTP_input.
  // As a file is either one of these or an annotated_formula
  // this needs a semantic action to collect includes together.
  // This is covered by the function class, which will
  // add an include to file_includes each time it is called.
  //--------------------------------------------------------------
  template<typename It>
  struct include_grammar
  : qi::grammar<It, vector<string>(), ascii::space_type>
  {
      include_grammar()
      : include_grammar::base_type(include) {
          space_name %= name;
          name_list %=
              name % ',';
          formula_selection %=
              ('[' >> name_list >> ']')
              | star;
          include_optionals %=
              (',' >> formula_selection)
              | (',' >> formula_selection >> ',' >> space_name)
              | null;
          include %=
              lit("include")
              >> '(' >> file_name >> include_optionals >> ')'
              >> '.';
      }
      qi::rule<Iter, string(), ascii::space_type> space_name;
      qi::rule<Iter, vector<string>(), ascii::space_type> name_list;
      qi::rule<Iter, vector<string>(), ascii::space_type> formula_selection;
      qi::rule<Iter, vector<string>(), ascii::space_type> include_optionals;
      qi::rule<Iter, vector<string>(), ascii::space_type> include;
  };
  //--------------------------------------------------------------
  // Now I need a grammar and some related stuff to handle
  // literals. This was originally based pretty closely on the XML
  // example in the boost documentation, but it's grown a lot
  // since then. It ends up being pretty convoluted, but ultimately
  // you're just getting P(x, f(y),...) and similar.
  //
  // Note that it would obviously be dangerous to have a variable
  // and a constant with the same name...
  //--------------------------------------------------------------
  // fof_term
  //
  // There are a couple of places in what follows where a definition
  // is repeated, and the copies should match. This is clearly
  // not ideal. However the TPTP definition is highly self-referential,
  // and this is the closest I can get to keeping it to
  // a nicely separated bunch of structs that are nice to
  // work with.
  //--------------------------------------------------------------
  template<typename It>
  struct fof_term_grammar
  : qi::grammar<It, fof_arguments_struct(), ascii::space_type>
  {
      fof_term_grammar()
      : fof_term_grammar::base_type(fof_term) {

        fof_term %=
          fof_function_term
          | variable;

        fof_function_term %=
          fof_plain_term
          | fof_defined_term
          | fof_system_term;

        fof_plain_term %=
          // Both in fact atomic_word.
          (constant | functor)
          >> -('(' >> fof_arguments >> ')');

        fof_defined_term %=
          (defined_term [DefinedAdder()] >> attr(vector<fof_arguments_struct>()))
          | fof_defined_atomic_term;

        fof_defined_atomic_term %= fof_defined_plain_term;

        fof_defined_plain_term %=
          // defined_constant = defined_functor.
          (defined_constant | defined_functor) [DefinedAdder()]
          >> -('(' >> fof_arguments >> ')');

        // This also gets defined elsewhere and all definitions should
        // match.
        fof_system_term %=
          // Both in fact dollar_dollar_word.
          (system_constant | system_functor) [SystemAdder()]
          >> -('(' >> fof_arguments >> ')');

        // This also gets defined elsewhere and all definitions should
        // match.
        fof_arguments %= fof_term % ',';
      }
      qi::rule<It, fof_arguments_struct(), ascii::space_type>
      fof_term;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_function_term;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_plain_term;
      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_defined_term;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_defined_atomic_term;
      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_defined_plain_term;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_system_term;

      qi::rule<It, vector<fof_arguments_struct>(), ascii::space_type>
      fof_arguments;
  };
  //--------------------------------------------------------------
  // fof_defined_infix_formula
  //--------------------------------------------------------------
  template<typename It>
  struct fof_defined_infix_formula_grammar
  : qi::grammar<It, infix_struct(), ascii::space_type>
  {
      fof_defined_infix_formula_grammar()
      : fof_defined_infix_formula_grammar::base_type(fof_defined_infix_formula) {

        fof_defined_infix_formula %=
          fof_term >> defined_infix_pred >> fof_term;
      }

    fof_term_grammar<It> fof_term;

    qi::rule<It, infix_struct(), ascii::space_type>
    fof_defined_infix_formula;
  };
  //--------------------------------------------------------------
  // fof_infix_unary
  //--------------------------------------------------------------
  template<typename It>
  struct fof_infix_unary_grammar
  : qi::grammar<It, infix_struct(), ascii::space_type>
  {
      fof_infix_unary_grammar()
      : fof_infix_unary_grammar::base_type(fof_infix_unary) {

        fof_infix_unary %=
          fof_term >> infix_inequality >> fof_term
          // Desperate measures! Should apparently not be needed 
          // but there are very rare occasions when you want to 
          // parse something like a(b) = c(d) and it is! See 
          // TPTP SET007+6.ax, t1_zfmisc_1.
          | fof_term >> defined_infix_pred >> fof_term; 
      }

    fof_term_grammar<It> fof_term;

    qi::rule<It, infix_struct(), ascii::space_type>
    fof_infix_unary;
  };
  //--------------------------------------------------------------
  // fof_atomic_formula
  //--------------------------------------------------------------
  template<typename It>
  struct fof_atomic_formula_grammar
  : qi::grammar<It, fof_atomic_formula_type(), ascii::space_type>
  {
      fof_atomic_formula_grammar()
      : fof_atomic_formula_grammar::base_type(fof_atomic_formula) {

        // Types are slightly out of line here, but seems
        // fine.
        fof_atomic_formula %=
          fof_plain_atomic_formula
          | fof_defined_atomic_formula
          | fof_system_atomic_formula;

        fof_plain_atomic_formula %=
          // proposition = predicate
          ( proposition | predicate )
              >> -('(' >> fof_arguments >> ')');

        fof_defined_atomic_formula %=
          fof_defined_plain_formula
          | fof_defined_infix_formula;

        fof_system_atomic_formula %=
          fof_system_term;

        fof_defined_plain_formula %=
          // Slightly odd as it allows $true or $false to have parameters!
          (defined_proposition | defined_predicate)
          >> -('(' >> fof_arguments >> ')');

        // This also gets defined elsewhere and all definitions should
        // match.
        fof_system_term %=
          // Both in fact dollar_dollar_word.
          (system_constant | system_functor) [SystemAdder()]
          >> -('(' >> fof_arguments >> ')');

        // This also gets defined elsewhere and all definitions should
        // match.
        fof_arguments %= fof_term % ',';
      }
      fof_defined_infix_formula_grammar<It> fof_defined_infix_formula;
      fof_infix_unary_grammar<It> fof_infix_unary;
      fof_term_grammar<It> fof_term;

      qi::rule<It, fof_atomic_formula_type(), ascii::space_type>
      fof_atomic_formula;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_plain_atomic_formula;
      qi::rule<It, fof_atomic_formula_type(), ascii::space_type>
      fof_defined_atomic_formula;
      qi::rule<It, fof_atomic_formula_type(), ascii::space_type>
      fof_system_atomic_formula;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_defined_plain_formula;

      qi::rule<It, fof_plain_term_struct(), ascii::space_type>
      fof_system_term;

      qi::rule<It, vector<fof_arguments_struct>(), ascii::space_type>
      fof_arguments;
  };
  //--------------------------------------------------------------
  // literal
  //--------------------------------------------------------------
  template<typename It>
  struct literal_grammar
  : qi::grammar<It, fof_atomic_formula_type(), ascii::space_type>
  {
      literal_grammar()
      : literal_grammar::base_type(literal) {
          /*
          * NOTE: the line for fof_defined_infix_formula should not be here
          * according to the syntax. However for reasons that are not clear
          * f(X) = ... does not get parsed if it's left out. (X = ... is just
          * fine.) The syntax treats ... = ... differently from ... != ... 
          * with the former being handled by fof_atomic_formula.
          *
          * NOTE 2: I wonder what the intended behaviour is for
          * - X = Y .
          *
          * NOTE 3: In the TPTP definition fof_infix_unary comes last,
          * however that causes problems with f(X) != ...
          * I think all that is happening here is that the f(X) gets
          * parsed as an atomic formula if you use the definition
          * exactly.
          */
          // Types are slightly out of line here, but seems
          // fine.
          literal %=
            fof_defined_infix_formula [to_lit()]
            | fof_infix_unary [to_lit()]
            | (eps[unset_neg_lit()] >> fof_atomic_formula) [to_lit()]
            | (lit('~') >> eps[set_neg_lit()] >> fof_atomic_formula) [to_lit()];
      }
      fof_defined_infix_formula_grammar<It> fof_defined_infix_formula;
      fof_infix_unary_grammar<It> fof_infix_unary;
      fof_atomic_formula_grammar<It> fof_atomic_formula;

      qi::rule<It, fof_atomic_formula_type(), ascii::space_type>
      literal;
  };
  //--------------------------------------------------------------
  // Grammar for cnf_formula.
  //--------------------------------------------------------------
  template<typename It>
  struct cnf_formula_grammar
  : qi::grammar<It, vector<fof_atomic_formula_type>(), ascii::space_type>
  {
      cnf_formula_grammar()
      : cnf_formula_grammar::base_type(cnf_formula) {
          disjunction %=
              literal % vline;
          cnf_formula %=
              (disjunction
            | '(' >> disjunction >> ')');
      }
      literal_grammar<It> literal;

      // Grammar for cnf formulas.
      qi::rule<It, vector<fof_atomic_formula_type>(), ascii::space_type>
      disjunction;
      qi::rule<It, vector<fof_atomic_formula_type>(), ascii::space_type>
      cnf_formula;
  };
  //--------------------------------------------------------------
  // Grammar for fof_formula.
  //--------------------------------------------------------------
  template<typename It>
  struct fof_formula_grammar
  : qi::grammar<It, fof_formula_type(),
                ascii::space_type>
  {
      fof_formula_grammar()
      : fof_formula_grammar::base_type(fof_formula) {

        fof_binary_formula %=
          fof_binary_nonassoc
          | fof_binary_assoc;

        fof_binary_nonassoc %=
          (fof_unit_formula >> nonassoc_connective >> fof_unit_formula);

        fof_binary_assoc %=
          fof_or_formula
          | fof_and_formula;

        fof_or_formula %=
          fof_unit_formula >> vline >> (fof_unit_formula % '|');

        fof_and_formula %=
          fof_unit_formula >> ascii::string("&") >> (fof_unit_formula % '&');

        fof_quantified_formula %=
          fof_quantifier
          >> '[' >> fof_variable_list >> ']'
          >> ':' >> fof_unit_formula;

        fof_variable_list %=
          variable % ',';

        fof_unitary_formula %=
          fof_quantified_formula
          | fof_atomic_formula
          | ('(' >> fof_logic_formula >> ')');

        fof_unary_formula %=
          (unary_connective >> fof_unit_formula)
          | fof_infix_unary;

        // Similar issue here as with the literal grammar. I think
        // you need to be very careful with the TPTP definition and the 
        // distinction between terms and atomic formulas, f(X) = ... 
        // and f(X) != ... fail because the f(X) gets parsed as the latter in
        // fof_unitary_formula. I have added fof_defined_infix_formula
        // and fof_infix_unary here to fix that.
        fof_unit_formula %=
          fof_defined_infix_formula
          | fof_infix_unary
          | fof_unitary_formula
          | fof_unary_formula;

        fof_logic_formula %=
          fof_binary_formula
          | fof_unary_formula
          | fof_unitary_formula;

        fof_formula %=
          fof_logic_formula [make_fof_formula()];
      }
      fof_defined_infix_formula_grammar<It> fof_defined_infix_formula;
      fof_infix_unary_grammar<It> fof_infix_unary;
      fof_atomic_formula_grammar<It> fof_atomic_formula;

      qi::rule<It, fof_binary_struct(),
        ascii::space_type> fof_binary_nonassoc;
      qi::rule<It, fof_andor_struct(),
        ascii::space_type> fof_binary_assoc;

      qi::rule<It, vector<string>(),
        ascii::space_type> fof_variable_list;

      qi::rule<It, fof_quantifier_struct(),
        ascii::space_type> fof_quantified_formula;
      qi::rule<It, fof_andor_struct(),
        ascii::space_type> fof_or_formula;
      qi::rule<It, fof_andor_struct(),
        ascii::space_type> fof_and_formula;

      qi::rule<It, fof_formula_type(),
        ascii::space_type> fof_binary_formula;
      qi::rule<It, fof_formula_type(),
        ascii::space_type> fof_unit_formula;
      qi::rule<It, fof_formula_type(),
        ascii::space_type> fof_unary_formula;
      qi::rule<It, fof_formula_type(),
        ascii::space_type> fof_unitary_formula;

      qi::rule<It, fof_formula_type(),
        ascii::space_type> fof_logic_formula;

      qi::rule<It, fof_formula_type(), ascii::space_type>
      fof_formula;
  };
  //--------------------------------------------------------------
  // Grammar for cnf_annotated.
  //--------------------------------------------------------------
  template<typename It>
  struct cnf_annotated_grammar
  : qi::grammar<It, ascii::space_type>
  {
      cnf_annotated_grammar()
      : cnf_annotated_grammar::base_type(cnf_annotated) {
          cnf_annotated =
              lit("cnf")
              >> lit('(')
              >> name [print_cnf_formula_name()]
              >> lit(',')
              >> formula_role [print_cnf_formula_role()]
              >> lit(',')
              >> cnf_formula [add_current_clause()]
              >> lit(')')
              >> lit('.');
      }
      cnf_formula_grammar<It> cnf_formula;

      qi::rule<It, ascii::space_type>
      cnf_annotated;
  };
  //--------------------------------------------------------------
  // Grammar for fof_annotated.
  //--------------------------------------------------------------
  template<typename It>
  struct fof_annotated_grammar
  : qi::grammar<It, ascii::space_type>
  {
      fof_annotated_grammar()
      : fof_annotated_grammar::base_type(fof_annotated) {
          fof_annotated =
              lit("fof")
              >> lit('(')
              >> name [print_fof_formula_name()]
              >> lit(',')
              >> formula_role [print_fof_formula_role()]
              >> lit(',')
              >> fof_formula [add_fof_formula()] 
              >> lit(')')
              >> lit('.');
      }
      fof_formula_grammar<It> fof_formula;

      qi::rule<It, ascii::space_type>
      fof_annotated;
  };
  //--------------------------------------------------------------
  // Grammar for TPTP_file.
  //--------------------------------------------------------------
  template<typename It>
  struct TPTP_file_grammar
  : qi::grammar<It, ascii::space_type>
  {
      TPTP_file_grammar()
      : TPTP_file_grammar::base_type(TPTP_file) {
          annotated_formula =
              fof_annotated | cnf_annotated;
          TPTP_input =
              annotated_formula
            | comment_line       // Not in TPTP definition but needed anyway.
            | include [FileIncludeAdder()];
          TPTP_file =
              *TPTP_input;

      }
      cnf_annotated_grammar<It> cnf_annotated;
      fof_annotated_grammar<It> fof_annotated;
      include_grammar<It> include;

      qi::rule<It, ascii::space_type>
      annotated_formula;
      qi::rule<It, ascii::space_type> TPTP_input;
      qi::rule<It, ascii::space_type> TPTP_file;
  };
  //--------------------------------------------------------------
  // Implementation of print functions for debugging.
  //
  // Only one print function has to be here.
  //--------------------------------------------------------------
  void show_fof_plain_term::operator()
    (const fof_plain_term_struct& pt) {
      cout << pt.functor;
      size_t s = pt.args.size();
      if (s > 0) {
          cout << '(';
          show_fof_arguments sfa;
          for (const fof_arguments_struct& as : pt.args) {
              boost::apply_visitor(sfa, as);
              s--;
              if (s>0) cout << ", ";
          }
          cout << ')';
      }
  }
  //--------------------------------------------------------------
  // Simple semantic actions.
  //--------------------------------------------------------------
  void FileIncludeAdder::operator()(const vector<string>& inc,
                                      qi::unused_type,
                                      qi::unused_type) const {
      FileIncludeItem item;
      item.first = inc[0];
      vector<string> inc2 = inc;
      inc2.erase(inc2.begin());
      item.second = inc2;
      file_includes.push_back(item);
      // This line does the actual inclusion.
      recursive_tptp_include(item);
  }
  //--------------------------------------------------------------
  void CommentStatus::operator()(const string& s,
                    qi::unused_type,
                    qi::unused_type) const {
    if (is_first_status) {
      status = s;
      is_first_status = false;
    }
  }
  //--------------------------------------------------------------
  void DefinedAdder::operator()(const string& s,
                    qi::unused_type,
                    qi::unused_type) const {
      all_defined.push_back(s);
      string message("Found defined item: ");
      message += s;
      if (params::verbosity > 2)
        cout << message << endl;
  }
  //--------------------------------------------------------------
  void SystemAdder::operator()(const string& s,
                    qi::unused_type,
                    qi::unused_type) const {
      all_system.push_back(s);
      string message("Found system item: ");
      message += s;
      if (params::verbosity > 2)
        cout << message << endl;
  }
  //--------------------------------------------------------------
  void DistinctAdder::operator()(const string& s,
                    qi::unused_type,
                    qi::unused_type) const {
      distinct_objects.insert(s);
      string message("Found distinct object: ");
      message += s;
      if (params::verbosity > 2)
        cout << message << endl;
  }
  //--------------------------------------------------------------
  // More complex semantic actions.
  //
  // These are for the literal grammar.
  //--------------------------------------------------------------
  void to_lit::operator()(const fof_atomic_formula_type& f,
    qi::unused_type,
    qi::unused_type) const {
      current_lit =
        boost::apply_visitor(convert_fof_atomic_formula(), f);
      current_clause.add_lit(current_lit);
#ifdef DEBUGOUTPUT
      cout << current_lit << endl;
#endif
  }
  //--------------------------------------------------------------
  void show_lit::operator()(const fof_atomic_formula_type& f,
    qi::unused_type,
    qi::unused_type) const {
      Literal lit_to_show =
        boost::apply_visitor(convert_fof_atomic_formula(), f);
      cout << lit_to_show.to_string() << endl;
  }
  //--------------------------------------------------------------
  void set_neg_lit::operator()(qi::unused_type,
    qi::unused_type,
    qi::unused_type) const {
      neg_lit = true;
    }
  //--------------------------------------------------------------
  void unset_neg_lit::operator()(qi::unused_type,
    qi::unused_type,
    qi::unused_type) const {
      neg_lit = false;
    }
  //--------------------------------------------------------------
  void clear_current_clause::operator()(qi::unused_type,
    qi::unused_type,
    qi::unused_type) const {
      current_clause.clear();
    }
  //--------------------------------------------------------------
  void add_current_clause::operator()(qi::unused_type,
    qi::unused_type,
    qi::unused_type) const {
      if (include_this_item) {
        all_clauses.push_back(current_clause);
        clause_roles.push_back(current_clause_role);
        if (current_clause_role == string("negated_conjecture"))
          negated_conjecture_found = true;
      }
      current_clause.clear();
      current_clause_role = "";
  }
  //--------------------------------------------------------------
  // More complex semantic actions.
  //
  // Functions etc to make a literal.
  //--------------------------------------------------------------
  Term* convert_fof_arguments_struct::operator()
  (const string& s) const {
  // The only rule that makes a variable is fof_term, and that's the
  // only thing that produces an fof_arguments_struct. So if there is
  // a string here then it must be a variable.
    Variable* new_var = var_index_p->add_named_var(s);
    return t_index_p->add_variable_term(new_var);
  }
  //--------------------------------------------------------------
  Term* convert_fof_arguments_struct::operator()
  (const fof_plain_term_struct& t) const {
  // See comment for companion function: this must be a function.
    Arity arity = t.args.size();
    vector<Term*> args;
    for (size_t i = 0; i < arity; i++) {
      Term* new_t =
        boost::apply_visitor(convert_fof_arguments_struct(),
                              t.args[i]);
      args.push_back(new_t);
    }
    Function* f = fun_index_p->add_function(t.functor, arity);
    return t_index_p->add_function_term(f, args);
  }
  //--------------------------------------------------------------
  Literal convert_fof_atomic_formula::operator()
    (const fof_plain_term_struct& f) const {
    Literal result;
    size_t arity = f.args.size();
    Predicate* new_P =
      p_index_p->add_predicate(f.functor, arity);
    vector<Term*> args;
    for (size_t i = 0; i < arity; i++) {
      Term* new_t =
        boost::apply_visitor(convert_fof_arguments_struct(),
                              f.args[i]);
      args.push_back(new_t);
    }
    // neg_lit is set by a semantic action.
    return Literal(new_P, args, arity, !neg_lit);
  }
  //--------------------------------------------------------------
  Literal convert_fof_atomic_formula::operator()
    (const infix_struct& f) const {
    size_t arity = 2;
    if (!equals_added) {
      equals_added = true;
      equals_p = p_index_p->add_predicate("=", arity);
    }
    bool polarity = true;
    if (f.connective == "!=")
      polarity = false;
      vector<Term*> args;
      Term* new_t =
        boost::apply_visitor(convert_fof_arguments_struct(),
                              f.left);
      args.push_back(new_t);
      new_t =
        boost::apply_visitor(convert_fof_arguments_struct(),
                              f.right);
      args.push_back(new_t);
      return Literal(equals_p, args, arity, polarity);
  }
  //--------------------------------------------------------------
  // Semantic actions for cnf_formula.
  //--------------------------------------------------------------
  void print_cnf_formula_name::operator()(const string& s,
      qi::unused_type,
      qi::unused_type) const {
#ifdef DEBUGOUTPUT
          cout << "Found cnf formula: "
            << s;
#endif
        include_this_item = false;
        if (to_include.empty()) {
          include_this_item = true;
          return;
        }
        auto i = to_include.find(s);
        if (i != to_include.end()) {
          include_this_item = true;
          return;
        }
        return;
  }
  //--------------------------------------------------------------
  void print_cnf_formula_role::operator()(const string& s,
      qi::unused_type,
      qi::unused_type) const {
        current_clause_role = s;
#ifdef DEBUGOUTPUT
        cout << " ("
          << s
          << ")" << endl;
#endif
  }
  //--------------------------------------------------------------
  // Semantic actions for fof_formula.
  //--------------------------------------------------------------
  void print_fof_formula_name::operator()(const string& s,
      qi::unused_type,
      qi::unused_type) const {
        current_formula_name = s;
  #ifdef DEBUGOUTPUT
          cout << "Found fof formula: "
            << s;
  #endif
        include_this_item = false;
        if (to_include.empty()) {
          include_this_item = true;
          return;
        }
        auto i = to_include.find(s);
        if (i != to_include.end()) {
          include_this_item = true;
          return;
        }
        return;
  }
  //--------------------------------------------------------------
  void print_fof_formula_role::operator()(const string& s,
      qi::unused_type,
      qi::unused_type) const {
        current_formula_role = s;
  #ifdef DEBUGOUTPUT
        cout << " ("
          << s
          << ")" << endl;
  #endif
  }
  //--------------------------------------------------------------
  // More complex semantic actions for FOF formulas.
  //
  // Functions etc to make a FOF formula.
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const fof_plain_term_struct& f) const {
    size_t arity = f.args.size();
    Predicate* new_P =
      p_index_p->add_predicate(f.functor, arity);
    vector<Term*> args;
    for (size_t i = 0; i < arity; i++) {
      Term* new_t =
        boost::apply_visitor(convert_fof_arguments_struct(),
                              f.args[i]);
      args.push_back(new_t);
    }
    Literal lit(new_P, args, arity, true);
    FOF result(lit);
    return result;
  }
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const infix_struct& f) const {
    size_t arity = 2;
    if (!equals_added) {
      equals_added = true;
      equals_p = p_index_p->add_predicate("=", arity);
    }
    bool polarity = true;
    if (f.connective == "!=")
      polarity = false;

    vector<Term*> args;
    Term* new_t =
      boost::apply_visitor(convert_fof_arguments_struct(),
                              f.left);
    args.push_back(new_t);
    new_t =
        boost::apply_visitor(convert_fof_arguments_struct(),
                              f.right);
    args.push_back(new_t);
    Literal lit(equals_p, args, arity, polarity);
    FOF result(lit);
    return result;
  }
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const fof_unitary_formula_struct& f) const {
    FOF result =  boost::apply_visitor(convert_fof_formula(), f.arg);
    return result;
  }
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const fof_negation_struct& f) const {
    FOF sub = boost::apply_visitor(convert_fof_formula(), f.arg);
    vector<FOF> subs;
    subs.push_back(sub);
    FOF result(FOFType::Neg, subs, nullptr);
    return result;
  }
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const fof_quantifier_struct& f) const {
    FOF sub = boost::apply_visitor(convert_fof_formula(), f.arg);
    size_t n = f.vars.size();
    vector<FOF> subs;
    subs.push_back(sub);
    FOF temp(FOFType::Empty);
    if (f.type == "!") {
      for (int i = n - 1; i >= 0; i--) {
        Variable* var = var_index_p->add_named_var(f.vars[i]);
        temp = FOF(FOFType::A, subs, var);
        subs.clear();
        subs.push_back(temp);
      }
      return temp;
    }
    if (f.type == "?") {
      for (int i = n - 1; i >= 0; i--) {
        Variable* var = var_index_p->add_named_var(f.vars[i]);
        temp = FOF(FOFType::E, subs, var);
        subs.clear();
        subs.push_back(temp);
      }
      return temp;
    }
    cerr << "You have an unsupported fof_quantifier_struct." << endl;
    return FOF(FOFType::Empty);
  }
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const fof_binary_struct& f) const {
    FOF lhs = boost::apply_visitor(convert_fof_formula(), f.lhs);
    FOF rhs = boost::apply_visitor(convert_fof_formula(), f.rhs);
    vector<FOF> subs;
    FOF result(FOFType::Empty);
    if (f.type == "<=") {
      subs.push_back(rhs);
      subs.push_back(lhs);
      result = FOF(FOFType::Imp, subs, nullptr);
      return result;
    }
    subs.push_back(lhs);
    subs.push_back(rhs);
    if (f.type == "=>") {
      result = FOF(FOFType::Imp, subs, nullptr);
      return result;
    }
    if (f.type == "<=>") {
      result = FOF(FOFType::Iff, subs, nullptr);
      return result;
    }
    if (f.type == "<~>") {
      FOF not_lhs = lhs;
      not_lhs.negate();
      FOF not_rhs = rhs;
      not_rhs.negate();
      vector<FOF> new_subs_1;
      new_subs_1.push_back(lhs);
      new_subs_1.push_back(not_rhs);
      vector<FOF> new_subs_2;
      new_subs_2.push_back(not_lhs);
      new_subs_2.push_back(rhs);
      FOF new_lhs(FOFType::And, new_subs_1, nullptr);
      FOF new_rhs(FOFType::And, new_subs_2, nullptr);
      subs.clear();
      subs.push_back(new_lhs);
      subs.push_back(new_rhs);
      result = FOF(FOFType::Or, subs, nullptr);
      return result;
    }
    if (f.type == "~|") {
      result = FOF(FOFType::Or, subs, nullptr);
      result.negate();
      return result;
    }
    if (f.type == "~&") {
      result = FOF(FOFType::And, subs, nullptr);
      result.negate();
      return result;
    }
    cerr << "You have an unsupported fof_binary_struct." << endl;
    return result;
  }
  //--------------------------------------------------------------
  FOF convert_fof_formula::operator()(const fof_andor_struct& f) const {
    FOF result(FOFType::Empty);
    FOF lhs = boost::apply_visitor(convert_fof_formula(), f.lhs);
    vector<FOF> rhs;
    size_t n = f.rhs.size();
    for (size_t i = 0; i < n; i++) {
      FOF sub = boost::apply_visitor(convert_fof_formula(), f.rhs[i]);
      rhs.push_back(sub);
    }
    rhs.insert(rhs.begin(), lhs);
    if (f.type == "&") {
      result = FOF(FOFType::And, rhs, nullptr);
      return result;
    }
    if (f.type == "|") {
      result = FOF(FOFType::Or, rhs, nullptr);
      return result;
    }
    cerr << "You have an unsupported fof_andor_struct." << endl;
    return result;
  }
  //--------------------------------------------------------------
  void make_fof_formula::operator()(const fof_formula_type& f,
                    qi::unused_type,  qi::unused_type) const {
    current_formula =
        boost::apply_visitor(convert_fof_formula(), f);
  }
  //--------------------------------------------------------------
  void add_fof_formula::operator()(qi::unused_type,
                    qi::unused_type,  qi::unused_type) const {
    if (include_this_item) {
      all_formulas.push_back(current_formula);
      formula_roles.push_back(current_formula_role);
      formula_names.push_back(current_formula_name);
      if (current_formula_role == string("conjecture"))
          conjecture_found = true;
#ifdef DEBUGOUTPUT
      cout << current_formula.to_string() << endl;
#endif
    }
    current_formula_role = "";
  }
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
// Implementation of the TPTPParser class.
//---------------------------------------------------------------------
TPTPParser::TPTPParser(
  VariableIndex* new_vip,
  FunctionIndex* new_fip,
  TermIndex* new_tip,
  PredicateIndex* new_pip,
  Matrix* new_matrix
)
:
file_contents(),
comment_blocks(),
vip(new_vip),
fip(new_fip),
tip(new_tip),
pip(new_pip),
matrix(new_matrix) {
  // var_index_p is global in the tptp_parser namespace. It is
  // used by semantic actions.
  var_index_p = new_vip;
  // Similar for fun_index_p and so on...
  fun_index_p = new_fip;
  t_index_p = new_tip;
  p_index_p = new_pip;
  // And remember that FOF also needs to use the indices.
  FOF::set_indexes(std::tuple<VariableIndex*, FunctionIndex*, PredicateIndex*, TermIndex*>
    (new_vip, new_fip, new_pip, new_tip));
  clear();
  tptp_conversion_string = "";
};
//--------------------------------------------------------------
void TPTPParser::read_tptp_from_file(const string& file_name) {
    // Used to collect up comments as you see them.
    string comment;
    bool in_comment = false;
    
    char c;

    ifstream file;
    file.unsetf(std::ios_base::skipws);
    file.open(file_name);
    if (file.fail()) {
      throw (file_open_exception(file_name));
    }
    file.get(c);
    while (file.good()) {
        // Detect the start of a comment.
        if (!in_comment && c == '/') {
            if (file.peek() == '*') {
                file.get(c);
                in_comment = true;
                comment.clear();
            }
            else file_contents += c;
        }
        // Detect the end of a comment.
        else if (in_comment && c == '*') {
            if (file.peek() == '/') {
                file.get(c);
                in_comment = false;
                comment_blocks.push_back(comment);
            }
            else comment += c;
        }
        // Nothings to see. We're just adding to the
        // relevant output.
        else if (in_comment)
             comment += c;
        else
            file_contents += c;
        file.get(c);
    }
    file.close();
}
//--------------------------------------------------------------
bool TPTPParser::parse_tptp_from_file(const string& file_name) {
    /*
    * Let the parser do the heavy-lifting: get stuff from the 
    * TPTP file and parse it.
    */
    read_tptp_from_file(file_name);

    Iter start = file_contents.begin();
    Iter end = file_contents.end();

    include_file_path = params::full_problem_path;
    
    TPTP_file_grammar<Iter> g;
    bool result = qi::phrase_parse(start, end, g, ascii::space);

    if (start != end || !result) 
      throw (file_parse_exception(file_name));
    /*
    * If you get to here, then the parser has read everything and set 
    * up a whole bunch of stuff for you. In particular, all_clauses and 
    * all_formulas have the juicy stuff.
    *
    * However, what follows gets stupidly complicated because you 
    * have to deal with a lot of rare special cases. :-(
    */
    if (pip->true_false_added() && params::verbosity > 1) 
      cout << "Found true/false." << endl;
    /*
    * First, deal with cnf(...). entries. There's not much to 
    * do as simplification can happen later.
    */
    if (negated_conjecture_found && params::verbosity > 1) 
      cout << "Found negated conjecture." << endl;
    /* 
    * Now do clause conversion for the fof(...). entries.
    *
    * Remember: negate the conjecture if necessary.
    */
    if (conjecture_found && params::verbosity > 1 && params::first_parse) 
      cout << "Found conjecture." << endl;
    /*
    * Were there and first_order items, or is it just CNF?
    */
    cnf_only = (all_formulas.size() == 0);
    if (cnf_only && params::verbosity > 1) 
      cout << "The problem is CNF only." << endl;
    /*
    * First do a check for general oddness.
    */
    if (negated_conjecture_found && conjecture_found) {
        cout << "% SZS status Error for " 
             << params::problem_name 
             << " : conjecture and negated conjecture found in the same problem." << endl;
        exit(EXIT_FAILURE);
    }
    if (!negated_conjecture_found && !conjecture_found && params::verbosity > 1) {
      cout << "No conjecture or negated conjecture found." << endl;
    } 
    if (negated_conjecture_found && all_formulas.size() > 0 && params::verbosity > 1) {
      cout << "% SZS status Error for " 
           << params::problem_name 
           << " : negated conjecture found in FOF problem." << endl;
      exit(EXIT_FAILURE);
    } 
    /*
    * Now we can convert some formulas to clauses.
    *
    * Remember: different things need to happen here depending on the state 
    * of params::no_definitional and params::all_definitional.
    */
    if (params::no_definitional && params::all_definitional) {
        cout << "% SZS status Error for " 
             << params::problem_name 
             << " : --all-definitional and --no-definitional have both been set." << endl;
        exit(EXIT_FAILURE);
    }
    /*
    * Later on I'll need to know whether the original (FOF) problem 
    * actually had axioms.
    */
    has_axioms = (all_clauses.size() > 0); 
    if (!has_axioms) {
      for (const string& s : formula_roles) {
        if (s != "conjecture") {
          has_axioms = true;
          break;
        }
      }
    }
    /*
    * Do the conversion to clauses and store the results. 
    * Don't simplify yet.
    */   
    vector<vector<Clause>> all_fof_clauses;
    bool found_one_conjecture = false;
    vector<bool> definitional_conversion;
    size_t i = 0;
    size_t conjecture_index = 0;
    for (FOF f : all_formulas) {
       vector<Clause> vc;
       if (formula_roles[i] == string("conjecture")) {
            conjecture_index = i;
            if (found_one_conjecture) {
              cout << "% SZS status Error for " 
              << params::problem_name 
              << " : more than one conjecture in the input file." << endl;
              exit(EXIT_FAILURE);
            }
            else {
              found_one_conjecture = true;
            }
            // This is rather important!
            f.negate(); 
            if (!params::no_definitional) {
                f.definitional_convert_to_cnf_clauses(vc);
                definitional_conversion.push_back(true);
            }
            else {
                f.convert_to_cnf_clauses(vc);
                definitional_conversion.push_back(false);
            }
            number_of_negated_conjecture_clauses = vc.size();
       } 
       else {
            if (params::all_definitional || !conjecture_found) {
                f.definitional_convert_to_cnf_clauses(vc);
                definitional_conversion.push_back(true);
            }
            else {
                 f.convert_to_cnf_clauses(vc);
                 definitional_conversion.push_back(false);
            }
       }
       all_fof_clauses.push_back(vc);
       i++;
    }
    /*
    * Now all_fof_clauses has unsimplified clauses, as
    * does all_clauses. We also know where any conjecture 
    * is.
    *
    * Before doing anything else, it might be that all we 
    * want is to see the clause conversion.
    */
    i = 0;
    if (params::show_clauses) {
      for (vector<Clause>& vc : all_fof_clauses) {
        cout << "---------------------" << endl;
        cout << "Formula: " << formula_names[i] << ", " 
             << formula_roles[i] << endl;
        cout << all_formulas[i] << endl;
        cout << "Clauses:";
        if (definitional_conversion[i]) {
          cout << " (definitional conversion)";
        } 
        cout << endl;
        FOF::simplify_cnf(vc);
        for (const Clause& c : vc) {
          cout << c << endl;
        } 
        i++;
      }
      exit(EXIT_SUCCESS);
    }
    /*
    * OK - so we've got more to do. Now simplify everything, 
    * but keep track of any strange cases.
    *
    * Start with the case when the problem is CNF only.
    */
    SimplificationResult cnf_result = FOF::simplify_cnf(all_clauses, clause_roles);
    /* 
    * Did we somehow manage to delete all the negated conjectures?
    */
    for (const string& s : clause_roles) {
      if (s == string("negated_conjecture")) {
        negated_conjecture_exists = true;
        break;
      }
    }
    string output_string; 
    vector<Clause> simplified_fof_clauses;
    vector<string> simplified_fof_roles;
    /*
    * Note that we can draw the following conclusions regardless of whether 
    * or not any equality axioms have been added.
    */
    if (all_formulas.size() == 0) {
        if (cnf_result == SimplificationResult::Tautology) {
          output_string = "Satisfiable";
        }
        if (cnf_result == SimplificationResult::Contradiction) {
          output_string = "Unsatisfiable";
        }
        if (output_string != "") {
          cout << "% SZS status " << output_string << " for " 
               << params::problem_name 
               << " : established by clause simplification." << endl;
          std::exit(EXIT_SUCCESS);
        }
    }
    // Here, we know it's a problem with FOF stuff in it.
    else {
      i = 0;
      for (vector<Clause> cs : all_fof_clauses) {
        SimplificationResult fof_result = FOF::simplify_cnf(cs);

        if (i == conjecture_index && conjecture_found) {
          number_of_simplified_negated_conjecture_clauses = cs.size();
        }

        if (params::generate_tptp_proof) {
          tptp_conversion_string += "\n% Formula: ";
          tptp_conversion_string += formula_names[i];
          tptp_conversion_string += " ( ";
          tptp_conversion_string += formula_roles[i];
          tptp_conversion_string += " ) ";
          if (definitional_conversion[i]) {
            tptp_conversion_string +=  "(definitionally) ";
          } 
          tptp_conversion_string += "converted to clauses:\n";
        }

        if (fof_result == SimplificationResult::Tautology) {
          if (i == conjecture_index && conjecture_found) {
            conjecture_false = true;
            if (params::verbosity > 1) {
              cout << "The conjecture is equivalent to $false." << endl;
            }
          }
          else {
            found_true_axiom = true; 
            if (params::verbosity > 1) {
              cout << "Axiom is equivalent to $true." << endl;
            }
          }
          if (params::generate_tptp_proof) {
            tptp_conversion_string += "cnf(";
            tptp_conversion_string += string(formula_names[i]);
            tptp_conversion_string += ", ";
            if (formula_roles[i] == string("conjecture"))
              tptp_conversion_string += "negated_conjecture";
            else 
              tptp_conversion_string += formula_roles[i];
            tptp_conversion_string += ", $true).\n";
          }
          i++;
          continue;
        }
        else if (fof_result == SimplificationResult::Contradiction) {
          if (i == conjecture_index && conjecture_found) {
            conjecture_true = true;
            if (params::verbosity > 1) {
              cout << "The conjecture is equivalent to $true." << endl;
            }
          }
          else {
            found_false_axiom = true;
            if (params::verbosity > 1) {
              cout << "Axiom is equivalent to $false." << endl;
            }
          }
          if (params::generate_tptp_proof) {
            tptp_conversion_string += "cnf(";
            tptp_conversion_string += string(formula_names[i]);
            tptp_conversion_string += ", ";
            if (formula_roles[i] == string("conjecture"))
              tptp_conversion_string += "negated_conjecture";
            else 
              tptp_conversion_string += formula_roles[i];
            tptp_conversion_string += ", $false).\n";
          }
          i++;
          continue;
        }
        else {
          size_t clause_count = 1;
          for (const Clause& c : cs) {
            simplified_fof_clauses.push_back(c);
            simplified_fof_roles.push_back(formula_roles[i]);
            if (params::generate_tptp_proof) {
              tptp_conversion_string += "cnf(";
              tptp_conversion_string += string(formula_names[i]);
              tptp_conversion_string += "-";
              tptp_conversion_string += std::to_string(clause_count);
              tptp_conversion_string += ", ";
              if (formula_roles[i] == string("conjecture"))
                tptp_conversion_string += "negated_conjecture";
              else 
                tptp_conversion_string += formula_roles[i];
              tptp_conversion_string += ", ";
              tptp_conversion_string += c.to_tptp_string();
              tptp_conversion_string += ").";
              tptp_conversion_string += "\n";
            }
            clause_count++;
          }
          i++;
        }
      }
    }
    /*
    * Remember: this actually does some setup work, so don't do it 
    * until *everything* else is in place. In particular, definitional 
    * clause conversion can introduce new predicates, so this has to 
    * happen later.
    */
    matrix->set_num_preds(pip->get_num_preds());

    i = 0;
    for (Clause& c : all_clauses)
      matrix->add_clause(c, clause_roles[i++]);
    /*
    * If it's a CNF only problem we're done! However, if there are FOF 
    * clauses then we have to deal with all the silly possibilities.
    */
    if (all_formulas.size() > 0) {
      /*
      * Now I know about all odd instances where a part of the problem  
      * gave rise to clauses that were equivalent to $true or $false.
      *
      * Does this allow me to stop?
      */
      string output_string;
      if (cnf_result == SimplificationResult::Contradiction || found_false_axiom) {
        if (conjecture_true) {
          output_string = "TautologousConclusionContradictoryAxioms";
        }
        else if (conjecture_false) {
          output_string = "UnsatisfiableConclusionContradictoryAxioms";
        }
        else if (!conjecture_found) {
          output_string = "Unsatisfiable";
        }
        else {
          output_string = "ContradictoryAxioms";
        }
      }
      else {
        /* 
        * The case of something in the axioms being $true just shrinks the 
        * set of axioms. So you need to handle the situation where there 
        * are no axioms remaining!
        */
        has_axioms_remaining = (all_clauses.size() > 0); 
        if (!has_axioms_remaining) {
          for (const string& s : simplified_fof_roles) {
            if (s != "conjecture") {
              has_axioms_remaining = true;
              break;
            }
          }
        }
        if (has_axioms_remaining) {
          /*
          * So: assuming you have some axioms, what happens if the conjecture 
          * was $true or $false?
          *
          * If the conjecture is $false then, as you have axioms, the outcome 
          * still needs to be determined in case the axioms are contradictory.
          */
          if (conjecture_true) {
            output_string = "Theorem";
          }       
          /*
          * We now have just axioms, or axioms with a false conjecture, so 
          * keep going and sort it out later -- 
          */
        }
        /*
        * We have no axioms.
        */
        else {
          if (conjecture_true) {
            output_string = "Theorem";
          }
          if (conjecture_false) {
            output_string = "CounterSatisfiable";
          }
          if (!conjecture_found) {
            output_string = "Theorem";
          }
         /*
         * We now have just a conjecture (or not), so keep going and sort it out 
         * later -- 
         */
        }
      }
      if (output_string != "") {
        cout << "% SZS status " << output_string << " for " 
             << params::problem_name 
             << " : established by clause simplification." << endl;
        exit(EXIT_SUCCESS);
      }
      /*
      * If none of the special cases forced us to stop, then add the 
      * FOF material to the matrix.
      */
      i = 0;
      for (Clause& c : simplified_fof_clauses) {
        matrix->add_clause(c, simplified_fof_roles[i++]);
      }
    }
    return true;
}
//--------------------------------------------------------------
void TPTPParser::show_file_includes() {
    for (FileIncludeItem i : file_includes) {
        cout << "From " << i.first << ": ";
        if (i.second.size() == 0)
            cout << "all";
        else
            for (string s : i.second)
                cout << s << " ";
        cout << endl;
    }
}
//--------------------------------------------------------------
void TPTPParser::clear() {
  equals_added = false;
  conjecture_found = false;
  negated_conjecture_found = false;
  conjecture_true = false;
  conjecture_false = false;
  found_true_axiom = false;
  found_false_axiom = false; 
  negated_conjecture_exists = false;
  has_axioms = false;
  has_axioms_remaining = false;
  cnf_only = false;
  number_of_negated_conjecture_clauses = 0;
  number_of_simplified_negated_conjecture_clauses = 0;
  equals_p = nullptr;
  neg_lit = false;
  is_first_status = true;
  current_clause_role = "";
  current_formula_role = "";
  current_formula_name = "";
  clause_roles.clear();
  formula_roles.clear();
  formula_names.clear();
  file_contents.clear();
  comment_blocks.clear();
  status = "";
  all_defined.clear();
  all_system.clear();
  distinct_objects.clear();
  current_clause.clear();
  current_formula.clear();
  all_formulas.clear();
  all_clauses.clear();
  file_includes.clear();
  to_include.clear();
  include_this_item = true;
  include_file_path = fs::path();
}
//--------------------------------------------------------------
vector<string> TPTPParser::get_defined_items() {
  return all_defined;
}
//--------------------------------------------------------------
vector<string> TPTPParser::get_system_items() {
  return all_system;
}
//--------------------------------------------------------------
bool TPTPParser::equality_used() {
  return equals_added;
}
//--------------------------------------------------------------
size_t TPTPParser::number_of_fof_formulas() const {
  return all_formulas.size();
}
//--------------------------------------------------------------
string TPTPParser::get_problem_status() {
  return status;
}
//--------------------------------------------------------------
Predicate* TPTPParser::get_equals_predicate() const {
  if (equals_added)
    return equals_p;
  else
    return nullptr;
}
//--------------------------------------------------------------
void read_tptp_from_file_simple(const string& file_name, 
          string& file_contents) {
  
    bool in_comment = false;
    char c;

    ifstream file;
    file.unsetf(std::ios_base::skipws);
    file.open(file_name);
    if (file.fail()) {
      throw (file_open_exception(file_name));
    }
    file.get(c);
    while (file.good()) {
        // Detect the start of a comment.
        if (!in_comment && c == '/') {
            if (file.peek() == '*') {
                file.get(c);
                in_comment = true;
            }
            else file_contents += c;
        }
        // Detect the end of a comment.
        else if (in_comment && c == '*') {
            if (file.peek() == '/') {
                file.get(c);
                in_comment = false;
            }
        }
        // Nothings to see. We're just adding to the
        // relevant output.
        else if (!in_comment)
            file_contents += c;
    
        file.get(c);
    }
    file.close();
}
//--------------------------------------------------------------
// One has to be careful with file paths here. The TPTP 
// wants you to treat relative paths as relative to the 
// location of the file that's doing the including, OR, 
// if that doesn't work, relative to the TPTP environment 
// variable.
//--------------------------------------------------------------
void recursive_tptp_include(const FileIncludeItem& include_item) {
  
  verbose_print::VPrint show(params::verbosity);

  // The file to include, as stated in the current TPTP file.
  fs::path file_name(include_item.first);
  fs::path actual_include_path(include_item.first);
  fs::path initial_path(include_file_path);
  // Is it absolute? If so, life is easy!
  if (actual_include_path.is_absolute()) {
    if (!fs::exists(actual_include_path)) {
      cout << "% SZS status Error for " 
           << params::problem_name 
           << " : include file missing."  << endl;
      exit(EXIT_FAILURE);
    }
  }
  // It must be relative - let's try to find it...
  else {
    //...relative to the current file's path...
    file_name = initial_path / actual_include_path;
    if (!fs::exists(file_name)) {
      fs::path tptp(params::tptp_path);
      file_name = tptp / actual_include_path;
      //...or relative to the TPTP path.
      if (!fs::exists(file_name)) {
        cout << "% SZS status Error for " 
             << params::problem_name 
             << " : include file missing."  << endl;
        exit(EXIT_FAILURE);
      }
    }
  }

  // Save the path for the current part of the recursion and 
  // set it to the new path.
  fs::path saved_path = include_file_path;
  include_file_path = file_name;
  include_file_path.remove_filename();

  if (params::first_parse) {
    show(1,string("Including: "));
    show(1,file_name, true);
  }

  // Remember the current include formulas.
  set<string> saved_includes = to_include;

  // This was deleted to take account of the TPTP's slightly 
  // cryptic "...(this filter also applies to formulae that 
  // have been recursively included into the named file)...". 
  // I interpreted this as meaning that you have to pass 
  // the names of things to include along each time you 
  // recurse. However Geoff says this is not the case!
  to_include.clear();
  
  // Set up the new include formulas.
  if (include_item.second.empty() || 
     (include_item.second.size() == 1 && include_item.second[0] == string("all"))) {
      if (params::first_parse) {
        show(1,string("All"),true);
      }
  }
  else {
    for (string s : include_item.second) {
      to_include.insert(s);
      if (params::first_parse) {
        show(1, s, true);
      }
    }
  }

  // Get the file you want to include.
  string file_contents;
  read_tptp_from_file_simple(file_name, file_contents);

  // Use the existing parser.
  Iter start = file_contents.begin();
  Iter end = file_contents.end();

  TPTP_file_grammar<Iter> g;
  bool result = qi::phrase_parse(start, end, g, ascii::space);

  if (start != end || !result) 
    throw (file_parse_exception(file_name));

  // Restore previous include formulas.
  to_include = saved_includes; 
  if (to_include.empty()) 
    include_this_item = true;

  // Restore include file path.
  include_file_path = saved_path;
}
//--------------------------------------------------------------
bool TPTPParser::conjecture_present() const {
  return conjecture_found;
}
//--------------------------------------------------------------
bool TPTPParser::negated_conjecture_present() const {
  return negated_conjecture_found;
}
//--------------------------------------------------------------
bool TPTPParser::no_conjecture_clause() const {
  return ((all_formulas.size() > 0 && !conjecture_found) ||
          (all_formulas.size() > 0 && (conjecture_true || conjecture_false)) ||
          (all_formulas.size() == 0 && !negated_conjecture_found) ||
          (all_formulas.size() == 0 && !negated_conjecture_exists));
}
bool TPTPParser::problem_is_cnf_only() const {
  return cnf_only;
}
//--------------------------------------------------------------
bool TPTPParser::fof_conjecture_is_true() const {
  return conjecture_true;
}

//--------------------------------------------------------------
bool TPTPParser::fof_conjecture_is_false() const {
  return conjecture_false;
}
//--------------------------------------------------------------
bool TPTPParser::fof_conjecture_is_missing() const {
  return !conjecture_found;
}
//--------------------------------------------------------------
bool TPTPParser::fof_negated_conjecture_removed() const {
  return conjecture_found && (number_of_simplified_negated_conjecture_clauses == 0);
}
//--------------------------------------------------------------
bool TPTPParser::simplified_fof_has_axioms() const {
  return has_axioms_remaining;
}
//--------------------------------------------------------------
bool TPTPParser::fof_has_axioms() const {
  return has_axioms;
}
};
