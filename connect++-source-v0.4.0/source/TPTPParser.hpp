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

#ifndef TPTPPARSER_HPP
#define TPTPPARSER_HPP

#include <iostream>
#include <fstream>

#include <boost/spirit/include/qi.hpp>

#include "Exceptions.hpp"
#include "PredicateIndex.hpp"
#include "FunctionIndex.hpp"
#include "Matrix.hpp"
#include "FOF.hpp"
#include "vic_strings.hpp"

using std::string;
using std::vector;
using std::set;
using std::ifstream;
using std::cout;
namespace fs = std::filesystem;

using namespace boost::spirit;

//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
namespace tptp_parser {
  /**
  * \brief Iterator type for parser rules and grammars.
  */
  using Iter = string::const_iterator;
  /**
  * \brief Recursive data structures for terms and so on.
  *
  * Recursion here, so need to define this in advance.
  */
  struct fof_plain_term_struct;
  /**
  * \brief Variant - Term arguments can be Variables or other Terms.
  */
  using fof_arguments_struct =
    boost::variant<
      string,
      boost::recursive_wrapper<fof_plain_term_struct>
    >;
  /**
  * \brief Recursive data structure for Terms.
  *
  * This is pretty closely based on the XML example in the
  * boost documentation.
  *
  * fof_plain_term includes other fof_plain_terms, so
  * this has to be made recursive.
  */
  struct fof_plain_term_struct {
    string functor;
    std::vector<fof_arguments_struct> args;
  };
  /**
  * \brief Structure for fof_defined_infix_formula and fof_infix_unary.
  */
  struct infix_struct {
    fof_arguments_struct left;
    string connective;
    fof_arguments_struct right;
  };
  /**
  * \brief An atomic formula can be infix as well. 
  */
  using fof_atomic_formula_type = boost::variant<
    fof_plain_term_struct,
    infix_struct
  >;
  /**
  * \brief Parser's representation of a Clause.
  */
  struct cnf_annotated_struct {
    string name;
    string role;
    std::vector<fof_atomic_formula_type> f;
  };
} // tptp_parser namespace ends.
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief You have to make fof_plain_term_struct etc something
*        that boost::fusion can use.
*
* Note that we've just left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
    tptp_parser::fof_plain_term_struct,
    (string, functor)
    (std::vector<tptp_parser::fof_arguments_struct>, args)
)
/**
* \brief You have to make fof_plain_term_struct etc something
*        that boost::fusion can use.
*
* Note that we've just left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
    tptp_parser::infix_struct,
    (tptp_parser::fof_arguments_struct, left)
    (string, connective)
    (tptp_parser::fof_arguments_struct, right)
)
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
// Back to the tptp_parser namespace.
//---------------------------------------------------------------------
namespace tptp_parser {
  /**
  * \brief Recursive data structures for first order formulas.
  *
  * This is also loosely based on the example in the
  * documentation.
  *
  * This requires great care, not to mention blood sweat and
  * tears, to get the types right. As usual DON'T MESS AROUND 
  * HERE unless you REALLY know what you're doing!
  */
  struct fof_unitary_formula_struct;
  struct fof_negation_struct;
  struct fof_quantifier_struct;
  struct fof_binary_struct;
  struct fof_andor_struct;
  /**
  * \brief An FOF formula can be quite a few different things.
  */
  using fof_formula_type = boost::variant<
    fof_plain_term_struct,
    infix_struct,
    boost::recursive_wrapper<fof_unitary_formula_struct>,
    boost::recursive_wrapper<fof_negation_struct>,
    boost::recursive_wrapper<fof_quantifier_struct>,
    boost::recursive_wrapper<fof_binary_struct>,
    boost::recursive_wrapper<fof_andor_struct>
  >;
  /**
  * \brief Data structure for first order formulas.
  */
  struct fof_unitary_formula_struct {
    fof_formula_type arg;
  };
  /**
  * \brief Data structure for first order formulas.
  */
  struct fof_negation_struct {
    string type;
    fof_formula_type arg;
  };
  /**
  * \brief Data structure for first order formulas.
  */
  struct fof_quantifier_struct {
    string type;
    std::vector<string> vars;
    fof_formula_type arg;
  };
  /**
  * \brief Data structure for first order formulas.
  */
  struct fof_binary_struct {
    fof_formula_type lhs;
    string type;
    fof_formula_type rhs;
  };
  /**
  * \brief Data structure for first order formulas.
  */
  struct fof_andor_struct {
    fof_formula_type lhs;
    string type;
    vector<fof_formula_type> rhs;
  };
} // tptp_parser namespace ends.
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief You have to make these something
*        that boost::fusion can use.
*
* Note that we've left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
  tptp_parser::fof_unitary_formula_struct,
  (tptp_parser::fof_formula_type, arg)
)
/**
* \brief You have to make these something
*        that boost::fusion can use.
*
* Note that we've left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
  tptp_parser::fof_negation_struct,
  (string, type)
  (tptp_parser::fof_formula_type, arg)
)
/**
* \brief You have to make these something
*        that boost::fusion can use.
*
* Note that we've left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
  tptp_parser::fof_quantifier_struct,
  (string, type)
  (std::vector<string>, vars)
  (tptp_parser::fof_formula_type, arg)
)
/**
* \brief You have to make these something
*        that boost::fusion can use.
*
* Note that we've left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
  tptp_parser::fof_binary_struct,
  (tptp_parser::fof_formula_type, lhs)
  (string, type)
  (tptp_parser::fof_formula_type, rhs)
)
/**
* \brief You have to make these something
*        that boost::fusion can use.
*
* Note that we've left the tptp_parser namespace.
* If you don't then the next bit causes havoc.
*/
BOOST_FUSION_ADAPT_STRUCT(
  tptp_parser::fof_andor_struct,
  (tptp_parser::fof_formula_type, lhs)
  (string, type)
  (std::vector<tptp_parser::fof_formula_type>, rhs)
)
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
// Back to the tptp_parser namespace.
//---------------------------------------------------------------------
namespace tptp_parser {
  /**
  * \brief Display terms, literals and clauses while parsing.
  *
  * Mostly for debugging purposes and probably not used in the
  * final code.
  */
  struct show_fof_plain_term {
    void operator()(const fof_plain_term_struct&);
  };
  /**
  * \brief Display terms, literals and clauses while parsing.
  *
  * Mostly for debugging purposes and probably not used in the
  * final code.
  */
  struct show_fof_arguments : boost::static_visitor<> {
    void operator()(const string& s) {
      cout << s;
    }
    void operator()(const fof_plain_term_struct& t) {
      show_fof_plain_term spt;
      spt(t);
    }
  };
  /**
  * \brief Display terms, literals and clauses while parsing.
  *
  * Mostly for debugging purposes and probably not used in the
  * final code.
  */
  struct show_fof_atomic_formula : boost::static_visitor<> {
    void operator()(const fof_plain_term_struct& s) {
      show_fof_plain_term st;
      st(s);
    }
    void operator()(const infix_struct& s) {
      show_fof_arguments sa;
      boost::apply_visitor(sa, s.left);
      cout << " " << s.connective << " ";
      boost::apply_visitor(sa, s.right);
    }
  };
  /**
  * \brief Display terms, literals and clauses while parsing.
  *
  * Mostly for debugging purposes and probably not used in the
  * final code.
  */
  struct show_clause {
    void operator()(const vector<fof_atomic_formula_type>& v) const {
      show_fof_atomic_formula st;
      cout << "Clause = {" << endl;
      for (fof_atomic_formula_type f : v) {
          cout << "    ";
          boost::apply_visitor(st, f);
          cout << endl;
      }
      cout << '}' << endl;
    }
  };
  /**
  * \brief Display FOL formulas as you parse.
  *
  * Mostly for debugging purposes and probably not used in the
  * final code.
  */
  struct show_fof_formula_type : boost::static_visitor<> {
    void operator()(const fof_plain_term_struct& t) {
      show_fof_atomic_formula saf;
      saf(t);
    }
    void operator()(const infix_struct& s) {
      show_fof_atomic_formula saf;
      saf(s);
    }
    void operator()(const fof_unitary_formula_struct& f) {
      show_fof_formula_type sf;
      boost::apply_visitor(sf, f.arg);
    }
    void operator()(const fof_negation_struct& f) {
      cout << f.type << "(";
      show_fof_formula_type sf;
      boost::apply_visitor(sf, f.arg);
      cout << ")";
    }
    void operator()(const fof_quantifier_struct& f) {
      cout << f.type << " [";
      for (const string& s : f.vars)
        cout << s << " ";
      cout << "] (";
      show_fof_formula_type sf;
      boost::apply_visitor(sf, f.arg);
      cout << ")";
    }
    void operator()(const fof_binary_struct& f) {
      show_fof_formula_type sf;
      boost::apply_visitor(sf, f.lhs);
      cout << " " << f.type << " ";
      boost::apply_visitor(sf, f.rhs);
    }
    void operator()(const fof_andor_struct& f) {
      show_fof_formula_type sf;
      boost::apply_visitor(sf, f.lhs);
      for (const fof_formula_type& g : f.rhs) {
        cout << " " << f.type << " ";
        boost::apply_visitor(sf, g);
      }
    }
  };
  /**
  * \brief Display FOL formulas as you parse.
  *
  * Mostly for debugging purposes and probably not used in the
  * final code.
  */
  struct show_fof_formula {
    void operator()(const fof_formula_type& f) const {
    show_fof_formula_type sf;
    boost::apply_visitor(sf, f);
    cout << endl;
  }
};
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief One of several basic semantic actions.
*
* Collectively, store include file information, comments and so on.
*/
struct FileIncludeAdder {
  void operator()(const vector<string>&, qi::unused_type, qi::unused_type) const;
};
/**
* \brief One of several basic semantic actions.
*
* Collectively, store include file information, comments and so on.
*/
struct CommentStatus {
  void operator()(const string&, qi::unused_type, qi::unused_type) const;
};
/**
* \brief One of several basic semantic actions.
*
* Collectively, store include file information, comments and so on.
*/
struct DefinedAdder {
  void operator()(const string&, qi::unused_type, qi::unused_type) const;
};
/**
* \brief One of several basic semantic actions.
*
* Collectively, store include file information, comments and so on.
*/
struct SystemAdder {
  void operator()(const string&, qi::unused_type, qi::unused_type) const;
};
/**
* \brief One of several basic semantic actions.
*
* Collectively, store include file information, comments and so on.
*/
struct DistinctAdder {
  void operator()(const string&, qi::unused_type, qi::unused_type) const;
};
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief Collection of more complex semantic actions.
*
* These are for the literal grammar.
*/
struct to_lit {
  void operator()(const fof_atomic_formula_type&,  qi::unused_type,qi::unused_type) const;
};
/**
* \brief Collection of more complex semantic actions.
*
* These are for the literal grammar.
*/
struct show_lit {
  void operator()(const fof_atomic_formula_type&,  qi::unused_type,  qi::unused_type) const;
};
/**
* \brief Collection of more complex semantic actions.
*
* These are for the literal grammar.
*/
struct set_neg_lit {
  void operator()(qi::unused_type,  qi::unused_type,  qi::unused_type) const;
};
/**
* \brief Collection of more complex semantic actions.
*
* These are for the literal grammar.
*/
struct unset_neg_lit {
  void operator()(qi::unused_type,  qi::unused_type,  qi::unused_type) const;
};
/**
* \brief Collection of more complex semantic actions.
*
* These are for the literal grammar.
*/
struct clear_current_clause {
  void operator()(qi::unused_type,  qi::unused_type,  qi::unused_type) const;
};
/**
* \brief Collection of more complex semantic actions.
*
* These are for the literal grammar.
*/
struct add_current_clause {
  void operator()(qi::unused_type,  qi::unused_type,  qi::unused_type) const;
};
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief More complex semantic actions, now functions etc to make 
*        a literal.
*
* This is complicated by the need to be very careful to 
* distinguish predicates from functions. So we have one
* function to deal with fof_plain_term the first time it's seen,
* to get a predicate. Then a different one to get the functions.
*/
struct convert_fof_atomic_formula : boost::static_visitor<Literal> {
  Literal operator()(const fof_plain_term_struct&) const;
  Literal operator()(const infix_struct&) const;
};
/**
* \brief More complex semantic actions, now functions etc to make 
*        a literal.
*
* This is complicated by the need to be very careful to 
* distinguish predicates from functions. So we have one
* function to deal with fof_plain_term the first time it's seen,
* to get a prodicate. Then a different one to get the functions.
*/
struct convert_fof_arguments_struct : boost::static_visitor<Term*> {
  Term* operator()(const string&) const;
  Term* operator()(const fof_plain_term_struct&) const;
};
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief Semantic action for cnf_formula.
*/
struct print_cnf_formula_name {
  void operator()(const string&,
    qi::unused_type,
    qi::unused_type) const;
};
/**
* \brief Semantic action for cnf_formula.
*/
struct print_cnf_formula_role {
  void operator()(const string&,
    qi::unused_type,
    qi::unused_type) const;
};
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief Semantic action for fof_formula.
*/
struct print_fof_formula_name {
  void operator()(const string&,
    qi::unused_type,
    qi::unused_type) const;
};
/**
* \brief Semantic action for fof_formula.
*/
struct print_fof_formula_role {
  void operator()(const string&,
    qi::unused_type,
    qi::unused_type) const;
};
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/** 
* \brief More complex semantic action for FOF formulas.
*
* Functions etc to make a FOF formula.
*/
struct convert_fof_formula : boost::static_visitor<FOF> {
  FOF operator()(const fof_plain_term_struct&) const;
  FOF operator()(const infix_struct&) const;
  FOF operator()(const fof_unitary_formula_struct&) const;
  FOF operator()(const fof_negation_struct&) const;
  FOF operator()(const fof_quantifier_struct&) const;
  FOF operator()(const fof_binary_struct&) const;
  FOF operator()(const fof_andor_struct&) const;
};
/** 
* \brief More complex semantic action for FOF formulas.
*
* Functions etc to make a FOF formula.
*/
struct make_fof_formula {
  void operator()(const fof_formula_type&, qi::unused_type,  qi::unused_type) const;
};
/** 
* \brief More complex semantic action for FOF formulas.
*
* Functions etc to make a FOF formula.
*/
struct add_fof_formula {
  void operator()(qi::unused_type,  qi::unused_type,  qi::unused_type) const;
};
//---------------------------------------------------------------------
/** \brief This is essentially the same as read_tptp_from_file, but 
*          doesn't collect comments.
*
* It is also global within the namespace because it needs to be used 
* to process includes, and that's a lot easier this way.
*
* @param file_name     Reference to name of file.
* @param file_contents Reference used to return result. 
*/
void read_tptp_from_file_simple(const string&, string&);
//---------------------------------------------------------------------
/** \brief Deal with TPTP includes. 
*
* This all feels a bit delicate, but is essentially just 
* a bit of (mutual) recursion between this function and 
* the parser. We're using the global 
* set<string> to_include to keep track of what to take 
* notice of. 
*
* @param include_item Reference to FileIncludeItem. 
*/
using FileIncludeItem = pair<string, vector<string>>;

void recursive_tptp_include(const FileIncludeItem&);
//---------------------------------------------------------------------
//---------------------------------------------------------------------
//---------------------------------------------------------------------
/**
* \brief Wrap up everything the TPTP parser needs to do inside a single
*        class.
*
* This class needs access to the assorted indices employed by the prover 
* because they are the only things anyone should be using to make 
* Terms, Variables etc. 
*
* If you construct this properly and use parse_tptp_from_file, then 
* after a successful parse the indices have everything ready to go.
*/
class TPTPParser {
private:
    /**
    * \brief Contents of the TPTP file, with comments removed. 
    *
    * Assuming of course that you used read_tptp_from_file.
    */
    string file_contents;
    /**
    * \brief Each comment is stored here.
    */
    vector<string> comment_blocks;
    /**
    * \brief The class has pointers to all the relevant indices.
    *
    * These are used directly to make the actual data structures 
    * used by the prover.
    */
    VariableIndex* vip;
    /**
    * \brief The class has pointers to all the relevant indices.
    *
    * These are used directly to make the actual data structures 
    * used by the prover.
    */
    FunctionIndex* fip;
    /**
    * \brief The class has pointers to all the relevant indices.
    *
    * These are used directly to make the actual data structures 
    * used by the prover.
    */
    TermIndex* tip;
    /**
    * \brief The class has pointers to all the relevant indices.
    *
    * These are used directly to make the actual data structures 
    * used by the prover.
    */
    PredicateIndex* pip;
    /**
    * \brief The class has a pointer to the matrix, and can 
    *        therefore construct it as it parses.
    */
    Matrix* matrix;
    /**
    * \brief Used to build a string containing the TPTP-friendly 
    *        description of the clause conversion.
    */
    string tptp_conversion_string;
    /**
    * \brief Read the file into a string, while stripping out and
    *        collecting comment blocks. 
    *
    * (Yes, better done with a custom skip parser, but writing 
    * those is a pain.)
    * 
    * @param file_name Reference to a string containing the file name
    */
    void read_tptp_from_file(const string&);
public:
    /**
    * \brief You definitely don't want this constructor.
    */
    TPTPParser() = delete;
    /**
    * \brief The only constructor that makes sense.
    */
    TPTPParser(VariableIndex*,
      FunctionIndex*,
      TermIndex*,
      PredicateIndex*,
      Matrix*);
    /**
    * \brief Main method to parse from a TPTP file to the data 
    *        structures needed by the prover.
    *
    * This first uses read_tptp_from_file to strip out comments. 
    * It then uses TPTP_file_grammar with qi::phrase_parse to 
    * parse the file.
    *
    * As a side effect of that, a bunch of things such as all_clauses 
    * and clause_roles, which are global in the tptp_parser 
    * namespace, get set up. These are then used to populate the 
    * matrix etc.
    *
    * @param file_name Reference to string containing the file name.
    */
    bool parse_tptp_from_file(const string&);
    /**
    * \brief Show any includes present in the TPTP file.
    *
    * These are collected as part of the parse.
    */
    void show_file_includes();
    /**
    * \brief Clear everything associated with the TPTP parser.
    *
    * Note that this is slightly messy because it also clears 
    * all the supporting stuff that's global in the tptp_parser 
    * namespace. Yes, very ugly. What ya gonna do about it!!??
    */
    void clear();
    /**
    * \brief Get a copy of tptp_parser::all_defined.
    *
    * These are gathered during the parse and may be useful.
    */
    vector<string> get_defined_items();
    /**
    * \brief Get a copy of tptp_parser::all_system.
    *
    * These are gathered during the parse and may be useful.
    */
    vector<string> get_system_items();
    /**
    * \brief Did equality turn up anywhere in the parse?
    */
    bool equality_used();
    /**
    * \brief Did a conjecture turn up anywhere in the parse?
    */
    bool conjecture_present() const;
    /**
    * \brief Did a negated conjecture turn up anywhere in the parse?
    */
    bool negated_conjecture_present() const;
    /**
    * \brief When you analysed the original problem, did you 
    *        conclude that it has no conjecture clauses that 
    *        can be used as a starting point?
    */
    bool no_conjecture_clause() const;
    /**
    * \brief How many first-order formulas turned up in the parse?
    */
    size_t number_of_fof_formulas() const;
    /**
    * \brief The parse tries to identify the problem status.
    */
    string get_problem_status();
    /**
    * \brief If equality turned up anywhere in the parse it will have 
    *        been turned into an actual Predicate, so this will 
    *        give you a pointer to it.
    */
    Predicate* get_equals_predicate() const;
    /** 
    * \brief Self-explanatory.
    */
    bool problem_is_cnf_only() const;
    /** 
    * \brief Self-explanatory.
    */
    bool fof_conjecture_is_true() const;
    /** 
    * \brief Self-explanatory.
    */
    bool fof_conjecture_is_false() const;
    /** 
    * \brief Was there a conjecture clause in the problem file?
    */
    bool fof_conjecture_is_missing() const;
    /**
    * \brief Was there a conjecture clause that got simplified away?
    */
    bool fof_negated_conjecture_removed() const;
    /** 
    * \brief Where there any axioms for an FOF problem after simplification?
    */
    bool simplified_fof_has_axioms() const;
    /** 
    * \brief Where there any axioms for an FOF problem before simplification?
    */
    bool fof_has_axioms() const;
    /**
    * \brief Self-explanatory.
    */
    string get_tptp_conversion_string() const {
      return tptp_conversion_string;
    }
};

};

#endif
