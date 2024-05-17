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

#ifndef FOF_HPP
#define FOF_HPP

#include<iostream>
#include<string>

#include "PredicateIndex.hpp"
#include "FunctionIndex.hpp"
#include "Literal.hpp"
#include "Clause.hpp"

using std::string;
using std::cout;
using std::endl;

/**
* \brief Enumeration of kinds of FOF.
*/
enum class FOFType {Empty, Atom, Neg, And, Or, Imp, Iff, A, E};

/**
* \brief Representation of first order formulas. 
* 
* First and foremost: I intensely dislike the use of inheritance. 
* I vastly prefer to make the methods static and do everything the 
* obvioous way. If you want the alternative sort of OO, then feel free 
* to implement this yourself.
* 
* This has to play nicely with the parser and with the indexing of 
* terms, variables and so on, so it needs pointers to the relevant 
* indices.  
*/
class FOF {
private:
  /** 
  * \brief Used for all FOFs to denote what kind it it.
  */
  FOFType type;
  /**
  * \brief FOFType::Atom can store one of 
  *        these to represent a Literal.
  */
  Literal pred;
  /**
  * \brief Most FOFs will have subformulas.
  */
  vector<FOF> sub_formulas;
  /**
  * \brief Associate a Variable with a quantifier.
  */
  Variable* var;
  /**
  * \brief Access to the index: static because all FOFs should
  *        share it.
  */
  static VariableIndex* var_index;
  /**
  * \brief Access to the index: static because all FOFs should
  *        share it.
  */
  static FunctionIndex* fun_index;
  /**
  * \brief Access to the index: static because all FOFs should
  *        share it.
  */
  static TermIndex* term_index;
  /**
  * \brief Access to the index: static because all FOFs should
  *        share it.
  */
  static PredicateIndex* pred_index;
  //---------------------------------------------------------------------------
  // Simple methods for Variables.
  //---------------------------------------------------------------------------
  /**
  * \brief Does this formula contain the specified variable 
  * unbound?
  *
  * *Only* use this if bound variables are unique. (If it finds 
  * *any* quantifier binding the variable it will return false.)
  *
  * @param v Pointer to Variable of interest.
  */ 
  bool has_free_variable(Variable*);
  /** 
  * \brief Self-explanatory. 
  *
  * However note that this works only on Atoms: quantifiers will be 
  * unaffected.
  *
  * @param new_var Pointer to new Variable.
  * @param old_var Pointer to Variable to replace.
  */
  void replace_variable(Variable*, Variable*);
  //---------------------------------------------------------------------------
  // Skolemization.
  //---------------------------------------------------------------------------
  /** 
  * \brief Make a new Skolem function.
  *
  * Mainly achieved using methods from other classes. 
  *
  * @param args Vector of pointers to Term. These are the Skolem 
  *             function arguments.
  */
  Term* make_skolem_function(const vector<Term*>&);
   /** 
  * \brief Replace a Variable with a Term.
  *
  * Mainly achieved using methods from other classes.
  *
  * Note that this works only on Atoms: quantifiers will be 
  * unaffected.
  *
  * @param new_term Pointer to new Term to use.
  * @param old_var Pointer to Variable to replace.
  */
  void replace_variable_with_term(Term*, Variable*);
  /**
  * \brief Main helper function called by FOF::skolemize().
  *
  * The parameter is used to collect variables for the universal 
  * quantifiers inside which you find an existential quantifier. 
  * Those then become the parameters for the Skolem function.
  *
  * @param skolem_arguments Vector of pointers to Term. 
  *
  * @see make_skolem_function.
  * @see replace_variable_with_term.
  */
  void skolemize_main(vector<Term*>);
  /**
  * \brief The dual of skolemize_main.
  *
  * @see skolemize_main
  */
  void skolemize_universals_main(vector<Term*>);
  //---------------------------------------------------------------------------
  // Miniscoping.
  //---------------------------------------------------------------------------
  /**
  * \brief Helper for miniscope.
  *
  * Split subformulas into ones that do and don't have the 
  * relevant variable.
  *
  * @param v       Pointer to Variable of interest.
  * @param free    Reference to vector of FOF. Collect FOFs 
                   with the Variable.
  * @param absent  Reference to vector of FOF. Collect FOFs 
                   without the Variable.
  */
  void miniscope_split(Variable*, vector<FOF>&, vector<FOF>&);
  /**
  * \brief Apply miniscoping to all subformulas.
  */
  void miniscope_all();
  //---------------------------------------------------------------------------
  // Definitional clause translation.
  //---------------------------------------------------------------------------
  /**
  * \brief When doing definitional clause conversion you need to be able to 
  *        make unique new predicates. This will provide one.
  */
  FOF make_definitional_predicate() const;
  //---------------------------------------------------------------------------
  // Distribution of Or/And.
  //---------------------------------------------------------------------------
  /**
  * \brief Find an OR that can be distributed and deal with 
  *        it. Indicate if there isn't one.
  */
  bool distribute_or_once();
  /**
  * \brief Find an AND that can be distributed and deal with 
  *        it. Indicate if there isn't one.
  */
  bool distribute_and_once();
public:
  //---------------------------------------------------------------------------
  // Constructors.
  //---------------------------------------------------------------------------
  /**
  * \brief You don't want this constructor.
  */
  FOF() = delete;
  /**
  * \brief You probably don't want this constructor.
  */
   FOF(FOFType t)
  : type(t), pred(), sub_formulas(), var(nullptr) {}
  /**
  * \brief Construct FOF from Literal.
  *
  * @param lit Reference to Literal to use.
  */
  FOF(const Literal&);
  /**
  * \brief Construct FOF for a non-literal.
  *
  * @param t Specify FOFType for what you're making.
  * @param sf Reference to vector of FOF for subformulas.
  * @param v Pointer to Variable.
  */
  FOF(FOFType, const vector<FOF>&, Variable*);
  //---------------------------------------------------------------------------
  // Straightforward methods for getting, setting etc.
  //---------------------------------------------------------------------------
  /**
  * \brief Set up pointer to the variable index etc.
  */
  static void set_indexes(std::tuple<VariableIndex*, 
                          FunctionIndex*, 
                          PredicateIndex*, 
                          TermIndex*> is) {
    var_index = std::get<0>(is);
    fun_index = std::get<1>(is);
    pred_index = std::get<2>(is);
    term_index = std::get<3>(is);
  }
  /**
  * \brief Show the indices.
  */
  void show_indexes() const {
    cout << var_index << " " << fun_index 
                      << " " << pred_index 
                      << " " << term_index 
                      << endl;
  }
  /**
  * \brief Basic get method.
  */
  FOFType fof_type() { return type; }
  /**
  * \brief Add a subformula.
  */
  void add_formula(const FOF& f) { sub_formulas.push_back(f); }
  /**
  * \brief Make an FOFType::Empty.
  */
  void clear() { 
    type = FOFType::Empty; 
    pred.clear(); 
    sub_formulas.clear();
     var = nullptr; 
  }
  //---------------------------------------------------------------------------
  // Straightforward methods for making FOFs.
  //---------------------------------------------------------------------------
  /**
  * \brief Directly make a Literal.
  */
  static FOF make_literal(const Literal& lit) {
    FOF result(lit);
    return result;
  }
  /**
  * \brief Directly negate a FOF.
  *
  * Careful: no attempt here to make any obvious simplifications.
  */
  static FOF make_neg(const FOF& f) {
    vector<FOF> fs;
    fs.push_back(f);
    FOF result(FOFType::Neg, fs, nullptr);
    return result;
  }
  /**
  * \brief Directly make a conjunction.
  */
  static FOF make_and(const vector<FOF>& fs) {
    FOF result(FOFType::And, fs, nullptr);
    return result;
  }
  /**
  * \brief Directly make a disjunction.
  */
  static FOF make_or(const vector<FOF>& fs) {
    FOF result(FOFType::Or, fs, nullptr);
    return result;
  }
  /**
  * \brief Directly make an implication.
  */
  static FOF make_imp(const FOF& lhs, const FOF& rhs) {
    vector<FOF> fs;
    fs.push_back(lhs);
    fs.push_back(rhs);
    FOF result(FOFType::Imp, fs, nullptr);
    return result;
  }
  /**
  * \brief Directly make an iff.
  */
  static FOF make_iff(const FOF& lhs, const FOF& rhs) {
    vector<FOF> fs;
    fs.push_back(lhs);
    fs.push_back(rhs);
    FOF result(FOFType::Iff, fs, nullptr);
    return result;
  }
  /**
  * \brief Directly make a universally quantified FOF.
  */
  static FOF make_forall(const FOF& f, Variable* v) {
    vector<FOF> fs;
    fs.push_back(f);
    FOF result(FOFType::A, fs, v);
    return result;
  }
  /**
  * \brief Directly make an existentially quantified FOF.
  */
  static FOF make_exists(const FOF& f, Variable* v) {
    vector<FOF> fs;
    fs.push_back(f);
    FOF result(FOFType::E, fs, v);
    return result;
  }
  //---------------------------------------------------------------------------
  // Basic tests.
  //---------------------------------------------------------------------------
  /**
  * \brief Check if an FOF is a literal. 
  *
  * Works in general, not just for NNF.
  */
  bool is_literal() const;
  /**
  * \brief Check if something is a clause.
  *
  * This check in the strict sense: either it must be a literal or 
  * a disjunction of literals, including an empty disjunction.
  *
  * Returns false if FOFType::Empty.
  */
  bool is_clause() const;
  //---------------------------------------------------------------------------
  // Standard simplifications.
  //---------------------------------------------------------------------------
  /**
  * \brief Remove the leading negation from an arbitrary
  * FOF, if it has one.
  */
  void remove_negation();
  /**
  * \brief Negate an FOF, applying obvious simplifications if it's already
  * negated or an implication.
  */
  void negate();
  /**
  * \brief Negate an FOF without applying any simplifications.
  */
  void simple_negate();
  /**
  * \brief Self-explanatory!
  */
  void invert_literal();
  /**
  * \brief Replace <-> throughout using ->.
  */
  void remove_iff();
  /**
  * \brief Replace A->B throughout with neg A v B.
  */
  void remove_imp();
  /**
  * \brief Replace all bound variables with unique new ones.
  *
  * Has to be done with care to maintain the indexes correctly.
  */
  void make_unique_bound_variables();
  /**
  * \brief Remove quantifiers if they don't bind anything in 
  *        their scope.
  *
  * Yes, the TPTP does contain such formulas. Use this only 
  * if bound variables are unique.
  */
  void remove_redundant_quantifiers();
  /**
  * \brief Push all negations in.
  *
  * DON'T call it on anything with a -> or <->.
  */
  void push_negs();
  /**
  * \brief Convert to Negation Normal Form.
  *
  * Follows the usual recipe (Larry's lecture notes.)
  */
  void convert_to_nnf();
  /**
  * \brief Apply the rules for miniscoping.
  *
  * Push the quantifiers in as much as you can. 
  * Don't use this unless your formula is in NNF.
  */
  void miniscope();
  /**
  * \brief Convert to Conjunctive Normal Form.
  *
  * Follow the usual recipe (Larry's lecture notes.) BUT 
  * there are lots of ways to do this---at present there is 
  * nothing sophisticated happening, and the approach is 
  * entirely obvious/straightforward. Also, this implementation 
  * does miniscoping.
  *
  * @param cs vector of clauses containing the CNF.
  */
  void convert_to_cnf_clauses(vector<Clause>&);
  /**
  * \brief Split subformulas in half.
  *
  * @param left_sub First half of the subformulas.
  * @param right_sub Second half of subformulas. 
  */
  void split_sub_formulas(vector<FOF>&, vector<FOF>&);
  /**
  * \brief Heavy-lifting for conversion to definitional clause 
  *        form.
  *
  * @param f First part of definitional tuple.
  * @param d Second part of definitional tuple.
  * @param in_conjunctionm Indicates whether or not the 
  *                        parent formula was a conjunction.
  */
  void find_definitional_tuple(FOF&, vector<FOF>&, bool);
  /**
  * \brief Convert to Conjunctive Normal Form using 
  *        a form of definitional conversion.
  *
  * There are lots of ways of doing definitional conversion. However 
  * as the restricted backtracking paper describing leanCoP v2.1 
  * gives experimental results demonstrating that a particular approach 
  * is preferred, this implements the method as described in that 
  * paper.
  *
  * @param cs vector of clauses containing the CNF.
  *
  * @see find_definitional_tuple
  */
  void definitional_convert_to_cnf_clauses(vector<Clause>&);
  /**
  * \brief Skolemize the given formula.
  *
  * All the hard work is done by skolemize_main.
  *
  * @see skolemize_main 
  */
  void skolemize();
  /**
  * \brief Self-explanatory.
  */
  void remove_universal_quantifiers();
  /**
  * \brief Skolemize the universal quantifiers in the 
  *        given formula.
  *
  * All the hard work is done by skolemize_universals_main.
  *
  * @see skolemize_universals_main 
  */
  void skolemize_universals();
  /**
  * \brief Self-explanatory.
  */
  void remove_existential_quantifiers();
  /**
  * \brief Assuming the FOF is a literal, convert it to something of 
  *        type Literal.
  *
  * This is straightforward as most of the heavy lifting has already 
  * been done. DON'T use it on an FOF that isn't in the form of 
  * a literal.
  */
  void to_Literal(Literal&) const;
  /**
  * \brief Assuming you have a CNF, convert it to a 
  *        collection of Clauses.
  */
  void convert_to_clauses(vector<Clause>&) const;
  /**
  * \brief Assuming you have a DNF, invert it and convert it to a 
  *        collection of CNF clauses.
  */
  void dnf_invert_and_convert_to_clauses(vector<Clause>&) const;
  /**
  * \brief Does the collection of subformulas contain an AND?
  *        If so, find it.
  *
  * Note: does not do any recursion -- only looks at the top 
  * level.  
  */
  size_t find_and() const;
  /**
  * \brief Does the collection of subformulas contain an OR?
  *        If so, find it.
  *
  * Note: does not do any recursion -- only looks at the top 
  * level.  
  */
  size_t find_or() const;
  /**
  * \brief Distribute ORs to the maximum extent possible.
  *
  * Assumes you have nothing but a quantifier-free NNF. The 
  * result will have a tree structure with ANDs at the top, then 
  * ORs, then literals. 
  */
  void distribute_or();
  /**
  * \brief Distribute ANDs to the maximum extent possible.
  *
  * Assumes you have nothing but a quantifier-free DNF in NNF. 
  * The result will have a tree structure with ORs at the 
  * top, then ANDs, then literals. 
  */
  void distribute_and();
  /**
  * \brief Convert a FOF into a nice-looking string.
  */
  string to_string() const;
  /**
  * \brief Simplify the clauses in a CNF using the method 
  *        in Clause.
  */
  static SimplificationResult simplify_cnf(vector<Clause>&);
  /**
  * \brief As first version of simplify_cnf, but keep track of 
  *        corresponding roles as well.
  */
  static SimplificationResult simplify_cnf(vector<Clause>&, vector<string>&);
  /**
  * \brief Find the free variables in the formula.
  *
  * Note: will consider x to be free in:
  *
  *  ( P(x) | Ax. Q(x) ).
  */
  set<Term*> find_free_variables() const;

  friend ostream& operator<<(ostream&, const FOF&);
};


#endif
