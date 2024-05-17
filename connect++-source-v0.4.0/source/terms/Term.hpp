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

#ifndef TERM_HPP
#define TERM_HPP

#include<iostream>
#include<sstream>
#include<string>
#include<vector>
#include<set>
#include<unordered_map>

#include "VariableIndex.hpp"

using std::vector;
using std::pair;
using std::unordered_map;
using std::ostream;
using std::ostringstream;
using std::to_string;
using std::set;

using VarMapType = pair<Variable*,Term*>;

class TermIndex;

/**
* \brief General representation of terms.
*
* Terms can be variables or function-based. This requires care,
* because after you substitute the former for the latter, it
* effectively becomes the latter. Similarly, function-based terms
* are altered by substitution. If a method has "subbed" in
* the name it means substitutions will be taken into account.
*
* And, yes, the OO mob want to do this with inheritance, but I don't
* because ultimately I want hash consing, and inheritance would stuff 
* that up BIG TIME!
*/
class Term {
private:
    Variable* v;
    Function* f;
    vector<Term*> args;
     /**
    * \brief Constructors - these are private as Terms should 
    *        only ever be constructed by the TermIndex, which is a 
    *        friend. 
    */
    Term() : v(nullptr), f(nullptr), args() {}
    Term(Variable* new_v) : v(new_v), f(nullptr), args() {}
    /**
    * \brief This is the only non-trivial constructor because of the
    *        need to deal with the function arguments.
    *
    * You really should make sure you only pass arguments that were 
    * obtained from the TermIndex.
    */
    Term(Function*, const vector<Term*>&);
public:
    friend class TermIndex;
    /**
    * Everything you do with these should really be done via 
    * pointers, so disallow copying where you can because that would 
    * mean you're doing something wrong.
    *
    * As usual, let the compiler help detect any errors.
    *
    * Unfortunately it turns out that if you want to use 
    * unordered_map to hash cons Terms then you do in fact 
    * need these.
    */
    #ifndef HASHCONSTERMS
    
    Term(const Term&) = delete;
    Term(const Term&&) = delete;
    Term& operator=(const Term&) = delete;
    Term& operator=(const Term&&) = delete;  
    
    #endif
    /**
    * \brief Self-explanatory access function.
    */
    inline Variable* get_v() const { return v; }
    /**
    * \brief Self-explanatory access function.
    */
    inline Function* get_f() const { return f; }
    /**
    * \brief Self-explanatory.
    */
    inline bool is_variable() const { return v != nullptr; }
    /**
    * \brief Self-explanatory.
    */
    inline bool is_function() const { return f != nullptr; }
    /**
    * \brief Self-explanatory access function.
    */
    inline Arity arity() const { return args.size(); }
    /**
    * \brief Access to args, but don't mess with them!
    * 
    * Do you really need to use this? Be careful as the parameter 
    * isn't checked.
    *
    * @param i Index of the argument you want.
    */
    Term* operator[](size_t) const;
    /**
    * \brief Make a string representation of the Term, taking into account
    * any substitutions that have been made.
    *
    * @param subbed Implement substitutions if true
    * @param show_addresses Show memory address of this Term if true
    */
    string to_string(bool = false, bool = false) const;
    /**
    * \brief Convert to a string that can be read by Prolog. 
    *
    * Does not apply substitutions.
    */
    string to_prolog_string() const;
    /**
    * \brief Make a useable LaTeX representation.
    *
    * Assumes you are in Math mode. 
    *
    * @param subbed Implement substitutions if true
    */
    string make_LaTeX(bool = false) const;
    /**
    * \brief For the TermIndex you want strict equaliity of the
    *        data members.
    *
    * This will *not* take substitutions into account.
    */
    bool operator==(const Term&) const;
    /**
    * \brief Test whether any variable has been substituted.
    */
    bool is_subbed() const;
    /**
    * \brief Equality test, taking substitution into account.
    *
    * For unification you have to take substitution into
    * account, so this needs different treatment to operator==.
    */
    bool subbed_equal(Term*) const;
    /**
    * \brief Is this a variable that hasn't been substituted?
    */
    bool is_unsubbed_variable() const;


    /*
    * The next block of methods are exactly analogous to those in
    * Variable.
    */


    /**
    * \brief Is this term a function, taking substitution into accoumt?
    */
    bool subbed_is_function() const;
    /**
    * \brief Is this term a variable, taking substitution into accoumt?
    */
    bool subbed_is_variable() const;
    /**
     * \brief Taking substitution into account, does the term include
     * the variable passed?
     *
     * Note that this acts on the eventual term, so if you look
     * for something that has itself been subbed then the answer is
     * "no".
     */
    bool contains_variable(Variable*) const;
    /**
     * \brief Taking substitution into account, what variable do we actually
     * have?
     */
    Variable* subbed_variable() const;
    /**
     * \brief Taking substitution into account, what function do we actually
     * have?
     */
    Function* get_subbed_f() const;
    /**
     * \brief Taking substitution into account, what arity do we actually
     * have?
     */
    Arity get_subbed_arity() const;
    /**
    * \brief It may be that there is a chain of substitutions attached to
    * a variable.
    *
    * When doing unification we actually want a pointer
    * either to the final variable in a chain or to the
    * first term that's a function. This returns it.
    */
    Term* skip_leading_variables() const;
    /**
    * \brief Taking substitution into account, find all the variables in a
    * term.
    *
    * Does not clear the parameter -- you may be adding to it across a
    * bunch of terms.
    */
    void find_subbed_vars(set<Variable*>&) const;
    /**
    * \brief Does as the name suggests.
    *
    * Not straightforward! See documentation for
    * make_copy_with_new_vars_helper
    *
    * Implementation is in TermIndex.cpp
    * 
    * @param vi Reference to the VariableIndex
    * @param ti Reference to the TermIndex
    */
    Term* make_copy_with_new_vars(VariableIndex&, TermIndex&) const;
    /**
    * \brief Main implementation of make_copy_with_new_vars.
    *
    * Requires care. You need to build this so that the hash consing
    * is maintained.
    *
    * In general you might also need to account for substituted 
    * variables. This method removes them entirely, so you end up 
    * with a term whose only variables are new, and which are 
    * also leaves.
    *
    * This needs to be maintained because the TermIndex should 
    * only ever have unsubstituted terms added. (In fact at present 
    * TermIndex doesn't make any distinction.)
    *
    * It may be necessary at some point to add something that also
    * replaces subbed variables with new ones, and additionally
    * updates the current substitution so that they are subbed to
    * the newly constructed terms. However, for Connection 
    * Calculus, this method is only needed with stuff in the 
    * matrix, and as variables are never directly substituted for 
    * things in the matrix the issue never arises.
    *
    * Implementation is in TermIndex.cpp
    *
    * @param vi Reference to the VariableIndex
    * @param ti Reference to the TermIndex
    * @param v_map Reference to an unordered_map from pointers 
                   to Variables, to pointers 
                   to Terms. Initially empty. On completion 
                   contains a map from variables, to the terms 
                   corresponding to the new variables made to 
                   replace them. 
    */
    Term* make_copy_with_new_vars_helper(VariableIndex&,
                                         TermIndex&,
                                         unordered_map<Variable*,Term*>&) const;
    /**
    * \brief Assuming nothing has been substituted, find 
    *        all the variables in this term.
    */
    set<Term*> all_variables() const;

    friend ostream& operator<<(ostream&, const Term&);
};

#endif
