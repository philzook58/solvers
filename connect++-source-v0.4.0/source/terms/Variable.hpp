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

#ifndef VARIABLE_HPP
#define VARIABLE_HPP

#include<iostream>
#include<iomanip>
#include<string>
#include<vector>

#include "LaTeXUtilities.hpp"
#include "Function.hpp"

class Term;

using std::string;
using std::ostream;

/**
 * \brief Basic representation of variables.
 *
 * This way of treating variables makes substitution and the removal
 * thereof extremely easy. BUT, you have to be somewhat careful, because
 * once substituted you may no longer have a variable.
 *
 * A Variable has an id and a namem Substitution is by way 
 * of setting the substitution pointer from nullptr to the 
 * address of a Term.
 *
 * Some of the implementation is in Term.cpp in order to allow the
 * compiler to do things in the right order.
 *
 * You should *never* try to construct one of these yourself. Only 
 * do it by way of the VariableIndex.
 */
class Variable {
private:
    ID id;
    string name;
    Term* substitution;
     /**
     * \brief Constructors: you can *only* construct un-substituted 
     *        variables.
     *
     * These are private because in order to inforce sharing 
     * the only place you should ever construct one is in the 
     * VariableIndex, which is a friend.
     */
    Variable() : id(0), name(), substitution(nullptr) {}
    Variable(ID new_id) : id(new_id), name(), substitution(nullptr) {}
    Variable(ID new_id, const string& new_name)
    : id(new_id), name(new_name), substitution(nullptr) {}
public:
    friend class VariableIndex;
    /**
     * \brief Explicitly disallow copying as this is a very bad idea.
     *
     * You should never have to do this, and by explicitly 
     * disallowing it we help the compiler to find our errors 
     * for us.
     */
    Variable(const Variable&) = delete;
    Variable(const Variable&&) = delete;
    Variable& operator=(const Variable&) = delete;
    Variable& operator=(const Variable&&) = delete;
    //----------------------------------------------------------------------
    /**
    * \brief Self-explanatory access function.
    */
    inline ID get_id() const { return id; }
    //----------------------------------------------------------------------
    /**
    * \brief Self-explanatory access function. 
    *
    * Only return the variable name -- do not follow substitutions.
    */
    inline string get_name() const { return name; }
    //----------------------------------------------------------------------
    /**
    * \brief Convert to a (coloured) string. 
    * 
    * @param subbed Include effect of substitution if true.
    */
    string to_string(bool = false) const;
    //----------------------------------------------------------------------
    /**
    * \brief Self-explanatory.
    */
    inline bool is_subbed() const { return (substitution != nullptr); }
    //----------------------------------------------------------------------
    /**
    * \brief Self-explanatory.
    */
    inline Term* get_subbed_term() const { return substitution; }
    //----------------------------------------------------------------------
    /**
    * \brief Self-explanatory, but be careful!
    *
    * As long as your Term* pointers are *only* generated buy the 
    * TermIndex, then you don't have to worry about memory allocation 
    * or de-allocation. 
    *
    * If you did a "new Term" anywhere yourself then you must live 
    * with the consequences.
    */
    inline void remove_substitution() { substitution = nullptr; }
    //----------------------------------------------------------------------
    /**
    * \brief Self-explanatory, but be careful!
    *
    * As long as your Term* pointers are *only* generated buy the 
    * TermIndex, then you don't have to worry about memory allocation 
    * or de-allocation. 
    *
    * If you did a "new Term" anywhere yourself then you must live 
    * with the consequences.
    *
    * @param t Pointer to Term to substitute.
    */
    inline void substitute(Term* t) { substitution = t; }
    //----------------------------------------------------------------------
    /**
     * \brief Is the variable now a function, taking substitution 
     *        into account?
     *
     * Note that this it false if the variable is unsubstituted.
     */
    bool subbed_is_function() const;
    //----------------------------------------------------------------------
    /**
     * \brief Is the variable still in fact a variable, taking 
     *        substitution into account?
     *
     * Note that this it true if the variable is unsubstituted.
     */
    bool subbed_is_variable() const;
    //----------------------------------------------------------------------
    /**
     * \brief If the variable is unsubbed then return "this"; 
     *        otherwise a pointer to the variable at the end of 
     *        a chain of substitutions of variables for variables.
     *
     * You should probably only call this if you know the substitution
     * is a chain of variables. (Otherwise you're getting a nullptr and 
     * an error message.)
     */
    Variable* subbed_variable() const;
    //----------------------------------------------------------------------
    /**
     * \brief Does the substitution turn the variable into something
     *        that includes the variable passed?
     *
     * Note that this acts on the eventual term, so if you look
     * for something that has itself been subbed then the answer is
     * "no".
     *
     * @param v2 Pointer to Variable to search for.
     */
    bool contains_variable(Variable*) const;
    //----------------------------------------------------------------------
    /**
     * \brief If there is a chain of substitutions ending in a function,
     *        find that function.
     */
    Function* get_subbed_f() const;
    //----------------------------------------------------------------------
    /**
     * \brief If there is a chain of substitutions ending in a function,
     *        find that function's arity.
     */
    Arity get_subbed_arity() const;
    //----------------------------------------------------------------------
    /**
    * \brief It may be that there is a chain of substitutions 
    *        attached to this variable: skip the leading ones.
    *
    * When doing unification we actually want a pointer
    * either to the final variable in a chain or to the
    * first term that's a function. This returns it.
    */
    Term* skip_leading_variables() const;
    //----------------------------------------------------------------------
    /**
    * \brief Convert the Variable to a useable LaTeX representation.
    *
    * Note that this makes a limited attempt to deal with all situations.
    * Anonymous variables will work fine, but if your named
    * variables have symbols that need an escape or similar it may not
    * work as expected.
    *
    * Assumes that the output will be typeset in math mode. Parameter
    * implements substitutions if true.
    *
    * @param subbed Include effect of substitution if true.
    */
    string make_LaTeX(bool = false) const;
    //----------------------------------------------------------------------

    friend ostream& operator<<(ostream&, const Variable&);
};

#endif
