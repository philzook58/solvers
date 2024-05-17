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

#ifndef LITERAL_HPP
#define LITERAL_HPP

#include<iostream>
#include<iomanip>
#include<string>
#include<vector>
#include<set>
#include<unordered_map>

#include "TermIndex.hpp"
#include "Predicate.hpp"

using std::vector;
using std::string;
using std::set;
using std::unordered_map;
using std::ostream;
using std::endl;

/** 
* \brief Basic representation of literals, bundling together 
*        (pointers to) a Predicate, a collection of arguments 
*        each a (pointer to a) Term, an arity and a polarity.
*/
class Literal {
private:
    Predicate* pred;
    vector<Term*> args;
    Arity arity;
    bool polarity;
public:
    Literal() : pred(nullptr), args(), arity(0), polarity(true) {}
    /**
    * \brief Construct a Literal from existing material.
    *
    * @param new_p Pointer to a Predicate
    * @param new_args Reference to a vector of pointers to Terms
    * @param new_ar New value for arity
    * @param new_pol Set true for positive literal, false for 
    *                negative (negated).
    */
    Literal(Predicate*, const vector<Term*>&, Arity, bool);
    /**
    * \brief Basic get method.
    */
    inline Predicate* get_pred() const { return pred; }
    /**
    * \brief Basic get method.
    */
    inline Arity get_arity() const { return arity; }
    /**
    * \brief Basic get method.
    */
    inline bool get_polarity() const { return polarity; }
    /**
    * \brief Basic get method.
    */
    inline const vector<Term*>& get_args() const { return args; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline bool is_positive() const { return polarity; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline bool is_negative() const { return !polarity; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline void make_positive() { polarity = true; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline void make_negative() { polarity = false; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline void invert() { polarity = !polarity; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline void make_empty() { pred = nullptr; }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    inline bool is_empty() const { return (pred == nullptr); }
    /**
    * \brief Basic manipulation - entirely self-explanatory.
    */
    void clear() { pred = nullptr; args.clear(), arity = 0; polarity = true; } 
    /**
    * \brief Turn a Literal into an array index.
    *
    * This is straightforward: positive literals have even 
    * indices and negative literals odd.
    */
    inline size_t get_pred_as_index() const {
        size_t index = pred->get_ID() << 1;
        if (!polarity)
            index |= 0x00000001;
        return index;
    };
    /**
    * \brief Is this equivalent to $true?
    */
    bool is_true() const;
    /**
    * \brief Is this equivalent to $false?
    */
    bool is_false() const;
    /**
    * \brief Does this Literal contain the specified variable?
    *
    * @param v Pointer to Variable to search for.
    */
    bool contains_variable(Variable*) const;
    /**
    * \brief Literals can only be unified if the polarity and 
    * actual predicate are the same.
    *
    * One does not generally expect literals to be differentiated
    * by arity, but it's possible so we check that too.
    *
    * @param l Pointer to Literal to compare with.
    */
    bool is_compatible_with(const Literal*) const;
    /**
    * \brief Test whether one literal is exactly the same 
    *        as another, with the exception of the polarity.
    *
    * This also requires that the argument lists are the same.
    */
    bool is_complement_of(const Literal&) const;
    /**
    * \brief Get the predicate and polarity as a string.
    */
    string get_small_lit() const;
    /**
    * \brief Full conversion of Literal to string.
    *
    * @param subbed Implement substitutions if true.
    */
    string to_string(bool = false) const;
    /**
    * \brief Convert to a string in a format readable by Prolog. 
    *
    * Does not apply substitutions.
    */
    string to_prolog_string() const;
    /**
    * \brief Convert to a string in a format compatible 
    * with the TPTP. 
    *
    * Does not apply substitutions.
    */
    string to_tptp_string() const;
    /**
    * \brief Make a useable LaTeX version.
    *
    * Assumes you are typesetting in Math Mode.
    *
    * @param subbed Implement substitutions if true.
    */
    string make_LaTeX(bool = false) const;
    /**
    * \brief Equality without taking account of substutions.
    *
    * @param l Literal to compare with.
    */
    bool operator==(const Literal&) const;
    /**
    * \brief Equality, taking account of substitutions.
    *
    * @param l Pointer to Literal to compare with
    */
    bool subbed_equal(Literal*) const;
    /**
    * \brief Make a copy of the Literal but with a new set 
    *        of variables.
    *
    * All the heavy lifting is done by the Term class. 
    * Essentially just initializes an unordered_map and 
    * calls the corresponging helper.
    *
    * @param vi Reference to the VariableIndex
    * @param ti Reference to the TermIndex 
    */
    Literal make_copy_with_new_vars(VariableIndex&, TermIndex&) const;
    /**
    * \brief Helper function for make_copy_with_new_vars.
    *
    * Iterates over the args using the corresponding method in 
    * the Term class to do the real work.
    * 
    * @param vi Reference to the VariableIndex
    * @param ti Reference to the TermIndex 
    * @param new_vars Reference to an unordered_map from pointers 
    *                 to Variables, to pointers 
    *                 to Terms. Initially empty. On completion 
    *                 contains a map from variables, to the terms 
    *                 corresponding to the new variables made to 
    *                 replace them. 
    */
    Literal make_copy_with_new_vars_helper(VariableIndex&,
                                           TermIndex&,
                                           unordered_map<Variable*,Term*>&) const;
    /**
    * \brief Replace one variable with another throughout.
    *
    * Iterate over the args using the replace_variable_in_term
    * method in TermIndex to do the real work.
    *
    * @param new_var Pointer to new Variable
    * @param old_var Pointer to old Variable
    * @param ti Pointer to the TermIndex
    */
    void replace_variable(Variable*, Variable*, TermIndex*);
    /**
    * \brief Replace one variable with a term throughout.
    *
    * Iterate over the args using the 
    * replace_variable_in_term_with_term
    * method in TermIndex to do the real work.
    *
    * @param new_term Pointer to new Term
    * @param old_var Pointer to old Variable
    * @param ti Pointer to the TermIndex
    */
    void replace_variable_with_term(Term*, Variable*, TermIndex*);

    friend ostream& operator<<(ostream&, const Literal&);
};

#endif
