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

#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP

#include<iostream>
#include<string>
#include<vector>

#include "vic_strings.hpp"
#include "Term.hpp"

using std::pair;
using std::vector;
using std::string;
using std::ostream;
using std::endl;

/**
* \brief Unsurprisingly, a single substitution is just a pointer 
*        to the Variable being sustituted, and a pointer to 
*        the Term to use. 
*/
using SubPair = pair<Variable*, Term*>;

/**
* \brief General representation of a substitution.
*
* This is just a vector of individual substitutions, each a 
* pair of pointers, one to the Variable and one to the Term.
*
* Only very minimal methods are needed, essentially for 
* applying and removing the substitutions.
*/
class Substitution {
private:
    /**
    * \brief A single substitution is just a pointer 
    *        to the Variable being sustituted, and a pointer to 
    *        the Term to use. The Substitution is just a vector 
    *        of those.
    */
    vector<SubPair> sub;
public:
    /**
    * \brief Trivial constructor. 
    */
    Substitution() : sub() {}
    /**
    * \brief Trivial get method. 
    */
    size_t size() const { return sub.size(); }
    /**
    * \brief Add a pair to a substitution.
    *
    * @param v Pointer to the Variable. 
    * @param t Pointer to the Term.
    */
    void push_back(Variable*, Term*);
    /**
    * \brief Clear a substitution.
    */
    void clear() { sub.clear(); }
    /**
    * \brief Apply a substitution everywhere.
    *
    * Because of the way terms are represented this is easy, 
    * and involves updating a single pointer for each variable.
    */
    void apply() const;
    /**
    * \brief Remove a substitution everywhere.
    *
    * Because of the way terms are represented this is easy, 
    * and involves updating a single pointer for each variable.
    */
    void backtrack() const;
    /**
    * \brief Make a string representation.
    * 
    * @param subbed Implement substitutions if true.
    */
    string to_string(bool = false) const;
    /**
    * \brief Make a useable LaTeX representation.
    *
    * Assumes you're in Math Mode. 
    *
    * @param subbed Implement substitutions if true.
    */
    string make_LaTeX(bool = false) const;
    /** 
    * \brief Iteration is just iteration over the vector of pairs.
    */
    vector<SubPair>::iterator begin() { return sub.begin(); }
    /** 
    * \brief Iteration is just iteration over the vector of pairs.
    */
    vector<SubPair>::iterator end() { return sub.end(); }
    /** 
    * \brief Iteration is just iteration over the vector of pairs.
    */
    vector<SubPair>::const_iterator cbegin() { return sub.cbegin(); }
    /** 
    * \brief Iteration is just iteration over the vector of pairs.
    */
    vector<SubPair>::const_iterator cend() { return sub.cend(); }

    friend ostream& operator<<(ostream&, const Substitution&);
};

#endif
