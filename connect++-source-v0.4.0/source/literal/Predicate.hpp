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

#ifndef PREDICATE_HPP
#define PREDICATE_HPP

#include<iostream>
#include<iomanip>
#include<string>
#include<vector>

#include "LaTeXUtilities.hpp"
#include "BasicTypes.hpp"
#include "Parameters.hpp"
#include "vic_strings.hpp"

using std::string;
using std::ostream;
using std::endl;
using std::setw;

/**
* \brief Basic representation of predicates: here just names, 
*        ids and arities.
*
* This really just acts as identification. See the Literal class, 
* which is where Predicate and Term get connected together. (No 
* pun intended.)
*/
class Predicate {
private:
    ID id;
    string name;
    Arity arity;
    /**
    * \brief These should only be constructed by PredicateIndex, 
    *        which is a friend, and the constructors are 
    *        therefore private.
    */
    Predicate() : id(0), name(), arity(0) {}
    Predicate(ID new_id) : id(new_id), name(), arity(0) {}
    Predicate(ID new_id, const string& new_name)
    : id(new_id), name(new_name), arity(0) {}
    Predicate(ID new_id, const string& new_name, Arity new_arity)
    : id(new_id), name(new_name), arity(new_arity) {}
public:
    friend class PredicateIndex;
    /**
    * \brief Don't allow copies of these to be made.
    *
    * As usual, let the compiler find any errors because 
    * you should never need to make copies this way.
    */
    Predicate(const Predicate&) = delete;
    Predicate(const Predicate&&) = delete;
    Predicate& operator=(const Predicate&) = delete;
    Predicate& operator=(const Predicate&&) = delete;
    /**
    * \brief Basic get method.
    */
    inline ID get_ID() const { return id; }
     /**
    * \brief Basic get method.
    */
    inline string get_name() const { return name; }
     /**
    * \brief Basic get method.
    */
    inline Arity get_arity() const { return arity; }
    /**
    * \brief Do the name and the arity of a pair of 
    *        Predicates both match?
    *
    * @param p2 Predicate to copare with
    */
    bool is_compatible_with(const Predicate&) const;
    /**
    * \brief Converting to a string just gives you the name.
    */
    string to_string() const;
    /**
    * \brief Make a useable LaTeX version.
    *
    * Assumes you are typesetting in Math Mode.
    */
    string make_LaTeX() const;

    friend ostream& operator<<(ostream&, const Predicate&);
};

#endif
