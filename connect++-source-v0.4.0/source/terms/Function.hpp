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

#ifndef FUNCTION_HPP
#define FUNCTION_HPP

#include<iostream>
#include<iomanip>
#include<string>

#include "LaTeXUtilities.hpp"
#include "BasicTypes.hpp"
#include "Parameters.hpp"
#include "vic_strings.hpp"
#include "cursor.hpp"

using std::string;
using std::ostream;
using std::endl;
using std::setw;

/**
* \brief Basic representation of functions.
*
* As with Variables, these are ultimately wrapped in a Term. These are
* also ultimately looked after by a FunctionIndex (which is a friend), 
* so there should not be any need to mess with them directly. (This 
* is why the constructors are private.)
*
* Note that this is somewhat simpler than Variable because you are 
* not dealing with substitutions: you only need id, name and arity. 
*/
class Function {
private:
    ID id;
    string name;
    Arity arity;
    /**
    * \brief Constructors are private as you only want 
    * the FunctionIndex to make these, and it's a friend.
    */
    Function() : id(0), name(), arity(0) {}
    Function(ID new_id) : id(new_id), name(), arity(0) {}
    Function(ID new_id, const string& new_name)
    : id(new_id), name(new_name), arity(0) {}
    Function(ID new_id, const string& new_name, Arity new_arity)
    : id(new_id), name(new_name), arity(new_arity) {}
public:
    friend class FunctionIndex;
    /**
    * \brief You want to inforce sharing, so don't allow copies to 
    *        be made.
    *
    * It should never be necessary to make copies, so this is to help 
    * the compiler to detect errors.
    */
    Function(const Function&) = delete;
    Function(const Function&&) = delete;
    Function& operator=(const Function&) = delete;
    Function& operator=(const Function&&) = delete;
    /**
    * \brief Most basic access function.
    */
    inline string get_name() const { return name; }
    /**
    * \brief Most basic access function.
    */
    inline Arity get_arity() const { return arity; }
    /**
    * \brief make a useable string representation.
    */
    string to_string() const;
    /**
    * \brief Make a useable LaTeX version.
    *
    * Assumes you are typesetting in Math Mode. Makes a limited
    * attempt to deal with special characters in the function 
    * name, but if your name is too fancy it's likely to produce 
    * something either ugly or unacceptable to LaTeX.
    */
    string make_LaTeX() const;

    friend ostream& operator<<(ostream&, const Function&);
};

#endif
