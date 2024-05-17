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

#ifndef FUNCTIONINDEX_HPP
#define FUNCTIONINDEX_HPP

#include<iostream>
#include<iomanip>
#include<string>
#include<vector>
#include<unordered_map>

#include "Function.hpp"
#include "FunctionHash.hpp"

using std::pair;
using std::setw;
using std::ostream;
using std::string;
using std::vector;
using std::unordered_map;
using std::cerr;
using std::endl;

using FunIndexType = pair<string, Arity>;
using FunMapType = pair<FunIndexType, Function*>;

/**
 * \brief Mechanism for looking after functions.
 *
 * Function names are only stored once, but functions can have 
 * the same name and a different arity.
 *
 * Somewhat more straightforward than looking after variables as 
 * there is no need for anonymous functions other than Skolem 
 * functions, and those do not get recycled. For the same reason, 
 * there is no need to take account of backtracking.
 *
 * You should *only* use this to make new Functions. As long as 
 * you do, it will take care of allocation and deallocation for 
 * you.
 */
class FunctionIndex {
private:
    /**
    * \brief Pointers to all the Functions used.
    */
    vector<Function*> funs;
    /**
    * \brief Fast lookup from name/arity to pointer to the Function.
    */
    unordered_map<pair<string, Arity>, Function*, fun_hash> name_index;
    /**
    * \brief keep track of ids for adding new Functions.
    */
    ID next_index;
    /**
    * \brief Automate the naming of Skolem functions.
    */
    uint32_t skolem_function_number;
public:
    FunctionIndex();
    /**
    * \brief As usual, trying to copy one of these is a really 
    * bad idea.
    */
    FunctionIndex(const FunctionIndex&) = delete;
    FunctionIndex(const FunctionIndex&&) = delete;
    FunctionIndex& operator=(const FunctionIndex&) = delete;
     FunctionIndex& operator=(const FunctionIndex&&) = delete;
    ~FunctionIndex();
    /**
    * \brief Self-explanatory.
    */
    size_t get_size() const { return funs.size(); }
    /**
    * \brief Add a new function to the index.
    *
    * If you add twice, the original will get re-used.
    *
    * @param name The name of the Function
    * @param arity The arity of the Function.
    */
    Function* add_function(const string&, Arity);
    /**
    * \brief Add a new Skolem function. Naming is automatic. 
    *
    * @param arity The arity of the new Skolem function. 
    */
    Function* make_skolem_function(Arity);
    /**
    * \brief Look up a stored Function by name and arity. 
    * 
    * @param fun_name Name of Function to find
    * @param arity Arity of Function to find
    */
    Function* find_function(const string&, Arity);
    /**
    * \brief Find the largest arity appearing for any Function 
    *        in the index.
    */
    Arity find_maximum_arity() const;
        /**
    * \brief Find the smallest arity appearing for any Function 
    *        in the index.
    */
    Arity find_minimum_arity() const;
    /**
    * \brief Access to pointers to Functions, but don't mess 
    *        with them!
    */
    Function* operator[](size_t i) { return funs[i]; }
    
    friend ostream& operator<<(ostream&, const FunctionIndex&);
};

#endif
