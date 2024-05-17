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

#ifndef VARIABLEINDEX_HPP
#define VARIABLEINDEX_HPP

#include<iostream>
#include<iomanip>
#include<string>
#include<sstream>
#include<vector>
#include<unordered_map>

#include "Variable.hpp"

using std::string;
using std::pair;
using std::vector;
using std::iostream;
using std::endl;
using std::cerr;
using std::unordered_map;
using std::istringstream;
using std::to_string;

using MapType = pair<string, Variable*>;

/**
 * \brief Storage of named variables, and management of new, 
 *        anonymous variables.
 *
 * Variables are only stored once, and I want backtracking to 
 * be easy while recycling old anonymous variables. You should 
 * only add named variables once, at the beginning of the 
 * process.
 *
 * You should only make variables using this index. If you do 
 * then it takes care of allocation/deallocation for you.
 */
class VariableIndex {
private:
    /**
    * \brief All the variables made, named and anonymous. 
    */
    vector<Variable*> vars;
    /**
    * \brief Fast lookup of Variables by name.
    */
    unordered_map<string, Variable*> name_index;
    /**
    * \brief Keep track of automatically generated Variable 
             indices.
    */
    ID next_index;
    /**
    * \brief When converting to CNF you need new, unique 
    *        variables, but they need to be treated separately 
    *        from anonymous variables.
    */
    ID next_unique_index;
    /**
    * \brief Set after you've added all the named variables 
    *        for the problem. 
    *
    * Allows you to know where in vars the problem variables 
    * stop and the anonymous variables start.
    */
    ID first_anon_variable;
    /**
    * \brief Keep track of how many anonymous Variables you 
    * currently have available.. 
    */
    ID highest_anon_variable;
    /**
    * \brief Set after you've added all the named variables 
    *        for the problem. 
    *
    * Used to detect erronious addition of further named 
    * Variables.
    */
    bool all_names_added;
    /**
    * \brief Backtrack points stored as indices in the vars 
    *        vector.
    */
    vector<ID> backtrack_points;
public:
    VariableIndex();
    ~VariableIndex();
    /**
     * \brief Copying this would be a very silly idea, so explicitly
     *        disallow it.
     *
     * As usual, let the compiler be your friend.
     */
    VariableIndex(const VariableIndex&) = delete;
    VariableIndex(const VariableIndex&&) = delete;
    VariableIndex& operator=(const VariableIndex&) = delete;
    VariableIndex& operator=(const VariableIndex&&) = delete;
    /**
     * \brief Straightforward access function.
     */
    inline ID get_next_index() const { return next_index; }
    /**
     * \brief Straightforward access function.
     */
    inline ID get_first_anon_variable() const { return first_anon_variable; }
    /**
     * \brief Straightforward access function.
     */
    inline ID get_highest_anon_variable() const { return highest_anon_variable; }
    /**
     * \brief Straightforward access function.
     */
    inline bool get_all_names_added() const { return all_names_added; }
    /**
     * \brief Straightforward access function.
     */
    inline size_t get_num_backtracks() const { return backtrack_points.size(); }
    /**
     * \brief Add a variable with the specified name to the index.
     *
     * Only allow a named variable to be added once, and before any
     * anonymous variables. If you add something twice you'll just get
     * a pointer to the first copy.
     *
     * @param name Name of Variable to add
     */
    Variable* add_named_var(const string&);
    /**
     * \brief Add an anonymous variable.
     *
     * Anonymous variables are recycled after backtracking.
     * Also denies addition of new named variables if you didn't do
     * that yourself. Anonymous variables do get names  of the form 
     * "_next_index" but are not currently included in the map as 
     * they can be found by other means if you absolutely need to, 
     * which you shouldn't.
     */
    Variable* add_anon_var();
    /**
    * \brief Add a unique variable when converting to CNF.
    *
    * Does not immediately deny addition of further named 
    * variables.
    */
    Variable* add_unique_var();
    /**
      * \brief Look up a variable by name.
      *
      * @param var_name Name of Variable to find.
      */
    Variable* find_variable(const string&);
    /**
     * \brief Call this to indicate that only anonymous variables 
     * can now be created.
     *
     * Note: this also adds a backtrack point at the first 
     * (currently not created) anonymous variable.
     */
    void set_all_names_added();
    /**
     * \brief Undo all substitutions made, to anything, ever.
     */
    void clear_substitutions();
    /**
     * \brief Add a backtrack point.
     *
     * This is straightforward. All we have to do is remember a 
     * starting point so that all anonymous variables after that 
     * can easily be reused.
     *
     * It is the responsibility of the user to insert and maintain 
     * an initial backtrack point at the first anonymous variable.
     */
    void add_backtrack_point();
    /**
    * \brief Same as add_backtrack_point, but return an identifier 
    *        allowing multiple levels of backtracking using 
    *        backtrack_to_named_point.
    */
    ID add_named_backtrack_point();
    /**
     * \brief Backtrack to the last marker.
     *
     * This is straightforward. Substitutions do *not* have to be 
     * undone here as that will happen if a variable is reused.
     */
    void backtrack();
    /**
    * \brief Backtrack, possibly multiple times, to the 
    *        specified point.
    */
    void backtrack_to_named_point(ID);
    /**
     * \brief Get rid of all the markers used for backtracking.
     *
     * Clears all backtracking information.
     */
    void reset();

    friend ostream& operator<<(ostream&, const VariableIndex&);
};

#endif
