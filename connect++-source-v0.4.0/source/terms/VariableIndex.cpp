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

#include "VariableIndex.hpp"

//----------------------------------------------------------------------
VariableIndex::VariableIndex()
: vars()
, name_index()
, next_index(0)
, next_unique_index(0)
, first_anon_variable(0)
, highest_anon_variable(0)
, all_names_added(false)
, backtrack_points()
{}
//----------------------------------------------------------------------
VariableIndex::~VariableIndex() {
    for (size_t i = 0; i < vars.size(); i++)
        delete vars[i];
}
//----------------------------------------------------------------------
Variable* VariableIndex::add_named_var(const string& name) {
    Variable* new_var = nullptr;
    if (!all_names_added) {
        auto i = name_index.find(name);
        if (i == name_index.end()) {
            new_var = new Variable(next_index++, name);
            vars.push_back(new_var);
            name_index.insert(MapType(name, new_var));
        }
        else {
            new_var = i->second;
        }
    }
    else {
        cerr << "You can't add any more named variables." << endl;
    }
    return new_var;
}
//----------------------------------------------------------------------
void VariableIndex::set_all_names_added() {
  all_names_added = true;
  first_anon_variable = next_index;
}
//----------------------------------------------------------------------
void VariableIndex::clear_substitutions() {
  for (size_t i = 0; i < vars.size(); i++)
    vars[i]->remove_substitution();
}
//----------------------------------------------------------------------
Variable* VariableIndex::add_anon_var() {
    if (!all_names_added) {
        set_all_names_added();
    }
    Variable* new_var = nullptr;
    // You can recycle an anonymous variable that was used 
    // earlier then freed up under backtracking.
    if (next_index <= highest_anon_variable) {
        new_var = vars[next_index++];
        new_var->remove_substitution();
    }
    // You need to actually generate a new anonymous variable.
    else {
        highest_anon_variable = next_index;
        string name("_");
        name += to_string(next_index);
        new_var = new Variable(next_index++, name);
        vars.push_back(new_var);
    }
    return new_var;
}
//----------------------------------------------------------------------
Variable* VariableIndex::add_unique_var() {
    string name(params::unique_var_prefix);
    name += to_string(next_unique_index);
    next_unique_index++;
    return add_named_var(name);
}
//----------------------------------------------------------------------
Variable* VariableIndex::find_variable(const string& var_name) {
    Variable* var = nullptr;
    istringstream st(var_name);
    char c;
    st >> c;
    if (c == '_') {
        ID id;
        st >> id;
        if (id < next_index)
            var = vars[id];
        else
            cerr << "That anonymous variable doesn't exist" << endl;
    }
    else {
        auto i = name_index.find(var_name);
        if (i != name_index.end())
            var = i->second;
        else
            cerr << "That named variable doesn't exist" << endl;
    }
    return var;
}
//----------------------------------------------------------------------
void VariableIndex::add_backtrack_point() {
    backtrack_points.push_back(next_index);
}
//----------------------------------------------------------------------
ID VariableIndex::add_named_backtrack_point() {
    backtrack_points.push_back(next_index);
    return next_index;
}
//----------------------------------------------------------------------
void VariableIndex::backtrack() {
    if (backtrack_points.size() > 0) {
        next_index = backtrack_points.back();
        backtrack_points.pop_back();
    }
    else
        cerr << "There's nowhere left to backtrack to." << endl;
}
//----------------------------------------------------------------------
void VariableIndex::backtrack_to_named_point(ID id) {
    while (backtrack_points.back() != id) {
        backtrack_points.pop_back();
    }
    next_index = id;
    backtrack_points.pop_back();
}
//----------------------------------------------------------------------
void VariableIndex::reset() {
  if (all_names_added) {
    backtrack_points.clear();
    next_index = first_anon_variable;
  }
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const VariableIndex& vi) {
    out << "Variable Index" << endl;
    out << "--------------" << endl;
    ID id = 0;
    auto i = vi.backtrack_points.begin();
    for (Variable* v : vi.vars) {
        if (id == vi.next_index)
            break;
        out << *v << " ";
        if (i != vi.backtrack_points.end()) {
            if (id == *i) {
                out << " <- Backtrack point";
                i++;
            }
        }
        out << endl;
        id++;
    }
    out << "Highest anon id: " << vi.highest_anon_variable;
    return out;
}
