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

#include "FunctionIndex.hpp"
//----------------------------------------------------------------------
FunctionIndex::FunctionIndex()
: funs()
, name_index()
, next_index(0)
, skolem_function_number(1)
{}
//----------------------------------------------------------------------
FunctionIndex::~FunctionIndex() {
    for (size_t i = 0; i < funs.size(); i++)
        delete funs[i];
}
//----------------------------------------------------------------------
Function* FunctionIndex::add_function(const string& name, Arity arity) {
    Function* new_fun = nullptr;
    auto i = name_index.find(FunIndexType(name, arity));
    if (i == name_index.end()) {
        new_fun = new Function(next_index++, name, arity);
        funs.push_back(new_fun);
        name_index.insert(FunMapType(FunIndexType(name, arity),
                                     new_fun));
    }
    else {
        new_fun = i->second;
    }
    return new_fun;
}
//----------------------------------------------------------------------
Function* FunctionIndex::make_skolem_function(Arity arity) {
  string name(params::unique_skolem_prefix);
  name += std::to_string(skolem_function_number++);
  return add_function(name, arity);
}
//----------------------------------------------------------------------
Function* FunctionIndex::find_function(const string& fun_name,
                                       Arity arity) {
    Function* fun = nullptr;
    auto i = name_index.find(FunIndexType(fun_name, arity));
    if (i != name_index.end())
        fun = i->second;
    else
        cerr << "That function name doesn't exist" << endl;
    return fun;
}
//----------------------------------------------------------------------
Arity FunctionIndex::find_maximum_arity() const {
  Arity result = 0;
  for (size_t i = 0; i < funs.size(); i++) {
    Arity current = funs[i]->get_arity();
    if (current > result)
      result = current;
  }
  return result;
}
//----------------------------------------------------------------------
Arity FunctionIndex::find_minimum_arity() const {
  Arity result = UINT32_MAX;
  for (size_t i = 0; i < funs.size(); i++) {
    Arity current = funs[i]->get_arity();
    if (current < result)
      result = current;
  }
  return result;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const FunctionIndex& fi) {
    out << "Function Index" << endl;
    out << "--------------" << endl;
    for (Function* f : fi.funs) {
        out << *f << endl;
    }
    return out;
}
