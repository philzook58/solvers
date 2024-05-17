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

#include "PredicateIndex.hpp"

PredicateIndex::PredicateIndex()
: preds()
, name_index()
, next_index(0)
, next_definitional_id(0)
{
}
//----------------------------------------------------------------------
PredicateIndex::~PredicateIndex() {
    for (size_t i = 0; i < preds.size(); i++)
        delete preds[i];
}
//----------------------------------------------------------------------
Predicate* PredicateIndex::add_predicate(const string& name,
                                         Arity arity) {
    Predicate* new_pred = nullptr;
    auto i = name_index.find(PredIndexType(name, arity));
    if (i == name_index.end()) {
        new_pred = new Predicate(next_index++, name, arity);
        preds.push_back(new_pred);
        name_index.insert(PredMapType(PredIndexType(name, arity), new_pred));
    }
    else {
        new_pred = i->second;
    }
    return new_pred;
}
//----------------------------------------------------------------------
Predicate* PredicateIndex::find_predicate(const string& fun_name,
                                          Arity arity) {
    Predicate* pred = nullptr;
    auto i = name_index.find(PredIndexType(fun_name, arity));
    if (i != name_index.end())
        pred = i->second;
    else
        cerr << "That predicate name doesn't exist" << endl;
    return pred;
}
//----------------------------------------------------------------------
Arity PredicateIndex::find_maximum_arity() const {
  Arity result = 0;
  for (size_t i = 0; i < preds.size(); i++) {
    Arity current = preds[i]->get_arity();
    if (current > result)
      result = current;
  }
  return result;
}
//----------------------------------------------------------------------
bool PredicateIndex::true_false_added() const {
    auto i = name_index.find(PredIndexType(string("$true"), 0));
    if (i != name_index.end())
        return true;
    i = name_index.find(PredIndexType(string("$false"), 0));
    if (i != name_index.end())
        return true;
    return false;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const PredicateIndex& pi) {
    out << "Predicate Index" << endl;
    out << "---------------" << endl;
    for (Predicate* p : pi.preds) {
        out << *p << endl;
    }
    return out;
}
