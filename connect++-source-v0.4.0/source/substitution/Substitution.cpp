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

#include "Substitution.hpp"

//----------------------------------------------------------------------
string Substitution::to_string(bool subbed) const {
    string result("\n");
    for (SubPair s : sub) {
        result += s.first->to_string();
        result += " <- ";
        result += s.second->to_string(subbed);
        result += '\n';
    }
    return result;
}
//----------------------------------------------------------------------
string Substitution::make_LaTeX(bool subbed) const {
  commas::comma com(sub.size());
  string result ("( ");
  for (SubPair s : sub) {
    result += s.first->make_LaTeX();
    result += " \\leftarrow ";
    result += s.second->make_LaTeX(subbed);
    result += com();
  }
  result += " )";
  return result;
}
//----------------------------------------------------------------------
void Substitution::push_back(Variable* v, Term* t) {
    sub.push_back(SubPair(v, t));
}
//----------------------------------------------------------------------
void Substitution::apply() const {
    for (SubPair s : sub) {
        s.first->substitute(s.second);
    }
}
//----------------------------------------------------------------------
void Substitution::backtrack() const {
    for (SubPair s : sub) {
        s.first->remove_substitution();
    }
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Substitution& s) {
  colour_string::ColourString cs(params::use_colours);
  for (SubPair sp : s.sub) {
      out << cs("(").orange() << sp.first->to_string();
      out << cs(" -> ").orange();
      out << sp.second->to_string() << cs(") ").orange();
  }
  return out;
}
