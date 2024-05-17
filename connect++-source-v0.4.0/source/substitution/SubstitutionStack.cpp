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

#include "SubstitutionStack.hpp"

//----------------------------------------------------------------------
void SubstitutionStack::push_all(Substitution& sub) {
  backtrack_points.push_back(next_index);
  for (SubPair& p : sub) {
    stack.push_back(p.first);
    next_index++;
  }
}
//----------------------------------------------------------------------
void SubstitutionStack::backtrack() {
  size_t previous_index = backtrack_points.back();
  backtrack_points.pop_back();
  while (next_index > previous_index) {
    next_index--;
    stack.back()->remove_substitution();
    stack.pop_back();
  }
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const SubstitutionStack& st) {
  out << st.stack.size();
  size_t bp_index = 0;
  for (size_t i = 0; i < st.stack.size(); i++) {
    if (i == st.backtrack_points[bp_index]) {
      out << "* ";
      bp_index++;
    }
    else
      out << "  ";
    out << st.stack[i]->to_string() << " -> "
        << st.stack[i]->get_subbed_term() << endl;//->to_string() << endl;
  }
  return out;
}