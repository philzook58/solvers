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

#include "StackItem.hpp"

//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const StackItemType& si) {
  switch (si) {
    case StackItemType::Start:
      out << "Start";
      break;
    case StackItemType::Axiom:
      out << "Axiom";
      break;
    case StackItemType::Reduction:
      out << "Reduction";
      break;
    case StackItemType::LeftBranch:
      out << "Left Branch";
      break;
    case StackItemType::RightBranch:
      out << "Right Branch";
      break;
    default:
      break;
  }
  return out;
}
//----------------------------------------------------------------------
void StackItem::restrict_backtrack() {
  /*
  * Implement the leanCop style restriction on backtracking.
  */
  actions.clear();
}
//----------------------------------------------------------------------
string StackItem::to_string_unsubbed() const {
  string result;
  result += "Stack item: ";
  switch (item_type) {
    case StackItemType::Start:
      result += "Start";
      break;
    case StackItemType::Axiom:
      result += "Axiom";
      break;
    case StackItemType::Reduction:
      result += "Reduction";
      break;
    case StackItemType::LeftBranch:
      result += "Left Branch";
      break;
    case StackItemType::RightBranch:
      result += "Right Branch";
      break;
    default:
      break;
  }
  result += " with ";
  result  += to_string(actions.size()) += " options\n";
  result += "C = ";
  result += c.to_string() += "\n";
  result += "P = ";
  result += p.to_string() += "\n";
  result += "L = ";
  result += l.to_string() += "\n";
  result += "Sub = ";
  result += sub.to_string() += "\n";
  result += "Depth: ";
  result += std::to_string(depth);
  return result;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const StackItem& si) {
  out << si.to_string_unsubbed() << endl;
  for (const InferenceItem& i : si.actions) {
    out << i << endl;
  }
  return out;
}