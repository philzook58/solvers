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

#include "Lemmata.hpp"

//----------------------------------------------------------------------
void Lemmata::push_back(const Literal& l) {
  ls.push_back(l);
  len++;
}
//----------------------------------------------------------------------
void Lemmata::find_initial_lemmata(vector<InferenceItem>& inf, Clause& c) {
  if (len == 0)
    return;
  if (c.size() == 0) {
    cerr << "You shouldn't be looking for lemmata with an empty clause" << endl;
    return;
  }
  size_t lemmata_index = 0;
  const Literal& lit1 = c[0];
  for (Literal& lit2 : ls) {
    if (lit1.subbed_equal(&lit2)) {
      inf.push_back(InferenceItem(InferenceItemType::Lemma, 
        lit1, 
        0, 
        lemmata_index));
      // If you've found a way of applying the rule them it 
      // doesn't make any sense to continue.
      return;
    }
    lemmata_index++;
  }
}
//----------------------------------------------------------------------
void Lemmata::find_all_lemmata(vector<InferenceItem>& inf, Clause& c) {
  if (len == 0)
    return;
  if (c.size() == 0) {
    cerr << "You shouldn't be looking for lemmata with an empty clause" << endl;
    return;
  }
  size_t i = 0;
  for (const Literal& lit1 : c) {
    size_t lemmata_index = 0;
    for (Literal& lit2 : ls) {
      if (lit1.subbed_equal(&lit2)) {
        inf.push_back(InferenceItem(InferenceItemType::Lemma, 
          lit1, 
          i, 
          lemmata_index));
        // If you've found a way of applying the rule them it 
        // doesn't make any sense to continue.
        break;
      }
      lemmata_index++;
    }
    i++;
  }
}
//----------------------------------------------------------------------
string Lemmata::to_string(bool subbed) const {
  commas::comma com(ls.size());
  string result;
  result += "[ ";
  for (const Literal& l : ls) {
        result += l.to_string(subbed);
        result += com();
  }
  result += " ]";
  return result;
}
//----------------------------------------------------------------------
string Lemmata::make_LaTeX(bool subbed) const {
  commas::comma com(ls.size());
  string s ("\\textcolor{cyan}{[ }");
  for (const Literal& l : ls) {
        s += l.make_LaTeX(subbed);
        s += com();
  }
  s += "\\textcolor{cyan}{]}";
  return s;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Lemmata& l) {
  out << "Lemmata:" << endl;
  out << "--------" << endl;
  out << l.to_string();
  return out;
}