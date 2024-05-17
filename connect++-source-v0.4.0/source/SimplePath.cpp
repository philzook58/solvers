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

#include "SimplePath.hpp"

//----------------------------------------------------------------------
SimplePath::SimplePath(uint32_t num_predicates)
: path()
, num_preds(num_predicates)
, len(0)
{}
//----------------------------------------------------------------------
void SimplePath::clear() {
    path.clear();
    len = 0;
}
//----------------------------------------------------------------------
void SimplePath::push(const Literal& lit) {
    path.push_back(lit);
    len++;
}
//----------------------------------------------------------------------
Literal SimplePath::back() const {
  if (len > 0)
    return path.back();
  else {
    cerr << "Stop it - the path is empty!" << endl;
    Literal result;
    return result;
  }
}
//----------------------------------------------------------------------
void SimplePath::pop() {
  if (len > 0) {
    path.pop_back();
    len--;
  }
  else {
    cerr << "Stop it - the path is empty!" << endl;
  }
}
//----------------------------------------------------------------------
bool SimplePath::test_for_regularity(Clause& c) const {
  for (const Literal& lit : path) {
    for (size_t i = 0; i < c.size(); i++)
      if (lit.subbed_equal(&(c[i])))
        return false;
  }
  return true;
}
//----------------------------------------------------------------------
// It's up to you to decide if you want to clear the result first.
// Note that you only need to find the substitutions, but the
// index in the path is also stored for proof checking.
//----------------------------------------------------------------------
void SimplePath::find_reductions(Unifier& u,
                           vector<InferenceItem>& result,
                           const Literal& lit,
                           LitNum index) {
  Literal neg_lit(lit);
  neg_lit.invert();
  size_t path_i = 0;
  for (const Literal& lit2 : path) {
    if (!neg_lit.is_compatible_with(&lit2)) {
      path_i++;
      continue;
    }
    UnificationOutcome outcome = u(neg_lit, lit2);
    if (outcome == UnificationOutcome::Succeed) {
      result.push_back(
        InferenceItem(InferenceItemType::Reduction,
            lit, index, 0, 0,
            u.get_substitution(),
            path_i));
      u.backtrack();
    }
    path_i++;
  }
}
//----------------------------------------------------------------------
void SimplePath::find_limited_reductions(Unifier& u,
                         vector<InferenceItem>& result,
                         Clause& c) {
  // Don't waste your time if the path is empty.
  if (len == 0)
    return;
  if (c.size() == 0) {
    cerr << "You shouldn't be looking for reductions with an empty clause" << endl;
    return;
  }
  find_reductions(u, result, c[0], 0);
}
//----------------------------------------------------------------------
void SimplePath::find_all_reductions(Unifier& u,
                         vector<InferenceItem>& result,
                         Clause& c) {
  // Don't waste your time if the path is empty.
  if (len == 0)
    return;
  if (c.size() == 0) {
    cerr << "You shouldn't be looking for reductions with an empty clause" << endl;
    return;
  }
  for (size_t index = 0; index < c.size(); index++) 
    find_reductions(u, result, c[index], index);
}
//----------------------------------------------------------------------
void SimplePath::show_path_only(ostream& out) {
  out << "Path: ";
  for (auto l : path)
    out << l << " ";
  out << endl;
}
//----------------------------------------------------------------------
string SimplePath::to_string(bool subbed) const {
  commas::comma com(path.size());
  string result;
  result += "[ ";
  for (const Literal& p : path) {
        result += p.to_string(subbed);
        result += com();
  }
  result += " ]";
  return result;
}
//----------------------------------------------------------------------
string SimplePath::make_LaTeX(bool subbed) const {
  string s ("\\textcolor{green}{[ }");
  commas::comma com(path.size());
  for (const Literal& p : path) {
        s += p.make_LaTeX(subbed);
        s += com();
  }
  s += "\\textcolor{green}{]}";
  return s;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const SimplePath& p) {
    out << "Path:" << endl;
    out << "-----" << endl;
    out << p.to_string();
    return out;
}
