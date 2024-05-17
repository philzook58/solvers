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

#include "Clause.hpp"

std::mt19937 Clause::d(params::random_seed);

//----------------------------------------------------------------------
bool Clause::is_positive() const {
#ifdef DEBUGMESSAGES
    if (c.size() == 0)
        cerr << "Don't check an empty clause for positivity" << endl;
#endif
  for (size_t i = 0; i < c.size(); i++) {
    if (c[i].is_negative())
      return false;
  }
  return true;
}
//----------------------------------------------------------------------
bool Clause::is_negative() const {
#ifdef DEBUGMESSAGES
    if (c.size() == 0)
        cerr << "Don't check an empty clause for negativity" << endl;
#endif
  for (size_t i = 0; i < c.size(); i++) {
    if (c[i].is_positive())
      return false;
  }
  return true;
}
//----------------------------------------------------------------------
 void Clause::remove_duplicates() {
    size_t s = c.size();
    if (s < 2)
        return;
    vector<Literal> new_c;
    for (size_t i = 0; i < s - 1; i++) {
        bool found = false;
        for (size_t j = i+1; j < s; j++ ) {
            if (c[i] == c[j]) {
                found = true;
                break;
            }
        }
        if (!found) 
            new_c.push_back(c[i]);
    }
    new_c.push_back(c[s - 1]);
    c = new_c;
 }
//----------------------------------------------------------------------
bool Clause::has_complementary_literals() const {
    size_t s = c.size();
    if (s < 2) 
        return false;
    for (size_t i = 0; i < s - 1; i++) {
        for (size_t j = i+1; j < s; j++) {
            if (c[i].is_complement_of(c[j])) 
                return true;
        }
    }
    return false;
}
//----------------------------------------------------------------------
void Clause::add_lit(const Literal& l) {
    for (size_t i = 0; i < c.size(); i++)
        if (c[i] == l) {
#ifdef DEBUGMESSAGES
            cerr << "Don't duplicate Literals in a clause!" << endl;
#endif
            return;
        }
    c.push_back(l);
}
//----------------------------------------------------------------------
Clause Clause::make_copy_with_new_vars(VariableIndex& vi, TermIndex& ti) const {
#ifdef DEBUGMESSAGES
    if (c.size() == 0)
        cerr << "You are making a copy of an empty clause" << endl;
#endif
    vector<Literal> new_lits;
    unordered_map<Variable*,Term*> new_vars;
    for (size_t i = 0; i < c.size(); i++)
        new_lits.push_back(c[i].make_copy_with_new_vars_helper(vi, ti, new_vars));
    return Clause(new_lits);
}
//---------------------------------------------------------------------------
 SimplificationResult Clause::simplify() {
    // Do this first in case someone has made a clause with 
    // both $true and $false in it.
    vector<Literal> new_clause;
    bool clause_is_true = false;
    for (Literal& lit : c)  {
        if (lit.is_false()) 
            continue;
        if (lit.is_true()) {
            clause_is_true = true;
            continue;
        }
        new_clause.push_back(lit);
    }
    c = new_clause;
    if (clause_is_true)
        return SimplificationResult::Tautology;
    remove_duplicates();
    if (c.size() == 0)
        return SimplificationResult::Contradiction;
    if (has_complementary_literals())
        return SimplificationResult::Tautology;
    return SimplificationResult::OK;
}
//----------------------------------------------------------------------
void Clause::drop_literal(LitNum l) {
    if (c.size() == 0) {
#ifdef DEBUGMESSAGES
        cerr << "Can't drop_literal from empty clause" << endl;
#endif
        return;
    }
    if (l > c.size() - 1) {
#ifdef DEBUGMESSAGES
        cerr << "drop_literal argument is out of range" << endl;
#endif
        return;
    }
    if (c.size() == 1) {
        c.pop_back();
        return;
    }
    c[l] = c.back();
    c.pop_back();
}
//----------------------------------------------------------------------
Literal Clause::extract_literal(LitNum l) {
     Literal error_lit;
     if (c.size() == 0) {
#ifdef DEBUGMESSAGES
        cerr << "Can't extract_literal from empty clause" << endl;
#endif
        return error_lit;
    }
    if (l > c.size() - 1) {
#ifdef DEBUGMESSAGES
        cerr << "extract_literal argument is out of range" << endl;
#endif
        return error_lit;
    }
    Literal lit(c[l]);
    if (c.size() == 1) {
        c.pop_back();
        return lit;
    }
    c[l] = c.back();
    c.pop_back();
    return lit;
}
//----------------------------------------------------------------------
Literal& Clause::operator[](size_t i) {
#ifdef DEBUGMESSAGES
    if (i > c.size() - 1)
        cerr << "You're out of range accessing a clause" << endl;
#endif
    return c[i];
}
//----------------------------------------------------------------------
void Clause::random_reorder() {
  // Make a permutation.
  vector<size_t> new_order;
  size_t s = c.size();
  for (size_t i = 0; i < s; i++)
    new_order.push_back(i);
  std::shuffle(new_order.begin(), new_order.end(), d);
  // Re-order.
  vector<Literal> new_c = c; 
  for (size_t i = 0; i < s; i++) {
    c[i] = new_c[new_order[i]];
  }
}
//----------------------------------------------------------------------
string Clause::to_string(bool subbed) const {
    commas::comma com(c.size());
    string result("{ ");
    for (const Literal& l : c) {
        result += l.to_string(subbed);
        result += com();
    }
    result += " }";
    return result;
}
//----------------------------------------------------------------------
string Clause::to_prolog_string() const {
  commas::comma com(c.size());
  string result("[ ");
  for (const Literal& l : c) {
      result += l.to_prolog_string();
      result += com();
  }
  result += " ]";
  return result;
}
//----------------------------------------------------------------------
string Clause::to_tptp_string() const {
  commas::comma com(c.size());
  string result("( ");
  for (const Literal& l : c) {
      result += l.to_tptp_string();
      string s = com();
      if (s == string(", "))
        s = string(" | "); 
      result += s;
  }
  result += " )";
  return result;
}
//----------------------------------------------------------------------
string Clause::make_LaTeX(bool subbed) const {
  commas::comma com(c.size());
  string s ("\\textcolor{blue}{\\{} ");
  for (const Literal& l : c) {
      s += l.make_LaTeX(subbed);
      s += com();
  }
  s += "\\textcolor{blue}{\\}}";
  return s;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Clause& cl) {
  out << "{ ";
  size_t s = cl.c.size();
  size_t i = 1;
  for (const Literal& l : cl.c) {
      out << l.to_string();
      if (i < s)
          out << " " << unicode_symbols::LogSym::or_sym << " ";
      i++;
  }
  out << " }";
  return out;
}
