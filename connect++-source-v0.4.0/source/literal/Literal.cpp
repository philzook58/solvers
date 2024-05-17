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

#include "Literal.hpp"

//----------------------------------------------------------------------
Literal::Literal(Predicate* new_p,
                 const vector<Term*>& new_args,
                 Arity new_ar,
                 bool new_pol)
: pred(new_p)
, args(new_args)
, arity(new_ar)
, polarity(new_pol)
{
  #ifdef DEBUGMESSAGES
    if (new_p == nullptr) {
      cerr << "Why would you construct an empty predicate?" << endl;
    }
  #endif
    if (new_p->get_arity() != new_args.size()) {
        cerr << "Number of arguments doesn't match predicate arity" << endl;
        cerr << "Are you mixing up your predicate names?" << endl;
    }
}
//----------------------------------------------------------------------
Literal Literal::make_copy_with_new_vars_helper(VariableIndex& vi,
                                                TermIndex& ti,
                                                unordered_map<Variable*,Term*>& new_vars) const {
    vector<Term*> new_args;
    for (size_t i = 0; i < arity; i++)
        new_args.push_back(args[i]->make_copy_with_new_vars_helper(vi, ti, new_vars));
    Literal result(pred, new_args, arity, polarity);
    return result;
}
//----------------------------------------------------------------------
Literal Literal::make_copy_with_new_vars(VariableIndex& vi, TermIndex& ti) const {
  #ifdef DEBUGMESSAGES
    if (pred == nullptr)
      cerr << "You shouldn't be making copies of empty Literals" << endl;
  #endif
    unordered_map<Variable*,Term*> new_vars;
    return make_copy_with_new_vars_helper(vi, ti, new_vars);
}
//----------------------------------------------------------------------
bool Literal::is_compatible_with(const Literal* l) const {
  #ifdef DEBUGMESSAGES
    if (pred == nullptr || l->pred == nullptr) {
      cerr << "You shouldn't be checking compatibility of empty Literals" << endl;
    }
  #endif
    return (pred == l->pred &&
      polarity == l->polarity &&
      arity == l->arity);
}
//----------------------------------------------------------------------
bool Literal::is_complement_of(const Literal& l) const {
  return (pred == l.pred &&
          args == l.args &&
          arity == l.arity &&
          !polarity == l.polarity);
}
//----------------------------------------------------------------------
bool Literal::is_true() const {
  return ((polarity && 
          (pred->get_name() == string("$true")) && 
          (pred->get_arity() == 0)) 
          ||
          (!polarity && 
          (pred->get_name() == string("$false")) && 
          (pred->get_arity() == 0)));
}
//----------------------------------------------------------------------
bool Literal::is_false() const {
  return ((polarity && 
          (pred->get_name() == string("$false")) && 
          (pred->get_arity() == 0)) 
          ||
          (!polarity && 
          (pred->get_name() == string("$true")) && 
          (pred->get_arity() == 0)));
}
//----------------------------------------------------------------------
bool Literal::contains_variable(Variable* v) const {
  for (size_t i = 0; i < args.size(); i++) {
    // Note that this takes account of substitutions.
    if (args[i]->contains_variable(v))
      return true;
  }
  return false;
}
//----------------------------------------------------------------------
bool Literal::operator==(const Literal& l) const {
  #ifdef DEBUGMESSAGES
    if (pred == nullptr || l.pred == nullptr) {
      cerr << "You shouldn't be checking equality of empty Literals" << endl;
    }
  #endif
    return (pred == l.pred &&
            args == l.args &&
            arity == l.arity &&
            polarity == l.polarity);
}
//----------------------------------------------------------------------
bool Literal::subbed_equal(Literal* l) const {
  #ifdef DEBUGMESSAGES
     if (pred == nullptr || l->pred == nullptr) {
      cerr << "You shouldn't be checking subbed equality of empty Literals" << endl;
    }
  #endif
    if (!is_compatible_with(l)) {
        return false;
    }
    for (size_t i = 0; i < arity; i++) {
      if (!(args[i]->subbed_equal((l->args)[i])))
        return false;
    }
    return true;
}
//----------------------------------------------------------------------
string Literal::get_small_lit() const {
  string result;
  if (!polarity)
      result += unicode_symbols::LogSym::neg;
  result += pred->to_string();
  return result;
}
//----------------------------------------------------------------------
string Literal::to_string(bool subbed) const {
  string result("Empty literal");
  if (!is_empty()) {
    result = get_small_lit();
    result += "(";
    commas::comma com(args.size());
    for (Term* p : args) {
      result += p->to_string(subbed);
      result += com();
    }
    result += ")";
  }
  return result;
}
//----------------------------------------------------------------------
string Literal::to_prolog_string() const {
  string result;
  if (!polarity)
      result += "-";
  string name = pred->get_name();
  if (name == "=")
    name = "equal";
  result += name;
  if (arity > 0) {
    result += "(";
    commas::comma com(args.size());
    for (Term* p : args) {
      result += p->to_prolog_string();
      result += com();
    }
    result += ")";
  }
  return result;
}
//----------------------------------------------------------------------
string Literal::to_tptp_string() const {
  string result;
  string name = pred->get_name();
  if (name != "=") {
    if (!polarity)
      result += "~";
    result += name;
    if (arity > 0) {
      result += "(";
      commas::comma com(args.size());
      for (Term* p : args) {
        result += p->to_prolog_string();
        result += com();
      }
      result += ")";
    }
  }
  else {
    result += "( ";
    result += args[0]->to_prolog_string();
    if (polarity)
      result += " = ";
    else 
      result += " != ";
    result += args[1]->to_prolog_string();
    result += ")";
  }
  return result;
}
//----------------------------------------------------------------------
string Literal::make_LaTeX(bool subbed) const {
  string s;
  if (!polarity)
    s += "\\neg ";
  s += pred->make_LaTeX();
  if (arity > 0) {
    s += "(";
    commas::comma com(arity);
    for (Term* p : args) {
        s += p->make_LaTeX(subbed);
        s += com();    
    }
    s += ")";
  }
  return s;
}
//----------------------------------------------------------------------
void Literal::replace_variable(Variable* new_var, Variable* old_var,
                               TermIndex* ti) {
#ifdef DEBUGMESSAGES
  if (pred == nullptr)
    cerr << "You shouldn't be replacing variables in an empty Literal" << endl;
#endif
  for (size_t i = 0; i < arity; i++) {
    args[i] = ti->replace_variable_in_term(new_var, old_var, args[i]);
  }
}
//----------------------------------------------------------------------
void Literal::replace_variable_with_term(Term* new_term, Variable* old_var,
                               TermIndex* ti) {
  #ifdef DEBUGMESSAGES
   if (pred == nullptr)
    cerr << "You shouldn't be subbing terms in an empty Literal" << endl;
  #endif
  for (size_t i = 0; i < arity; i++) {
    args[i] = ti->replace_variable_in_term_with_term(new_term, old_var, args[i]);
  }
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Literal& l) {
  if (l.is_empty())
    out << "Empty literal";
  else {
    if (!l.polarity)
      out << unicode_symbols::LogSym::neg;
    out << l.pred->to_string();
    size_t s = l.args.size() - 1;
    size_t i = 0;
    out << "(";
    for (Term* p : l.args) {
        out << p->to_string();
        if (i < s)
            out << ", ";
            i++;
        }
    out << ")";
  }
  return out;
}
