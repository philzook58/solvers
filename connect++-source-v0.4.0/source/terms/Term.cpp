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

#include "Term.hpp"

/*
* Some methods are in TermIndex.cpp to make the dependencies work:
*
* make_copy_with_new_vars_helper
* make_copy_with_new_vars
*/

//----------------------------------------------------------------------
Term::Term(Function* new_f, const vector<Term*>& new_args)
: v(nullptr), f(new_f), args(new_args)
{
    if (new_f->get_arity() != new_args.size()) {
        cerr << "Number of arguments doesn't match function arity" << endl;
        cerr << "Perhaps your function names are mixed up?" << endl;
    }
}
//----------------------------------------------------------------------
bool Term::operator==(const Term& t) const {
    return (v == t.v &&
            f == t.f &&
            args == t.args);
}
//----------------------------------------------------------------------
Term* Term::operator[](size_t i) const {
    if (args.size() == 0) {
        cerr << "You shouldn't be accessing a term's arguments here." << endl;
        return nullptr;
    }
    return args[i];
}
//----------------------------------------------------------------------
bool Term::is_subbed() const {
    if (v != nullptr) {
        return v->is_subbed();
    }
    else {
        for (size_t i = 0; i < args.size(); i++) {
            if (args[i]->is_subbed()) {
                return true;
            }
        }
    }
    return false;
}
//----------------------------------------------------------------------
bool Term::subbed_equal(Term* t) const {
    Variable* tv = t->v;
    // LHS is a variable.
    if (v != nullptr) {
        if (v->is_subbed()) {
            return (v->get_subbed_term())->subbed_equal(t);
        }
        else if (t->subbed_is_variable()) {
            return (t->subbed_variable() == v);
        }
        else return false;
    }
    // RHS is a variable.
    else if (tv != nullptr) {
        if (tv->is_subbed()) {
            return subbed_equal(tv->get_subbed_term());
        }
        else return false;
    }
    // Both sides are functions.
    else {
        if (f != t->f)
            return false;
        if (f->get_arity() != t->f->get_arity())
            return false;
        for (size_t i = 0; i < f->get_arity(); i++) {
            if (!(args[i]->subbed_equal(t->args[i])))
                return false;
        }
        return true;
    }
}
//----------------------------------------------------------------------
bool Term::subbed_is_function() const {
    if (v == nullptr)
        return true;
    else
        return v->subbed_is_function();
}
//----------------------------------------------------------------------
bool Term::subbed_is_variable() const {
    if (v == nullptr)
        return false;
    else
        return v->subbed_is_variable();
}
//----------------------------------------------------------------------
Variable* Term::subbed_variable() const {
    if (f != nullptr) {
        cerr << "You shouldn't be using this with a function term." << endl;
        return nullptr;
    }
    else
        return v->subbed_variable();
}
//----------------------------------------------------------------------
bool Term::contains_variable(Variable* v2) const {
    if (v != nullptr)
       return v->contains_variable(v2);
    if (f != nullptr)
        for (size_t i = 0; i < args.size(); i++)
            if (args[i]->contains_variable(v2))
                return true;
    return false;
}
//----------------------------------------------------------------------
Function* Term::get_subbed_f() const {
    if (f != nullptr)
        return f;
    else
        return v->get_subbed_f();
}
//----------------------------------------------------------------------
Arity Term::get_subbed_arity() const {
    if (f != nullptr)
        return f->get_arity();
    else
        return v->get_subbed_arity();
}
//----------------------------------------------------------------------
void Term::find_subbed_vars(set<Variable*>& vs) const {
    if (v != nullptr) {
        if (v->is_subbed())
            v->get_subbed_term()->find_subbed_vars(vs);
        else
            vs.insert(v);
    }
    else {
        for (size_t i = 0; i < args.size(); i++)
            args[i]->find_subbed_vars(vs);
    }
}
//----------------------------------------------------------------------
string Term::to_string(bool subbed, bool show_addresses) const {
    string result;
    if (v != nullptr) {
      result += v->to_string(subbed);
    }
    else if (f != nullptr) {
        commas::comma com(args.size());
        result += f->to_string();
        result += "(";
        for (size_t j = 0; j < args.size(); j++) {
            result += args[j]->to_string(subbed, show_addresses);
            result += com();
        }
        result += ")";
    }
    else
        result += "You're trying to print a badly-formed term.";
    if (show_addresses) {
        result += ":";
        ostringstream oss;
        oss << this;
        result += oss.str();
    }
    return result;
}
//----------------------------------------------------------------------
string Term::to_prolog_string() const {
  string result;
  if (v != nullptr) {
    result += v->get_name();
  }
  else if (f != nullptr) {
      commas::comma com(args.size());
      result += f->get_name();
      if (args.size() > 0) {
        result += "(";
        for (size_t j = 0; j < args.size(); j++) {
            result += args[j]->to_prolog_string();
            result += com();
        }
      result += ")";
    }
  }
  return result;
}
//----------------------------------------------------------------------
string Term::make_LaTeX(bool subbed) const {
  if (v != nullptr) {
      return v->make_LaTeX(subbed);
  }
  string s = f->make_LaTeX();
  if (args.size() > 0) {
    s += "(";
    commas::comma com(args.size());
    for (size_t j = 0; j < args.size(); j++) {
        s += args[j]->make_LaTeX(subbed);
        s += com();    
    }
    s += ")";
  }
  return s;
}
//----------------------------------------------------------------------
bool Term::is_unsubbed_variable() const {
    if (v == nullptr)
        return false;
    return !(v->is_subbed());
}
//----------------------------------------------------------------------
Term* Term::skip_leading_variables() const {
    if (f == nullptr) {
        if (v->is_subbed()) {
            return v->skip_leading_variables();
        }
    }
    Term* p = const_cast<Term*>(this);
    return p;
}
//----------------------------------------------------------------------
set<Term*> Term::all_variables() const {
    set<Term*> result;
    if (v != nullptr) {
        if (v->is_subbed()) 
            cerr << "STOP IT!!! You shouldn't be using this with substituted variables!" << endl;
        Term* p = const_cast<Term*>(this);
        result.insert(p);
    }
    else {
        for (Term* p : args) {
            set<Term*> some_vars = p->all_variables();
            result.insert(some_vars.begin(), some_vars.end());
        }
    }
    return result;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Term& t) {
  out << t.to_string(params::output_terms_with_substitution, true);
  return out;
}


/*
* Everything from here on is implementatin of methods for 
* Variable.hpp
*
* These need to be here to make the dependencies work.
*/


//----------------------------------------------------------------------
string Variable::to_string(bool subbed) const {
  colour_string::ColourString cs(params::use_colours);
  if (!subbed || substitution == nullptr)
    return cs(name).lblue();
  else
    return substitution->to_string(subbed);
}
//----------------------------------------------------------------------
string Variable::make_LaTeX(bool subbed) const {
 if (subbed && substitution != nullptr)
   return substitution->make_LaTeX(subbed);
 else {
   string s ("\\text{");
   s += latex_escape_characters(name);
   s += "}";
   return s;
 }
}
//----------------------------------------------------------------------
bool Variable::subbed_is_function() const {
    if (substitution == nullptr)
        return false;
    else
        return substitution->subbed_is_function();
}
//----------------------------------------------------------------------
bool Variable::subbed_is_variable() const {
    if (substitution == nullptr)
        return true;
    else
        return substitution->subbed_is_variable();
}
//----------------------------------------------------------------------
Variable* Variable::subbed_variable() const {
    if (substitution == nullptr) {
        Variable* p = const_cast<Variable*>(this);
        return p;
    }
    else
        return substitution->subbed_variable();
}
//----------------------------------------------------------------------
bool Variable::contains_variable(Variable* v2) const {
    if (substitution == nullptr)
        return this==v2;
    else
        return substitution->contains_variable(v2);
}
//----------------------------------------------------------------------
Function* Variable::get_subbed_f() const {
    if (substitution == nullptr) {
        cerr << "There is no function name to be found..." << endl;
        return nullptr;
    }
    else
        return substitution->get_subbed_f();
}
//----------------------------------------------------------------------
Arity Variable::get_subbed_arity() const {
    if (substitution == nullptr) {
        cerr << "There is no arity to be found..." << endl;
        return 0;
    }
    else
        return substitution->get_subbed_arity();
}
//----------------------------------------------------------------------
Term* Variable::skip_leading_variables() const {
  if (substitution != nullptr) {
    return substitution->skip_leading_variables();
  }
  cerr << "Stop it! You're trying to skip something inappropriate!" << endl;
  return nullptr;
}

