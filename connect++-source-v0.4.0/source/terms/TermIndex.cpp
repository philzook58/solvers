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

#include "TermIndex.hpp"

//----------------------------------------------------------------------
#ifdef HASHCONSTERMS

Term* TermIndex::find(const Term& t) {
  auto i = index.find(t);
  if (i != index.end()) {
    return i->second;
  }
  return nullptr;
}

#else

Term* TermIndex::find(const Term& t) {
  for (size_t i = 0; i < term_pointers.size(); i++) {
    if (*(term_pointers[i]) == t) {
      return term_pointers[i];
    }
  }
  return nullptr;
}

#endif
//----------------------------------------------------------------------
TermIndex::~TermIndex() {
    for (size_t i = 0; i < term_pointers.size(); i++)
        delete term_pointers[i];
}
//----------------------------------------------------------------------
Term* TermIndex::add_variable_term(Variable* vp) {
    if (vp->is_subbed()) {
      cerr << "Don't add substituted variables to the Term Index!" << endl;
    }
    Term t(vp);
    Term* p = find(t);
    if (p != nullptr) {
      return p;
    }
    p = new Term(vp);
#ifdef HASHCONSTERMS
    index.insert(pair<Term, Term*>(t, p));
#endif
    term_pointers.push_back(p);
    return p;
}
//----------------------------------------------------------------------
Term* TermIndex::add_function_term(Function* fp,
                                   const vector<Term*>& args) {
    for (size_t i = 0; i < args.size(); i++) {
      if (args[i]->is_subbed()) {
        cerr << "Don't add substituted functions to the Term Index!" << endl;
      }
    }
    Term t(fp, args);
    Term* p = find(t);
    if (p != nullptr) {
        return p;
    }
    p = new Term(fp, args);
#ifdef HASHCONSTERMS
    index.insert(pair<Term, Term*>(t, p));
#endif
    term_pointers.push_back(p);
    return p;
}
//----------------------------------------------------------------------
Term* TermIndex::replace_variable_in_term(Variable* new_v,
                                          Variable* old_v,
                                          Term* t) {
  if (t->is_variable()) {
    if (old_v == t->get_v()) {
      return add_variable_term(new_v);
    }
    else
      return t;
  }
  else {
    Function* f = t->get_f();
    vector<Term*> new_args;
    for (size_t i = 0; i < t->arity(); i++)
      new_args.push_back(replace_variable_in_term(new_v, old_v, (*t)[i]));
    return add_function_term(f, new_args);
  }
}
//----------------------------------------------------------------------
// ONLY use this if the new Term is in the index.
//----------------------------------------------------------------------
Term* TermIndex::replace_variable_in_term_with_term(Term* new_t,
                                          Variable* old_v,
                                          Term* t) {
  if (t->is_variable()) {
    if (old_v == t->get_v()) {
      return new_t;
    }
    else
      return t;
  }
  else {
    Function* f = t->get_f();
    vector<Term*> new_args;
    for (size_t i = 0; i < t->arity(); i++)
      new_args.push_back(replace_variable_in_term_with_term(new_t, old_v, (*t)[i]));
    return add_function_term(f, new_args);
  }
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const TermIndex& t) {
    out << "Contents of term index:" << endl;
    out << "-----------------------" << endl;
    for (Term* p : t.term_pointers)
        out << p << " : " << *p << endl;
    return out;
}


/*
* From here on we have methods for Term that need to use the TermIndex.
*/


//----------------------------------------------------------------------
Term* Term::make_copy_with_new_vars_helper(VariableIndex& vi,
                                           TermIndex& ti,
                                           unordered_map<Variable*,Term*>& v_map) const {
    Term* result = nullptr;
    if (v != nullptr) {
        if (v->is_subbed()) {
            result = v->get_subbed_term()->make_copy_with_new_vars_helper(vi, ti, v_map);
            cerr << "If you're doing Connection Calculus then something's wrong!" << endl;
        }
        else {
            auto i = v_map.find(v);
            if (i == v_map.end()) {
                Variable* new_v = vi.add_anon_var();
                result = ti.add_variable_term(new_v);
                v_map.insert(VarMapType(v, result));
            }
            else {
                result = i->second;
            }
        }
    }
    else {
        vector<Term*> new_args;
        for (size_t i = 0; i < args.size(); i++) {
            new_args.push_back(args[i]->make_copy_with_new_vars_helper(vi, ti, v_map));
        }
        result = ti.add_function_term(f, new_args);
    }
    return result;
}
//----------------------------------------------------------------------
Term* Term::make_copy_with_new_vars(VariableIndex& vi,
                                   TermIndex& ti) const {

    unordered_map<Variable*,Term*> v_map;
    return make_copy_with_new_vars_helper(vi, ti, v_map);
}
