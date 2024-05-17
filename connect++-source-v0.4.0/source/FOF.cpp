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

#include "FOF.hpp"

VariableIndex* FOF::var_index = nullptr;
FunctionIndex* FOF::fun_index = nullptr;
TermIndex* FOF::term_index = nullptr;
PredicateIndex* FOF::pred_index = nullptr;

//---------------------------------------------------------------------------
// Simple methods for Variables.
//---------------------------------------------------------------------------
bool FOF::has_free_variable(Variable* v) {
  switch (type) {
    case FOFType::Empty:
      cerr << "Don't do this with an Empty FOF!" << endl;
      return false;
      break;
    case FOFType::Atom:
      return pred.contains_variable(v);
    case FOFType::Neg:
      return (sub_formulas[0].has_free_variable(v));
      break;
    case FOFType::And:
    case FOFType::Or:
      for (size_t i = 0; i < sub_formulas.size(); i++) {
        if (sub_formulas[i].has_free_variable(v)) {
          return true;
        }
      }
      return false;
      break;
    case FOFType::Imp:
    case FOFType::Iff:
      return (sub_formulas[0].has_free_variable(v) ||
              sub_formulas[1].has_free_variable(v));
      break;
    case FOFType::A:
    case FOFType::E:
      if (var == v) 
        return false;
      return sub_formulas[0].has_free_variable(v);
      break;
    default:
      break;
  }
  return false;
}
//---------------------------------------------------------------------------
void FOF::replace_variable(Variable* new_var, Variable* old_var) {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  if (type == FOFType::Atom) {
    pred.replace_variable(new_var, old_var, term_index);
  }
  else {
    for (FOF& f : sub_formulas)
      f.replace_variable(new_var, old_var);
  }
}
//---------------------------------------------------------------------------
FOF FOF::make_definitional_predicate() const {
  set<Term*> a = this->find_free_variables();
  vector<Term*> args;
  for (Term* p : a)
    args.push_back(p);
  Predicate* name = pred_index->make_definitional_predicate(args.size());
  Literal lit(name, args, args.size(), true);
  return FOF(lit);
}
//---------------------------------------------------------------------------
bool FOF::distribute_or_once() {
  // For literals there is nothing to do.
  if (is_literal()) {
    return false;
  }
  // If we're at an AND, or an OR with no AND immediately under it,
  // then we're just going to deal with the subformulas. 
  size_t and_location = find_and();
  size_t s = sub_formulas.size();
  if (type == FOFType::And || 
      ((type == FOFType::Or) && (and_location == s))) {
    bool result = false;
    // OK, so it's not, strictly speaking, just "once" but 
    // we don't really mind do we?
    for (size_t i = 0; i < s; i++) {
      if (sub_formulas[i].distribute_or_once())
        result = true;
    }
    return result;
  }
  // It must be an OR with an AND immediately under it. That means 
  // we can distribute. First get the AND's subformulas and 
  // remove it.
  vector<FOF> and_fof_subs = sub_formulas[and_location].sub_formulas;
  if (and_location != (s-1)) {
    sub_formulas[and_location] = sub_formulas[s-1];
  }
  sub_formulas.pop_back();
  // Now you've saved the sub-formulas for the AND, and 
  // removed it. The last remaining child of the OR is 
  // now going to be combined using OR with all 
  // the saved subformulas.
  FOF f = sub_formulas[s-2];
  size_t s2 = and_fof_subs.size();
  vector<FOF> new_sub_formulas_2;
  for (int i = 0; i < s2; i++) {
    vector<FOF> new_sub_formulas;
    new_sub_formulas.push_back(f);
    new_sub_formulas.push_back(and_fof_subs[i]);
    new_sub_formulas_2.push_back(FOF::make_or(new_sub_formulas));
  }
  // You may have started with an OR with only two children. If so 
  // then you can now move the AND upwards.
  if (s == 2) {
    type = FOFType::And;
    sub_formulas = new_sub_formulas_2;
  }
  else {
    sub_formulas[s-2] = FOF::make_and(new_sub_formulas_2);
  }
  return true;
}
//---------------------------------------------------------------------------
bool FOF::distribute_and_once() {
  // For literals there is nothing to do.
  if (is_literal()) {
    return false;
  }
  // If we're at an OR, or an AND with no OR immediately under it,
  // then we're just going to deal with the subformulas. 
  size_t or_location = find_or();
  size_t s = sub_formulas.size();
  if (type == FOFType::Or || 
      ((type == FOFType::And) && (or_location == s))) {
    bool result = false;
    // OK, so it's not, strictly speaking, just "once" but 
    // we don't really mind do we?
    for (size_t i = 0; i < s; i++) {
      if (sub_formulas[i].distribute_and_once())
        result = true;
    }
    return result;
  }
  // It must be an AND with an OR immediately under it. That means 
  // we can distribute. First get the OR's subformulas and 
  // remove it.
  vector<FOF> or_fof_subs = sub_formulas[or_location].sub_formulas;
  if (or_location != (s-1)) {
    sub_formulas[or_location] = sub_formulas[s-1];
  }
  sub_formulas.pop_back();
  // Now you've saved the sub-formulas for the OR, and 
  // removed it. The last remaining child of the AND is 
  // now going to be combined using AND with all 
  // the saved subformulas.
  FOF f = sub_formulas[s-2];
  size_t s2 = or_fof_subs.size();
  vector<FOF> new_sub_formulas_2;
  for (int i = 0; i < s2; i++) {
    vector<FOF> new_sub_formulas;
    new_sub_formulas.push_back(f);
    new_sub_formulas.push_back(or_fof_subs[i]);
    new_sub_formulas_2.push_back(FOF::make_and(new_sub_formulas));
  }
  // You may have started with an AND with only two children. If so 
  // then you can now move the OR upwards.
  if (s == 2) {
    type = FOFType::Or;
    sub_formulas = new_sub_formulas_2;
  }
  else {
    sub_formulas[s-2] = FOF::make_or(new_sub_formulas_2);
  }
  return true;
}
//---------------------------------------------------------------------------
// Skolemization
//---------------------------------------------------------------------------
Term* FOF::make_skolem_function(const vector<Term*>& args) {
  Function* sk = fun_index->make_skolem_function(args.size());
  Term* sk_t = term_index->add_function_term(sk, args);
  return sk_t;
}
//---------------------------------------------------------------------------
void FOF::replace_variable_with_term(Term* new_term, Variable* old_var) {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  if (type == FOFType::Atom) {
    pred.replace_variable_with_term(new_term, old_var, term_index);
  }
  else {
    for (FOF& f : sub_formulas)
      f.replace_variable_with_term(new_term, old_var);
  }
}
//---------------------------------------------------------------------------
void FOF::skolemize_main(vector<Term*> skolem_arguments) {
  Term* sk_t;
  FOF f(FOFType::Atom);
  switch (type) {
    case FOFType::Atom:
      break;
    case FOFType::Neg:
      sub_formulas[0].skolemize_main(skolem_arguments);
      break;
    case FOFType::And:
    case FOFType::Or:
    case FOFType::Imp:
    case FOFType::Iff:
      for (FOF& g : sub_formulas)
        g.skolemize_main(skolem_arguments);
      break;
    case FOFType::A:
      skolem_arguments.push_back(term_index->add_variable_term(var));
      sub_formulas[0].skolemize_main(skolem_arguments);
      break;
    case FOFType::E:
      sk_t = make_skolem_function(skolem_arguments);
      sub_formulas[0].replace_variable_with_term(sk_t, var);
      sub_formulas[0].skolemize_main(skolem_arguments);
      f = sub_formulas[0];
      *this = f;
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
void FOF::skolemize_universals_main(vector<Term*> skolem_arguments) {
  Term* sk_t;
  FOF f(FOFType::Atom);
  switch (type) {
    case FOFType::Atom:
      break;
    case FOFType::Neg:
      sub_formulas[0].skolemize_universals_main(skolem_arguments);
      break;
    case FOFType::And:
    case FOFType::Or:
    case FOFType::Imp:
    case FOFType::Iff:
      for (FOF& g : sub_formulas)
        g.skolemize_universals_main(skolem_arguments);
      break;
    case FOFType::E:
      skolem_arguments.push_back(term_index->add_variable_term(var));
      sub_formulas[0].skolemize_universals_main(skolem_arguments);
      break;
    case FOFType::A:
      sk_t = make_skolem_function(skolem_arguments);
      sub_formulas[0].replace_variable_with_term(sk_t, var);
      sub_formulas[0].skolemize_universals_main(skolem_arguments);
      f = sub_formulas[0];
      *this = f;
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
// Miniscoping
//---------------------------------------------------------------------------
void FOF::miniscope_split(Variable* v, 
                          vector<FOF>& free, 
                          vector<FOF>& absent) {
  // Remember that at this point you have a NNF with 
  // unique variables. So whatever is in the subformula 
  // is AND, OR, Atom or Neg (Literal).
  vector<FOF>& subs = sub_formulas[0].sub_formulas;
  for (size_t i = 0; i < subs.size(); i++) {
    FOF f(subs[i]);
    if (f.has_free_variable(v))
      free.push_back(f);
    else
      absent.push_back(f);
  }
}
//---------------------------------------------------------------------------
void FOF::miniscope_all() {
  for (size_t i = 0; i < sub_formulas.size(); i++ ) {
    sub_formulas[i].miniscope();
  }
}
//---------------------------------------------------------------------------
// Constructors.
//---------------------------------------------------------------------------
FOF::FOF(const Literal& lit)
: sub_formulas()
, var(nullptr)
{
  if (lit.is_positive()) {
    type = FOFType::Atom;
    pred = lit;
  }
  else {
    pred.clear();
    type = FOFType::Neg;
    Literal lit_copy = lit;
    lit_copy.make_positive();
    FOF f(lit_copy);
    sub_formulas.push_back(f);
  }
}
//---------------------------------------------------------------------------
FOF::FOF(FOFType t, const vector<FOF>& sf, Variable* v)
: type(t)
, pred()
, sub_formulas(sf)
, var(v)
{
  switch (t) {
      case FOFType::Atom:
        cerr << "Stop it! You can't make an atom with this constructor!" << endl;
        break;
      case FOFType::Neg:
      case FOFType::And:
      case FOFType::Or:
      case FOFType::Imp:
      case FOFType::Iff:
        // Easy as the work gets done above.
        if (var != nullptr) {
          cerr << "Are you sure you want to associate a variable with something that's not a quantifier?" << endl;
          var = nullptr;
        }
        break;
      case FOFType::A:
      case FOFType::E:
        if (sf.size() != 1) {
          cerr << "Careful! A quantifier should only have one subformula." << endl;
        }
        if (v == nullptr) {
          cerr << "Careful! A quantifier needs a variable." << endl;
        }
        break;
      default:
        break;
  }
}
//---------------------------------------------------------------------------
// Basic tests.
//---------------------------------------------------------------------------
bool FOF::is_literal() const {
  return (type == FOFType::Atom) || 
    (type == FOFType::Neg && sub_formulas[0].type == FOFType::Atom);
}
//---------------------------------------------------------------------------
bool FOF::is_clause() const {
  if (is_literal()) {
    return true;
  }
  if (!(type == FOFType::Or)) {
    return false;
  }
  for (size_t i = 0; i < sub_formulas.size(); i++) {
    if (!sub_formulas[i].is_literal()) {
      return false;
    }
  } 
  return true;
}
//---------------------------------------------------------------------------
// Standard simplifications.
//---------------------------------------------------------------------------
void FOF::remove_negation() {
  if (type == FOFType::Neg) {
    FOF f = sub_formulas[0];
    *this = f;
  }
}
//---------------------------------------------------------------------------
void FOF::negate() {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  if (type == FOFType::Imp) {
    type = FOFType::And;
    sub_formulas[1].negate();
  }
  else if (type == FOFType::Neg) {
    remove_negation();
  }
  else {
    FOF f = *this;
    type = FOFType::Neg;
    pred.clear();
    var = nullptr;
    sub_formulas.clear();
    sub_formulas.push_back(f);
  }
}
//---------------------------------------------------------------------------
void FOF::simple_negate() {
  FOF f = *this;
  type = FOFType::Neg;
  pred.clear();
  var = nullptr;
  sub_formulas.clear();
  sub_formulas.push_back(f);
}
//---------------------------------------------------------------------------
void FOF::invert_literal() {
  if (type == FOFType::Atom) {
    simple_negate();
    return;
  } 
  if (type == FOFType::Neg && sub_formulas[0].type == FOFType::Atom) {
    remove_negation();
    return;
  }
  cerr << "Don't use this with a non-literal." << endl;
}
//---------------------------------------------------------------------------
void FOF::remove_iff() {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  // End of recursion.
  if (type == FOFType::Atom)
    return;
  // Do the relevant transformation.
  if (type == FOFType::Iff) {
    FOF lhs = *this;
    FOF rhs = *this;
    lhs.type = FOFType::Imp;
    rhs.type = FOFType::Imp;
    FOF store = rhs.sub_formulas[1];
    rhs.sub_formulas[1] = rhs.sub_formulas[0];
    rhs.sub_formulas[0] = store;
    type = FOFType::And;
    sub_formulas.clear();
    sub_formulas.push_back(lhs);
    sub_formulas.push_back(rhs);
  }
  // Finish the job. Also applies the transformation to other FOF types.
  for (FOF& f : sub_formulas)
    f.remove_iff();
}
//---------------------------------------------------------------------------
void FOF::remove_imp() {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  // End of recursion.
  if (type == FOFType::Atom)
    return;
  // Do the relevant transformation.
  if (type == FOFType::Imp) {
    type = FOFType::Or;
    sub_formulas[0].negate();
  }
  // Finish the job. Also applies the transformation to other FOF types.
  for (FOF& f : sub_formulas)
    f.remove_imp();
}
//---------------------------------------------------------------------------
void FOF::make_unique_bound_variables() {
  Variable* new_var;
  switch (type) {
    case FOFType::Atom:
      break;
    case FOFType::Neg:
    case FOFType::And:
    case FOFType::Or:
    case FOFType::Imp:
    case FOFType::Iff:
      for (FOF& sf : sub_formulas)
        sf.make_unique_bound_variables();
      break;
    case FOFType::A:
    case FOFType::E:
      sub_formulas[0].make_unique_bound_variables();
      new_var = var_index->add_unique_var();
      sub_formulas[0].replace_variable(new_var, var);
      var = new_var;
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
void FOF::remove_redundant_quantifiers() {
  Variable* new_var;
  switch (type) {
    case FOFType::Atom:
      break;
    case FOFType::Neg:
    case FOFType::And:
    case FOFType::Or:
    case FOFType::Imp:
    case FOFType::Iff:
      for (FOF& sf : sub_formulas)
        sf.remove_redundant_quantifiers();
      break;
    case FOFType::A:
    case FOFType::E:
      sub_formulas[0].remove_redundant_quantifiers();
      if (!sub_formulas[0].has_free_variable(var)) {
        vector<FOF> sf(sub_formulas);
        type = sub_formulas[0].type;
        pred = sub_formulas[0].pred;
        var = sub_formulas[0].var;
        sub_formulas = sf[0].sub_formulas;
      }
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
void FOF::push_negs() {
  switch (type) {
    case FOFType::Neg:
      switch (sub_formulas[0].type) {
          case FOFType::Neg:
            remove_negation();
            remove_negation();
            push_negs();
            break;
          case FOFType::Atom:
            break;
          case FOFType::And:
            remove_negation();
            type = FOFType::Or;
            for (FOF& f : sub_formulas) {
              f.negate();
              f.push_negs();
            }
            break;
          case FOFType::Or:
            remove_negation();
            type = FOFType::And;
            for (FOF& f : sub_formulas) {
              f.negate();
              f.push_negs();
            }
            break;
          case FOFType::A:
            remove_negation();
            type = FOFType::E;
            sub_formulas[0].negate();
            sub_formulas[0].push_negs();
            break;
          case FOFType::E:
            remove_negation();
            type = FOFType::A;
            sub_formulas[0].negate();
            sub_formulas[0].push_negs();
            break;
          case FOFType::Imp:
          case FOFType::Iff:
            cerr << "Stop it!!! You don't push negations through -> or <->." << endl;
            break;
          default:
            break;
      }
      break;
    case FOFType::Atom:
      break;
    case FOFType::And:
    case FOFType::Or:
    case FOFType::A:
    case FOFType::E:
      for (FOF& f : sub_formulas)
        f.push_negs();
      break;
    case FOFType::Imp:
    case FOFType::Iff:
      cerr << "Stop it!!! You don't push negations through -> or <->." << endl;
      break;
    default:
      break;
  }
}
//---------------------------------------------------------------------------
void FOF::convert_to_nnf() {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  remove_iff();
  remove_imp();
  push_negs();
}
//---------------------------------------------------------------------------
void FOF::miniscope() {
  vector<FOF> free;
  vector<FOF> absent;
  FOF new_sub(FOFType::Empty);
  vector<FOF> new_subs;
  Variable* new_var;
  switch (type) {
    case FOFType::Empty:
      cerr << "Don't do this with an empty formula" << endl;
      break;
    case FOFType::Atom:
    case FOFType::Neg:
      break;
    case FOFType::And:
    case FOFType::Or:
      miniscope_all();
      break;
    case FOFType::Imp:
    case FOFType::Iff:
      cerr << "Don't do this unless you've removed -> and <->" << endl;
      break;
    // Remember you're only dealing with stuff in NNF. You 
    // do however have to handle nested quantifiers.
    case FOFType::A:
      sub_formulas[0].miniscope();
      if (!(sub_formulas[0].type == FOFType::And ||
          sub_formulas[0].type == FOFType::Or)) {
        return;
      }
      // You have \forall followed by (miniscoped) AND or OR.
      miniscope_split(var, free, absent);
      // If the quantifier is followed by AND you can just 
      // make a \forall for every subformula involving the 
      // variable.
      if (sub_formulas[0].type == FOFType::And) {
        type = FOFType::And;
        // If everything is bound then make a new forall everywhere
        // with a new variable.
        if (free.size() == sub_formulas[0].sub_formulas.size()) {
          for (size_t i = 0; i < free.size(); i++) {
            new_var = var_index->add_unique_var();
            new_sub = free[i];
            new_sub.replace_variable(new_var, var);
            new_sub = FOF::make_forall(new_sub, new_var);
            new_subs.push_back(new_sub);
          }
          sub_formulas = new_subs;
        }
        // If any subformula doesn't have the variable then just
        // move the forall in. Remember you need to consider the 
        // possibility that the quantifier can just be removed.
        else if (free.size() > 0) {
          sub_formulas = absent;
          if (free.size() == 1)
            new_sub = free[0];
          else
            new_sub = FOF::make_and(free);
          new_sub = FOF::make_forall(new_sub, var);
          sub_formulas.push_back(new_sub);
        }
        // You're just going to remove the quantifier.
        else {
          sub_formulas = sub_formulas[0].sub_formulas;
        }
        var = nullptr;
        miniscope_all();
        return;
      }
      if (sub_formulas[0].type == FOFType::Or) {
        // You have a \forall followed by an OR.
        // If eveything is bound there's nothing to do.
        if (absent.size() == 0)
          return;
        else if (free.size() > 0) {
          type = FOFType::Or;
          sub_formulas = absent;
          if (free.size() == 1)
            new_sub = free[0];
          else
            new_sub = FOF::make_or(free);
          new_sub = FOF::make_forall(new_sub, var);
          sub_formulas.push_back(new_sub);
          var = nullptr;
          miniscope_all();
        }
        // You can just drop the quantifier.
        else {
          type = FOFType::Or;
          vector<FOF> sf(sub_formulas);
          sub_formulas = sf[0].sub_formulas;
          var = nullptr;
        }
        return;
      }
      break;
    // You have an \exists.
    case FOFType::E:
      sub_formulas[0].miniscope();
      if (!(sub_formulas[0].type == FOFType::And ||
          sub_formulas[0].type == FOFType::Or)) {
        return;
      }
      // You have an \exists followed by AND or OR.
      miniscope_split(var, free, absent);
      if (sub_formulas[0].type == FOFType::Or) {
        type = FOFType::Or;
        // If everything is bound then make a new exists everywhere
        // with a new variable.
        if (free.size() == sub_formulas[0].sub_formulas.size()) {
          for (size_t i = 0; i < free.size(); i++) {
            new_var = var_index->add_unique_var();
            new_sub = free[i];
            new_sub.replace_variable(new_var, var);
            new_sub = FOF::make_exists(new_sub, new_var);
            new_subs.push_back(new_sub);
          }
          sub_formulas = new_subs;
        }
        // If any subformula doesn't have the variable then just
        // move the \exists in.
        else if (free.size() > 0) {
          sub_formulas = absent;
          if (free.size() == 1)
            new_sub = free[0];
          else
            new_sub = FOF::make_or(free);
          new_sub = FOF::make_exists(new_sub, var);
          sub_formulas.push_back(new_sub);
        }
        // We're just going to drop the quantifier.
        else {
          sub_formulas = sub_formulas[0].sub_formulas;
        }
        var = nullptr;
        miniscope_all();
        return;
      }
      // You have an \exists followed by and AND.
      if (sub_formulas[0].type == FOFType::And) {
        // If eveything is bound there's nothing to do.
        if (absent.size() == 0)
          return;
        else if (free.size() != sub_formulas[0].sub_formulas.size()) {
          type = FOFType::And;
          sub_formulas = absent;
           if (free.size() == 1)
            new_sub = free[0];
          else
            new_sub = FOF::make_and(free);
          new_sub = FOF::make_exists(new_sub, var);
          sub_formulas.push_back(new_sub);
          var = nullptr;
          miniscope_all();
        }
        // We can just drop the quantifier.
        else {
          type = FOFType::And;
          vector<FOF> sf(sub_formulas);
          sub_formulas = sf[0].sub_formulas;
          var = nullptr;
        }
        return;
      }
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
void FOF::convert_to_cnf_clauses(vector<Clause>& cs) {
  if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
#ifdef DEBUGOUTPUT
      cout << "Remove iff:" << endl;
#endif
  remove_iff();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Remove imp" << endl;
#endif
  remove_imp();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Push negs:" << endl;
#endif
  push_negs();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Make unique vars:" << endl;
#endif
  make_unique_bound_variables();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Remove redundant quantifiers:" << endl;
#endif
  remove_redundant_quantifiers();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Miniscope:" << endl;
#endif
  if (params::miniscope) {
    miniscope();
  }
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Skolemize:" << endl;
#endif
  skolemize();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Remove universal quantifiers:" << endl;
#endif
  remove_universal_quantifiers();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Distribute or:" << endl;
#endif
  distribute_or();
#ifdef DEBUGOUTPUT
      cout << *this << endl;
      cout << "Convert to clauses:" << endl;
#endif
  convert_to_clauses(cs);
#ifdef DEBUGOUTPUT
      cout << *this << endl;
#endif
}
//---------------------------------------------------------------------------
void FOF::split_sub_formulas(vector<FOF>& left_sub, vector<FOF>& right_sub) {
  left_sub.clear();
  right_sub.clear();
  size_t s = sub_formulas.size();
  if (s == 2) {
    left_sub.push_back(sub_formulas[0]);
    right_sub.push_back(sub_formulas[1]);
    return;
  }
  if (s == 3) {
    right_sub.push_back(sub_formulas[2]);
    left_sub = sub_formulas;
    left_sub.pop_back();
    return;
  }
  size_t left_size = s / 2;
  for (size_t i = 0; i < left_size; i++) {
    left_sub.push_back(sub_formulas[i]);
  }
  for (size_t i = left_size; i < s; i++) {
    right_sub.push_back(sub_formulas[i]);
  }
}
//---------------------------------------------------------------------------
void FOF::find_definitional_tuple(FOF& f, vector<FOF>& d, bool in_conjunction) {
  f.clear();
  d.clear();
  // Literals are straightforward.
  if (is_literal()) {
    f = *this;
    vector<FOF> new_d;
    d = new_d;
    return;
  }
  // You must have an And or an Or because we're in NNF.
  // Let's split half and half, just for the sake of symmetry.
  vector<FOF> left;
  vector<FOF> right;
  split_sub_formulas(left, right);
  FOF l = left[0];
  FOF r = right[0];
  if (left.size() > 1) {
    l = FOF(type, left, nullptr);
  }
  if (right.size() > 1) {
    r = FOF(type, right, nullptr);
  }
  // Somewhere to store results.
  FOF new_f_1(FOFType::Empty);
  FOF new_f_2(FOFType::Empty);
  vector<FOF> new_d_1;
  vector<FOF> new_d_2;
  // The tricky case is an Or inside an And.
  if (in_conjunction && type == FOFType::Or) {
    l.find_definitional_tuple(new_f_1, new_d_1, false);
    r.find_definitional_tuple(new_f_2, new_d_2, false);
    FOF def = make_definitional_predicate();
    f = def;
    def.simple_negate();
    vector<FOF> args1;
    args1.push_back(def);
    args1.push_back(new_f_1);
    d.push_back(FOF::make_and(args1));
    vector<FOF> args2;
    args2.push_back(def);
    args2.push_back(new_f_2);
    d.push_back(FOF::make_and(args2));
    for (const FOF& g : new_d_1) {
      d.push_back(g);
    }
    for (const FOF& g : new_d_2) {
      d.push_back(g);
    }
    return;
  }
  // The final case is straightforward.
  bool is_and(type == FOFType::And);
  l.find_definitional_tuple(new_f_1, new_d_1, is_and);
  r.find_definitional_tuple(new_f_2, new_d_2, is_and);
  vector<FOF> new_args;
  new_args.push_back(new_f_1);
  new_args.push_back(new_f_2);
  FOF new_f(type, new_args, nullptr);
  f = new_f;
  d = new_d_1;
  for (const FOF& g : new_d_2){
    d.push_back(g);
  }
}
//---------------------------------------------------------------------------
void FOF::definitional_convert_to_cnf_clauses(vector<Clause>& cs) {
   if (type == FOFType::Empty) {
    cerr << "Don't do this with an Empty FOF!" << endl;
    return;
  }
  /*
  * Note that the description in the restricted backtracking paper produces a 
  * DNF and starts with a Skolemized NNF of the original formula, *not* its 
  * negation. As the difference between this and the current representation, for 
  * connection calculusm ir just that all the literals get negated, this could 
  * be done more efficiently, but for now I'm going to just do a direct 
  * implementation of the procedure described in the paper. So: negate 
  * first, produce a DNF, then negate again.
  */ 
  simple_negate();
  remove_iff();
  remove_imp();
  push_negs();
  make_unique_bound_variables();
  remove_redundant_quantifiers();
  /*
  * As we're producing a DNF, we skolemize universals and then remove existentials.
  */
  skolemize_universals();
  remove_existential_quantifiers();
  /*
  * Now we do the definitional magic. 
  */
  FOF f(FOFType::Empty);
  vector<FOF> d;
  find_definitional_tuple(f, d, false);
  /*
  * f is a DNF so we can invert it and flatten it to 
  * the required CNF. 
  */
  f.dnf_invert_and_convert_to_clauses(cs);
  /*
  * Each element of d now needs to be converted using 
  * a standard conversion, then inverted and transformed 
  * to CNF.
  */
  for (FOF& formula : d) {
    vector<Clause> new_cs;
    formula.distribute_and();
    formula.dnf_invert_and_convert_to_clauses(new_cs);
    for (const Clause& new_c : new_cs) {
      cs.push_back(new_c);
    }
  }
}
//---------------------------------------------------------------------------
void FOF::skolemize() {
  vector<Term*> skolem_arguments;
  skolemize_main(skolem_arguments);
}
//---------------------------------------------------------------------------
void FOF::skolemize_universals() {
  vector<Term*> skolem_arguments;
  skolemize_universals_main(skolem_arguments);
}
//---------------------------------------------------------------------------
void FOF::remove_universal_quantifiers() {
  FOF f(FOFType::Atom);
  switch (type) {
    case FOFType::Atom:
      break;
    case FOFType::Neg:
      sub_formulas[0].remove_universal_quantifiers();
      break;
    case FOFType::And:
    case FOFType::Or:
    case FOFType::Imp:
    case FOFType::Iff:
      for (FOF& g : sub_formulas)
        g.remove_universal_quantifiers();
      break;
    case FOFType::A:
      sub_formulas[0].remove_universal_quantifiers();
      f = sub_formulas[0];
      *this = f;
      break;
    case FOFType::E:
      sub_formulas[0].remove_universal_quantifiers();
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
void FOF::remove_existential_quantifiers() {
  FOF f(FOFType::Atom);
  switch (type) {
    case FOFType::Atom:
      break;
    case FOFType::Neg:
      sub_formulas[0].remove_existential_quantifiers();
      break;
    case FOFType::And:
    case FOFType::Or:
    case FOFType::Imp:
    case FOFType::Iff:
      for (FOF& g : sub_formulas)
        g.remove_existential_quantifiers();
      break;
    case FOFType::E:
      sub_formulas[0].remove_existential_quantifiers();
      f = sub_formulas[0];
      *this = f;
      break;
    case FOFType::A:
      sub_formulas[0].remove_existential_quantifiers();
      break;
    default:
      break;
    }
}
//---------------------------------------------------------------------------
void FOF::to_Literal(Literal& new_lit) const {
    if (type == FOFType::Atom) {
      new_lit = pred;
    }
    else {
      new_lit = sub_formulas[0].pred;
      new_lit.make_negative();
    }
}
//---------------------------------------------------------------------------
void FOF::convert_to_clauses(vector<Clause>& cs) const {
  cs.clear();
  if (is_literal()) {
    Literal new_lit;
    to_Literal(new_lit);
    Clause new_c;
    new_c.add_lit(new_lit);
    cs.push_back(new_c);
    return;
  } 
  if (type == FOFType::Or) {
    vector<Clause> c;
    Clause new_c;
    cs.push_back(new_c);
    for (size_t i = 0; i < sub_formulas.size(); i++) {
      sub_formulas[i].convert_to_clauses(c);
      for (size_t j = 0; j < c[0].size(); j++) {
        cs[0].add_lit((c[0])[j]);
      }
    }
    return;
  }
  if (type == FOFType::And) {
    vector<Clause> c;
    for (size_t i = 0; i < sub_formulas.size(); i++) {
      sub_formulas[i].convert_to_clauses(c);
      for (size_t j = 0; j < c.size();j++) {
        cs.push_back(c[j]);
      }
    }
  }
}
//---------------------------------------------------------------------------
void FOF::dnf_invert_and_convert_to_clauses(vector<Clause>& cs) const {
  cs.clear();
  if (is_literal()) {
    Literal new_lit;
    to_Literal(new_lit);
    // This is where the inversion happens.
    new_lit.invert();
    Clause new_c;
    new_c.add_lit(new_lit);
    cs.push_back(new_c);
    return;
  } 
  // Anything under here is essentially ANDed literals.
  if (type == FOFType::And) {
    vector<Clause> c;
    Clause new_c;
    cs.push_back(new_c);
    for (size_t i = 0; i < sub_formulas.size(); i++) {
      sub_formulas[i].dnf_invert_and_convert_to_clauses(c);
      for (size_t j = 0; j < c[0].size(); j++) {
        cs[0].add_lit((c[0])[j]);
      }
    }
    return;
  }
  // Anything below here essentially converts to another DNF.
  if (type == FOFType::Or) {
    vector<Clause> c;
    for (size_t i = 0; i < sub_formulas.size(); i++) {
      sub_formulas[i].dnf_invert_and_convert_to_clauses(c);
      for (size_t j = 0; j < c.size();j++) {
        cs.push_back(c[j]);
      }
    }
  }
}
//---------------------------------------------------------------------------
size_t FOF::find_and() const {
  size_t s = sub_formulas.size();
  for (size_t i = 0; i < s; i++) {
    if (sub_formulas[i].type == FOFType::And) {
      return i;
    }
  }
  return s;
}
//---------------------------------------------------------------------------
size_t FOF::find_or() const {
  size_t s = sub_formulas.size();
  for (size_t i = 0; i < s; i++) {
    if (sub_formulas[i].type == FOFType::Or) {
      return i;
    }
  }
  return s;
}
//---------------------------------------------------------------------------
void FOF::distribute_or() {
  while (distribute_or_once()) {};
}
//---------------------------------------------------------------------------
void FOF::distribute_and() {
  while (distribute_and_once()) {};
}
//---------------------------------------------------------------------------
string FOF::to_string() const {
  string result;
  size_t s = sub_formulas.size();;
  size_t i = 1;
  switch (type) {
    case FOFType::Atom:
      result = pred.to_string();
      break;
    case FOFType::Neg:
      result = unicode_symbols::LogSym::neg;
      result += "( ";
      result += sub_formulas[0].to_string();
      result += " )";
      break;
    case FOFType::And:
      result = "( ";
      for (const FOF& g : sub_formulas) {
        result += g.to_string();
        if (i < s) {
         result += " ";
          result += unicode_symbols::LogSym::and_sym;
          result += " ";
        }
        i++;
      }
      result += " )";
      break;
    case FOFType::Or:
      result = "( ";
      for (const FOF& g : sub_formulas) {
        result += g.to_string();
        if (i < s) {
            result += " ";
            result += unicode_symbols::LogSym::or_sym;
            result += " ";
        }
        i++;
      }
      result += " )";
      break;
    case FOFType::Imp:
      result = "( ";
      result +=  sub_formulas[0].to_string();
      result += " ";
      result += unicode_symbols::LogSym::ifthen;
      result += " ";
      result += sub_formulas[1].to_string();
      result += " )";
      break;
    case FOFType::Iff:
      result = "( ";
      result += sub_formulas[0].to_string();
      result += " ";
      result += unicode_symbols::LogSym::iff;
      result += " ";
      result += sub_formulas[1].to_string();
      result += " )";
      break;
    case FOFType::A:
      result = unicode_symbols::LogSym::forall;
      result += var->to_string();
      result += " . [ ";
      result += sub_formulas[0].to_string();
      result += " ]";
      break;
    case FOFType::E:
      result = unicode_symbols::LogSym::exists;
      result += var->to_string();
      result += " . [ ";
      result += sub_formulas[0].to_string();
      result += " ]";
      break;
    default:
      break;
  }
  return result;
}
//---------------------------------------------------------------------------
SimplificationResult FOF::simplify_cnf(vector<Clause>& cnf, 
                                       vector<string>& roles) {
  vector<Clause> new_cnf;
  vector<string> new_roles;
  bool cnf_is_contradiction = false;
  size_t i = 0;
  for (Clause& c : cnf) {
    SimplificationResult result = c.simplify();
    if (result == SimplificationResult::Tautology) {
      i++;
      continue;
    }
    if (result == SimplificationResult::Contradiction) {
      i++;
      cnf_is_contradiction = true;
      continue;
    } 
    new_cnf.push_back(c);
    new_roles.push_back(roles[i]);
    i++;
  }
  cnf = new_cnf;
  roles = new_roles;
  if (cnf_is_contradiction) 
    return SimplificationResult::Contradiction;
  if (cnf.size() == 0)
    return SimplificationResult::Tautology;
  return SimplificationResult::OK;
}
//---------------------------------------------------------------------------
SimplificationResult FOF::simplify_cnf(vector<Clause>& cnf) {
  vector<Clause> new_cnf;
  bool cnf_is_contradiction = false;
  for (Clause& c : cnf) {
    SimplificationResult result = c.simplify();
    if (result == SimplificationResult::Tautology)
      continue;
    if (result == SimplificationResult::Contradiction) {
      cnf_is_contradiction = true;
      continue;
    } 
    new_cnf.push_back(c);
  }
  cnf = new_cnf;
  if (cnf_is_contradiction) 
    return SimplificationResult::Contradiction;
  if (cnf.size() == 0)
    return SimplificationResult::Tautology;
  return SimplificationResult::OK;
}
//---------------------------------------------------------------------------
set<Term*> FOF::find_free_variables() const {
  set<Term*> result;
  set<Term*> free; 
  Term* to_remove; 
  switch (type) {
    case FOFType::Empty:
      cerr << "You shouldn't be doing this with an FOFType::Empty!" << endl;
      break;
    case FOFType::Atom:
      for (const Term* p : pred.get_args()) {
        free = p->all_variables();
        result.insert(free.begin(), free.end());
      }
      break;
    case FOFType::Neg:
    case FOFType::And: 
    case FOFType::Or: 
    case FOFType::Imp:
    case FOFType::Iff: 
      for (const FOF& f : sub_formulas) {
        free = f.find_free_variables();
        result.insert(free.begin(), free.end());
      }
      break;
    case FOFType::A: 
    case FOFType::E:
      result = sub_formulas[0].find_free_variables();
      to_remove = term_index->add_variable_term(var);
      result.erase(to_remove);
      break;
    default:
      break;
  }
  return result;
}
//---------------------------------------------------------------------------
ostream& operator<<(ostream& out, const FOF& f) {
  out << f.to_string();
  return out;
}
