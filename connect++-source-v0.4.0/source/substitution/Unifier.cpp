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

#include "Unifier.hpp"

//----------------------------------------------------------------------
UnificationOutcome Unifier::operator()(Term* term1, Term* term2) {
    to_do.clear();
    to_do.push_front(UPair(term1, term2));
    return complete_unification();
}
//----------------------------------------------------------------------
UnificationOutcome Unifier::operator()(const vector<Term*>& t1s,
                                       const vector<Term*>& t2s) {
    if (t1s.size() != t2s.size())
        return UnificationOutcome::ConflictFail;
    to_do.clear();
    auto i = t2s.begin();
    for (Term* term1 : t1s) {
        to_do.push_front(UPair(term1, *i));
        i++;
    }
    return complete_unification();
}
//----------------------------------------------------------------------
UnificationOutcome Unifier::operator()(Literal* l1, Literal* l2) {
    if (!l1->is_compatible_with(l2)) {
        cerr << "ERROR" << ": ";
        cerr << "You're trying to unify non-compatible literals." << endl;
        cerr << "ERROR" << ": " << *l1 << endl;
        cerr << "ERROR" << ": " << *l2 << endl;
    }
    const vector<Term*>& args1 = l1->get_args();
    const vector<Term*>& args2 = l2->get_args();
    return operator()(args1, args2);
}
//----------------------------------------------------------------------
UnificationOutcome Unifier::operator()(const Literal& l1,
                                       const Literal& l2) {
    if (!l1.is_compatible_with(&l2)) {
        cerr << "ERROR" << ": ";
        cerr << "You're trying to unify non-compatible literals." << endl;
        cerr << "ERROR" << ": " << l1 << endl;
        cerr << "ERROR" << ": " << l2 << endl;
    }
    const vector<Term*>& args1 = l1.get_args();
    const vector<Term*>& args2 = l2.get_args();
    return operator()(args1, args2);
}
//----------------------------------------------------------------------
UnificationOutcome Unifier::complete_unification() {
    s.clear();
    while (to_do.size() > 0) {
        // Get the next thing from the queue and split it up.
        UPair upair(to_do.front());
        Term* t1(upair.first);
        Term* t2(upair.second);
        // Make sure you do this! Many long debugging sessions
        // await if you ignore my advice.
        t1 = t1->skip_leading_variables();
        t2 = t2->skip_leading_variables();
        to_do.pop_front();
        // Work out exactly what everything is.
        bool t1_is_fun = t1->subbed_is_function();
        bool t2_is_fun = t2->subbed_is_function();
        bool t1_is_var = t1->subbed_is_variable();
        bool t2_is_var = t2->subbed_is_variable();
        Variable* t1v = nullptr;
        if (t1_is_var)
            t1v = t1->get_v()->subbed_variable();

        // Delete
        if (t1->subbed_equal(t2)) {
            continue;
        }
        // Swap
        if (t1_is_fun && t2_is_var) {
            to_do.push_back(UPair(t2, t1));
            continue;
        }
        // Occurs
        if (t1_is_var && t2_is_fun && t2->contains_variable(t1v)) {
            backtrack();
            return UnificationOutcome::OccursFail;
        }
        // Eliminate
        if (t1_is_var && !t2->contains_variable(t1v)) {
            s.push_back(t1v, t2);
            t1v->substitute(t2);
            continue;
        }
        // Decompose/Conflict
        if (t1_is_fun && t2_is_fun) {
            // Conflict
            if ((t1->get_subbed_f() != t2->get_subbed_f()) ||
                (t1->get_subbed_arity() != t2->get_subbed_arity())) {
                backtrack();
                return UnificationOutcome::ConflictFail;
            }
            // Decompose
            else {
                size_t n_args = t1->arity();
                for (size_t i = 0; i < n_args; i++) {
                    to_do.push_back(UPair((*t1)[i], (*t2)[i]));
                }
                continue;
            }
        }
    }
    return UnificationOutcome::Succeed;
}
//----------------------------------------------------------------------
void Unifier::backtrack() {
    s.backtrack();
    s.clear();
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const UnificationOutcome& o) {
    switch(o) {
        case UnificationOutcome::Succeed:
            out << "Unification: success.";
            break;
        case UnificationOutcome::ConflictFail:
            out << "Unification: failed due to conflict.";
            break;
        case UnificationOutcome::OccursFail:
            out << "Unification: failed due to occurs check.";
            break;
        default:

            break;
    }
    return out;
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Unifier& u) {
    out << u.to_string();
    return out;
}
