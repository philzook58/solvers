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

#include "ProofChecker.hpp"

//----------------------------------------------------------------------
ProofChecker::ProofChecker(Matrix& m, 
                           const ProofType& p,
                           VariableIndex* _vi,
                           TermIndex* _ti)
: vi(_vi)
, ti(_ti)
, matrix(m)
, C()
, P()
, Lem()
, proof(p) 
, u()
, r_stack()
, num_subs(0)
{}
//----------------------------------------------------------------------
bool ProofChecker::C_i_ok(size_t i) const {
    return (i >= 0 && i < matrix.get_num_clauses());
}
//----------------------------------------------------------------------
bool ProofChecker::Lit_i_ok(size_t i) const {
    return (i >= 0 && i < C.size());
}
//----------------------------------------------------------------------
bool ProofChecker::P_i_ok(size_t i) const {
    return (i >= 0 && i < P.size());
}
//----------------------------------------------------------------------
bool ProofChecker::Lem_i_ok(size_t i) const {
    return (i >= 0 && i < Lem.size());
}
//----------------------------------------------------------------------
string ProofChecker::state_to_string() const {
    string s("C = ");
    s += C.to_string() += "\nC = ";
    s += C.to_string(true) += " substituted.\n\nP = { ";
    for (const Literal& l : P) 
        s += l.to_string() += " ";
    s += " }\nP = { ";
    for (const Literal& l : P) 
        s += l.to_string(true) += " ";
    s += " } substituted.\n\nL = { ";
    for (const Literal& l : Lem)
        s += l.to_string() += " ";
    s += " }\nL = { ";
    for (const Literal& l : Lem)
        s += l.to_string(true) += " ";
    s += " } substituted.\n\n";
    return s;
}
//----------------------------------------------------------------------
pair<bool, string> ProofChecker::check_proof_verbose() {
    bool result = true;
    string out_string;

    for (size_t i = 0; i < proof.size(); i++) {
        out_string += "** Proof step: ";
        out_string += std::to_string(i) += " *************************************************\n";

        ProofLine line = proof[i];

        if (line.first == "start") {
            out_string += "Found a Start step with C = ";
            size_t C_i = line.second[0];
            out_string += std::to_string(C_i) += ".\n";
            if (i != 0) {
                out_string += "Error: you can only use the Start rule as step 1 of a proof.\n";
                result = false;
                break;
            }
            if (!C_i_ok(C_i)) {
                out_string += "Error: the start clause index is out of range.\n";
                result = false;
                break;
            }
            Clause start = matrix[C_i];
            out_string += "C = ";
            out_string += start.to_string() += "\n";
            C = start.make_copy_with_new_vars(*vi, *ti);
            out_string += "Starting from state (with new variables):\n";
            out_string += state_to_string();
        }
        else if (line.first == "left_branch") {
            size_t Lit_i = line.second[0];
            size_t newC_i = line.second[1];
            size_t newLit_i = line.second[2];
            size_t d = line.second[3];
            out_string += "Found an Extension step (left) with: L = ";
            out_string += std::to_string(Lit_i) += ", C' = ";
            out_string += std::to_string(newC_i) += ", L' = ";
            out_string += std::to_string(newLit_i) += ", depth = ";
            out_string += std::to_string(d) += ".\n";
            if (!Lit_i_ok(Lit_i)) {
                out_string += "Error: the clause literal index is out of range.\n";
                result = false;
                break;
            }
            Literal Lit = C[Lit_i];
            out_string += "L = ";
            out_string += Lit.to_string() += "\nL = ";
            out_string +=  Lit.to_string(true) += " substituted.\n";
            if (!C_i_ok(newC_i)) {
                out_string += "Error: the new clause index is out of range.\n";
                result = false;
                break;
            }
            Clause newC = matrix[newC_i];
            out_string += "C' = ";
            out_string += newC.to_string() += "\n";
            Clause newCcopy = newC.make_copy_with_new_vars(*vi, *ti);
            out_string += "C' = ";
            out_string += newCcopy.to_string() += " with new variables.\n";
            if (newLit_i < 0 || newLit_i >= newC.size()) {
                out_string += "Error: the new literal index is out of range.\n";
                result = false;
                break;
            }
            Literal newLit = newCcopy[newLit_i];
            Literal newLitinv = newCcopy[newLit_i];
            newLitinv.invert();
            out_string += "~L' = ";
            out_string += newLitinv.to_string() += " and has new variables.\n";
            UnificationOutcome out = u(Lit, newLitinv);
            if (out != UnificationOutcome::Succeed) {
                out_string += "Error: these literals can not be unified.\n";
                result = false;
                break;
            }
            num_subs++;
            out_string += "Literals L and ~L' are unified by: ";
            out_string += u.to_string() += "\n";
            
            // Make the material for the right branch.
            vector<Literal> rightP(P);
            vector<Literal> rightLem(Lem);
            rightLem.push_back(Lit);
            Clause rightC(C);
            rightC.drop_literal(Lit_i);
            RightStackItem r_item;
            r_item = std::make_tuple(rightC, rightP, rightLem, d);
            r_stack.push_back(r_item);

            // Make the material for the left branch.
            newCcopy.drop_literal(newLit_i);
            C = newCcopy;
            P.push_back(Lit);
            out_string += "Continuing with:\n";
            out_string += state_to_string();
        }
        else if (line.first == "reduction") {
            size_t Lit_i = line.second[0];
            size_t P_i = line.second[1];
            out_string += "Found a Reduction step with L = ";
            out_string += std::to_string(Lit_i) += " and L' = ";
            out_string += std::to_string(P_i) += ".\n";
            if (!Lit_i_ok(Lit_i)) {
                out_string += "Error: the clause literal index is out of range.\n";
                result = false;
                break;
            }
            if (!P_i_ok(P_i)) {
                out_string += "Error: the path literal index is out of range.\n";
                result = false;
                break;
            }
            out_string += "L = ";
            Literal l1 = C[Lit_i];
            out_string += l1.to_string() += "\nL = ";
            out_string += l1.to_string(true) += " substituted.\n"; 
            out_string += "~L' = ";
            Literal l2inv = P[P_i];
            l2inv.invert();
            Literal l2 = P[P_i];
            out_string += l2inv.to_string() += "\n~L' = ";
            out_string += l2inv.to_string(true) +=  " substituted.\n";
            UnificationOutcome out = u(l1, l2inv);
            if (out != UnificationOutcome::Succeed) {
                out_string += "Error: these literals can not be unified.\n";
                result = false;
                break;
            }
            num_subs++;
            out_string += "Literals L and ~L' are unified by: ";
            out_string += u.to_string() += "\n";
            Lem.push_back(l1);
            C.drop_literal(Lit_i);
            out_string += "Continuing with:\n";
            out_string += state_to_string();
        }
        else if (line.first == "lemmata") {
            size_t Lit_i = line.second[0];
            size_t Lem_i = line.second[1];
            out_string += "Found a Lemma step with L = ";
            out_string += std::to_string(Lit_i) += " and L' = ";
            out_string += std::to_string(Lem_i) += ".\n";
            if (!Lit_i_ok(Lit_i)) {
                out_string += "Error: the clause literal index is out of range.\n";
                result = false;
                break;
            }
            if (!Lem_i_ok(Lem_i)) {
                out_string += "Error: the lemma literal index is out of range.\n";
                result = false;
                break;
            }
            out_string += "L = ";
            Literal l1 = C[Lit_i];
            out_string += l1.to_string() += "\nL = ";
            out_string += l1.to_string(true) += " substituted.\n"; 
            out_string += "L' = ";
            Literal l2 = Lem[Lem_i];
            out_string += l2.to_string() += "\nL' = ";
            out_string += l2.to_string(true) += " substituted.\n";
            if (!l1.subbed_equal(&l2)) {
                out_string += "Error: these literals are not equal with the current substitution.\n";
                result = false;
                break;
            }
            out_string += "Literals L and L' are equal with the current substitution.\n";
            C.drop_literal(Lit_i);
            out_string += "Continuing with:\n";
            out_string += state_to_string();
        }
        else if (line.first == "right_branch") {
            size_t new_d = line.second[0];
            out_string += "Found a right branch step with depth ";
            out_string += std::to_string(new_d) += ".\n";
            if (r_stack.empty()) {
                out_string += "Error: the right stack is empty.\n";
                result = false;
                break;
            }
            if (C.size() != 0) {
                out_string += "Error: this should be an axiom but C is not empty.\n";
                result = false;
                break;
            }
            out_string += "We have an Axiom!\n";
            RightStackItem r_item(r_stack.back());
            r_stack.pop_back();
            C = get<0>(r_item);
            P = get<1>(r_item);
            Lem = get<2>(r_item);
            size_t d = get<3>(r_item);
            if (d != new_d) {
                out_string += "Error: the depths don't match.\n";
                result = false;
                break;
            }
            out_string += "Continuing with:\n";
            out_string += state_to_string();
        }
        else {
            out_string += "The proof is badly-formed.\n";
            result = false;
            break;
        }
    }
    if (!C.empty()) {
        out_string += "Error: you haven't ended with an Axiom.\n";
        result = false;
    }
    if (result) {
        out_string += "SUCCESS! The proof is good.\n";
    }    
    for (size_t i = 0; i < num_subs; i++) {
        u.backtrack();
    }
    return pair<bool, string>(result, out_string);
}
//----------------------------------------------------------------------
bool ProofChecker::check_proof() {
    bool result = true;

    for (size_t i = 0; i < proof.size(); i++) {

        ProofLine line = proof[i];

        if (line.first == "start") {
            size_t C_i = line.second[0];
            if (i != 0) {
                result = false;
                break;
            }
            if (!C_i_ok(C_i)) {
                result = false;
                break;
            }
            Clause start = matrix[C_i];
            C = start.make_copy_with_new_vars(*vi, *ti);
        }
        else if (line.first == "left_branch") {
            size_t Lit_i = line.second[0];
            size_t newC_i = line.second[1];
            size_t newLit_i = line.second[2];
            size_t d = line.second[3];
            if (!Lit_i_ok(Lit_i)) {
                result = false;
                break;
            }
            Literal Lit = C[Lit_i];
            if (!C_i_ok(newC_i)) {
                result = false;
                break;
            }
            Clause newC = matrix[newC_i];
            Clause newCcopy = newC.make_copy_with_new_vars(*vi, *ti);
            if (newLit_i < 0 || newLit_i >= newC.size()) {
                result = false;
                break;
            }
            Literal newLit = newCcopy[newLit_i];
            Literal newLitinv = newCcopy[newLit_i];
            newLitinv.invert();
            UnificationOutcome out = u(Lit, newLitinv);
            if (out != UnificationOutcome::Succeed) {
                result = false;
                break;
            }
            num_subs++;
            
            // Make the material for the right branch.
            vector<Literal> rightP(P);
            vector<Literal> rightLem(Lem);
            rightLem.push_back(Lit);
            Clause rightC(C);
            rightC.drop_literal(Lit_i);
            RightStackItem r_item;
            r_item = std::make_tuple(rightC, rightP, rightLem, d);
            r_stack.push_back(r_item);

            // Make the material for the left branch.
            newCcopy.drop_literal(newLit_i);
            C = newCcopy;
            P.push_back(Lit);
        }
        else if (line.first == "reduction") {
            size_t Lit_i = line.second[0];
            size_t P_i = line.second[1];
            if (!Lit_i_ok(Lit_i)) {
                result = false;
                break;
            }
            if (!P_i_ok(P_i)) {
                result = false;
                break;
            }
            Literal l1 = C[Lit_i];
            Literal l2inv = P[P_i];
            l2inv.invert();
            Literal l2 = P[P_i];
            UnificationOutcome out = u(l1, l2inv);
            if (out != UnificationOutcome::Succeed) {
                result = false;
                break;
            }
            num_subs++;
            Lem.push_back(l1);
            C.drop_literal(Lit_i);
        }
        else if (line.first == "lemmata") {
            size_t Lit_i = line.second[0];
            size_t Lem_i = line.second[1];
            if (!Lit_i_ok(Lit_i)) {
                result = false;
                break;
            }
            if (!Lem_i_ok(Lem_i)) {
                result = false;
                break;
            }
            Literal l1 = C[Lit_i];
            Literal l2 = Lem[Lem_i];
            if (!l1.subbed_equal(&l2)) {
                result = false;
                break;
            }
            C.drop_literal(Lit_i);
        }
        else if (line.first == "right_branch") {
            size_t new_d = line.second[0];
            if (r_stack.empty()) {
                result = false;
                break;
            }
            if (C.size() != 0) {
                result = false;
                break;
            }
            RightStackItem r_item(r_stack.back());
            r_stack.pop_back();
            C = get<0>(r_item);
            P = get<1>(r_item);
            Lem = get<2>(r_item);
            size_t d = get<3>(r_item);
            if (d != new_d) {
                result = false;
                break;
            }
        }
        else {
            result = false;
            break;
        }
    }
    if (!C.empty()) {
        result = false;
    } 
    for (size_t i = 0; i < num_subs; i++) {
        u.backtrack();
    }
    return result;
}
    

  
