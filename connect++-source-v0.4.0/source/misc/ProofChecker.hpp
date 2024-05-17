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

#ifndef PROOFCHECKER_HPP
#define PROOFCHECKER_HPP

#include<iostream>
#include<string>
#include<vector>

#include "Matrix.hpp"
#include "Unifier.hpp"

using std::vector;
using std::pair;
using std::get;

/**
* \brief We're using a simple internal representation of a proof here.
*
* The type of proof step (string) is followed by numbers (size_t). This is 
* exactly the same format as the Prolog, stack-based summary.
*/
using ProofLine = pair<string, vector<size_t>>;
/**
* \brief A proof is just a collection of the steps described above.
*/
using ProofType = vector<ProofLine>;
/**
* \brief While verifying a proof we need to maintain a collection of 
*        right-hand branches to be finished.
*/
using RightStackItem = std::tuple<Clause, 
                                  vector<Literal>, 
                                  vector<Literal>,
                                  size_t>;

/** 
* This is an alternative to the Prolog proof 
* checker. It uses the contents of stack and 
* matrix to re-construct the proof, checking as 
* it goes that the substitutions work. As an 
* extra check, it re-does unifications rather 
* than using anything stored. 
*
* Note: undoes its substitutions when it's 
* finished.
*/
class ProofChecker {
private:
    /**
    * \brief Needed as we need to generate things with new variables.
    */
    VariableIndex* vi;
    /**
    * \brief Needed as we need to generate things with new variables.
    */
    TermIndex* ti;
    /**
    * \brief Reference to the problem matrix.
    */
    Matrix& matrix;
    /**
    * \brief Part of the representation of the current state of the proof.
    */
    Clause C;
    /**
    * \brief Part of the representation of the current state of the proof.
    */
    vector<Literal> P;
    /**
    * \brief Part of the representation of the current state of the proof.
    */
    vector<Literal> Lem;
    /**
    * \brief Straightforward internal representation of the proof.
    */
    ProofType proof;
    /**
    * \brief Needed to check some proof steps.
    */
    Unifier u;
    /**
    * \brief Collection of right-hand branches to complete. 
    */
    vector<RightStackItem> r_stack;
    /**
    * \brief Use this to undo the substitutions when you've finished.
    */
    size_t num_subs;
    /**
    * \brief Check index. Self-explanatory!
    */
    bool C_i_ok(size_t) const;
    /**
    * \brief Check index. Self-explanatory!
    */
    bool Lit_i_ok(size_t) const;
    /**
    * \brief Check index. Self-explanatory!
    */
    bool P_i_ok(size_t) const;
    /**
    * \brief Check index. Self-explanatory!
    */
    bool Lem_i_ok(size_t) const;
    /**
    * \brief Make a string containing the current state.
    */
    string state_to_string() const;
public:
    ProofChecker() = delete;
    ProofChecker(Matrix&, const ProofType&, VariableIndex*, TermIndex*);
    /**
    *  \brief Check the proof and produce a string with a 
    *         detailed description.
    */
    pair<bool, string> check_proof_verbose();
     /**
    *  \brief Check the proof quietly.
    */
    bool check_proof();
};

#endif