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

#ifndef PROOFPRINTER_HPP
#define PROOFPRINTER_HPP

#include<iostream>
#include<fstream>
#include<filesystem>

#include "StackItem.hpp"

using std::filesystem::path;

using ProofLine = pair<string, vector<size_t>>;
using ProofType = vector<ProofLine>;

/**
* \brief Simple function to display the internal 
*        data structure containing a proof.
*
* @param proof Data structure containing proof stack.
*/
void show_internal_proof(const ProofType&);

/**
* \brief Class for rendering a proof in various formats.
*
* A proof is supplied as a stack of StackItem produced by 
* StackProver.
*
* At present, this class will render a proof as LaTeX, or in a 
* Prolog-readable certificate format that can be passed through 
* the Connect++ certificate checker.
*
* It will be extended later if a standard format for connection 
* calculus proof certificates is agreed -- this discussion is 
* ongoing.
*/
class ProofPrinter {
private:
  /**
  * \brief Pointer to the output of StackProver.
  */
  vector<StackItem>* p;
  /**
  * \brief Helper for producing LaTeX output.
  *
  * Make a string with the LaTeX reprresentation 
  * of the clause, path and lemmata list.
  *
  * @param item_p Pointer to StackItem to render
  */
  string make_LaTeX_state(StackItem*) const;
  /**
  * \brief Helper for producing LaTeX output.
  *
  * A bit tricky. This should produce 
  * \prf???{axioms1}{axioms2} with the
  * {conclusion} being added by the caller. 
  * The exception is right branches, which can 
  * include the conclusion themselves.
  *
  * @param item_p Pointer to StackItem to render
  */
  string make_LaTeX_subtree(StackItem*) const;
public:
  /**
  * \brief Basic constructor.
  */
  ProofPrinter() : p(nullptr) {};
  /**
  * \brief The constructor yuo want.
  *
  * @param _p Pointer to the output of StackProver. 
  */
  ProofPrinter(vector<StackItem>* _p) : p(_p) {};
  /**
  * \brief Basic set method.
  *
  * @param _p Pointer to the output of StackProver. 
  */
  inline void set_proof(vector<StackItem>* _p) { p = _p; }
   /**
  * \brief Basic set method.
  */
  inline void clear() { p = nullptr; }
  /**
  * \brief Convert to LaTeX and store in the specified file.
  *
  * @param path_to_file Path of file to store to
  * @param path_to_input_file File for the problem being solved
  * @param matrix_as_latex LaTeX formatted matrix
  */
  void make_LaTeX(const path&, const path&, const string&);
  /**
  * \brief Convert to a form suitable for use by the 
  *        Prolog proof checker and write to a file.
  *
  * @param path_to_file Path for output file
  */
  void make_Prolog(const path&);
  /**
  * \brief Show the proof in Prolog format.
  */
  void show_Prolog();
  /**
  * \brief Show the proof in a TPTP-friendly format.
  */
  void show_tptp();
  /**
  * \brief Make a simple data structure representing 
  *        the proof stack.
  *
  * The first part each element of the output is 
  * a string naming the proof rules. The second 
  * contains the associated numbers.
  */
  vector<pair<string, vector<size_t>>> make_internal() const;
};

#endif
