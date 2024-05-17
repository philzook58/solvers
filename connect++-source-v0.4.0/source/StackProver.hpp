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

#ifndef STACKPROVER_HPP
#define STACKPROVER_HPP

#include<iostream>
#include<string>
#include<filesystem>
#include <chrono>

#include "FunctionIndex.hpp"
#include "PredicateIndex.hpp"
#include "StackItem.hpp"
#include "Matrix.hpp"
#include "TPTPParser.hpp"
#include "ProverOutcome.hpp"
#include "SubstitutionStack.hpp"
#include "ProofPrinter.hpp"
#include "Interval.hpp"
#include "cursor.hpp"
#include "PathUtilities.hpp"
#include "vic_strings.hpp"

using std::string;
using std::get;

namespace fs = std::filesystem;
namespace chrono = std::chrono;

using namespace tptp_parser;

/**
* \brief Prover using a pair of stacks to conduct the proof search.
*
* This version is a straightforward translation of the proof 
* method to search for a tree with all its leaves being axioms. 
* However, by not using recursion we retain the ability to fully 
* control backtracking and therefore, amongst other things, 
* find all possible proofs.
*
* This is really the main class for Connect++, and everything 
* else essentially exists to support it. There's a lot going 
* on here so hang on to your hat!
*
* This is also one of only a small number of places where you'll 
* need to modify stuff to incorporate machine learning. The main 
* advice is simple: take notice of the comments that point out where 
* to do this, and be *very* careful to leave the general 
* stack manipulation code alone unless you *really* know what 
* you're doing, because that stuff is quite easy to break.
*/
class StackProver {
private:
    /**
    * \brief How many prdicates does the problem of interest 
    *        have?
    */
    size_t num_preds;
    /**
    * \brief This class needs one of each kind of index to 
    *        keep track of Variables, Terms etc.
    */
    VariableIndex var_index;
    /**
    * \brief This class needs one of each kind of index to 
    *        keep track of Variables, Terms etc.
    */
    FunctionIndex fun_index;
    /**
    * \brief This class needs one of each kind of index to 
    *        keep track of Variables, Terms etc.
    */
    TermIndex term_index;
    /**
    * \brief This class needs one of each kind of index to 
    *        keep track of Variables, Terms etc.
    */
    PredicateIndex pred_index;
     /**
    * \brief There is a separate stack to make application 
    *        and removal of substitutions straightforward.
    */
    SubstitutionStack sub_stack;
    /**
    * \brief This is populated by the StackProver::set_up_start_clauses
    *        method.
    *
    * That method looks at the settings for start clauses and tries 
    * to achieve them all in a sensible way. Initially this 
    * indicates which clauses to use to start, but then 
    * stores the results obtained after trying each 
    * possibility.
    */
    vector<StartClauseStatus> results;
    /**
    * \brief A copy of the matrix you're working with.
    */
    Matrix matrix;
    /**
    * \brief At any point in the search process this is a 
    *        copy of the path for the current node in the 
    *        proof being constructed.
    */
    SimplePath path;
    /**
    * \brief At any point in the search process this is a 
    *        copy of the clause for the current node in the 
    *        proof being constructed.
    */
    Clause new_C;
    /**
    * \brief At any point in the search process this is a 
    *        copy of the list of lemmata for the current node in the 
    *        proof being constructed.
    */
    Lemmata lemmata;
    /**
    * \brief We need a single Unifier to use throught the process.
    */
    Unifier u;
    /**
    * \brief Stores the next action from the current StackItem.
    */
    InferenceItem action;
    /**
    * \brief Pointer to the current StackItem.
    *
    * Be very careful with this. At present its use is fine 
    * because I don't think that the stack gets modified while 
    * the pointer is in use. BUT it may be a good future modification 
    * to make this an index rather than a pointer in case we run 
    * into trouble with the vector class moving things in memory.
    */
    StackItem* si;
    /**
    * \brief Self-explanatary.
    */
    uint32_t current_depth_limit;
    /**
    * \brief Self-explanatary.
    */
    uint32_t current_depth;
    /**
    * \brief Self-explanatary.
    */
    bool depth_limit_reached;
    /**
    * \brief Problem status, if found in input file.
    */
    string status;
    /**
    * \brief TPTP-friendly description of the clause conversion.
    */
    string tptp_conversion_string;
    /**
    * \brief Main stack: this is constructed by the search 
    *        process and, if completed, represents a proof.
    */
    vector<StackItem> stack;
    /**
    * \brief We build the proof by trying the left branches of 
    *        extensions first: this stack keeps track of the 
    *        right branches that we need to come back to.
    */
    vector<StackItem> right_branch_stack;
    /**
    * \brief Are we moving up or down the stack?
    */
    bool backtrack;
    /**
    * \brief You need one of these to print LaTeX output 
    *        or any kind of proof certificate.
    */
    ProofPrinter proof_printer;
    /**
    * \brief Path for the problem of interest.
    */
    fs::path problem_path;
    /**
    * \brief How often do you output updates about progress?
    */
    Interval output_interval;
    /**
    * \brief We'll be keeping some simple statistics about the 
    *        search process.
    *
    * Note that at present these statistics include *everything* 
    * tried over *all* steps in a schedule.
    */
    static uint32_t reductions_tried;
    /**
    * \brief We'll be keeping some simple statistics about the 
    *        search process.
    */
    static uint32_t extensions_tried;
    /**
    * \brief We'll be keeping some simple statistics about the 
    *        search process.
    */
    static uint32_t lemmata_tried;
    /**
    * \brief We'll be keeping some simple statistics about the 
    *        search process.
    */
    static uint32_t right_branches_started;
    /**
    * \brief If we're searching for multiple proofs, keep count  
    *        of which one this is.
    */
    uint32_t proof_count;
    /**
    * \brief Are we using a timeout?
    */
    bool use_timeout;
    /**
    * \brief When do we stop because of a timeout?
    */
    chrono::steady_clock::time_point end_time;
    /**
    * \brief Set up printing according to verbosity.
    */
    verbose_print::VPrint show;
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    // Here is where the heavy lifting happens.
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    /**
    * \brief This runs the proof search from a given Start Move.
    */
    ProverResult go();
    /**
    * \brief Fill the vector of possible actions with 
    *        everything available.
    */
    void populate_stack_item();
    /**
    * \brief Take a single inference (action) and update 
    *        the stacks accordingly.
    */
    void extend_with_action();
    /**
    * \brief Test for the depth limit.
    */
    bool depth_limited();
    /**
    * \brief Test to see if you're at an axiom.
    */
    bool axiom() const;
    /**
    * \brief Start a right branch to continue from an axiom. 
    *
    * You do this by taking the next available thing from the 
    * stack of right branches.
    */
    void process_axiom_forward();
    /**
    * \brief Basic, single step backtrack on the stack. 
    *
    * Careful though: you need to treat the depth of the tree 
    * correctly if you want to keep track of it.
    */
    void backtrack_once();
    /**
    * \brief One of several different kinds of backtracking.
    */
    void reduction_backtrack();
    /**
    * \brief One of several different kinds of backtracking.
    */
    void lemmata_backtrack();
    /**
    * \brief One of several different kinds of backtracking.
    */
    void left_extension_backtrack();
    /**
    * \brief One of several different kinds of backtracking.
    */
    void right_extension_backtrack();
    /**
    * \brief The start clauses to use depend on the settings, and 
    *        the settings can change.
    */
    void set_up_start_clauses();
    /**
    * \brief Reset everything so that you can start from 
    *        a specified start clause.
    */
    void reset_for_start() {
      depth_limit_reached = false;
      si = nullptr;
      backtrack = false;
      path.clear();
      stack.clear();
      lemmata.clear();
      right_branch_stack.clear();
      sub_stack.clear();
    }
    /**
    * \brief Keep track of whether there were any FOF formulas in the problem 
    *        file.
    */
    bool cnf_only;
    /**
    * \brief Keep track of whether the parser found the conjecture to be true.
    */
    bool conjecture_true;
     /**
    * \brief Keep track of whether the parser found the conjecture to be false.
    */
    bool conjecture_false;
    /**
    * \brief Keep track of whether the parser found a conjecture in the problem file.
    */
    bool conjecture_missing;
    /**
    * \brief Keep track of whether the parser simplified the conjecture away.
    */
    bool negated_conjecture_removed;
    /**
    * \brief Keep track of whether the parser found that it's an FOF 
    *        problem with axioms before simplification.
    */
    bool fof_has_axioms;
    /**
    * \brief Keep track of whether the parser found that it's an FOF 
    *        problem with axioms after simplification.
    */
    bool simplified_fof_has_axioms;
public:
    /**
    * \brief You only need a basic constructor.
    */
    StackProver();
    /**
    * \brief Don't try to copy this.
    */
    StackProver(const StackProver&) = delete;
    StackProver(const StackProver&&) = delete;
    StackProver& operator=(const StackProver&) = delete;
    StackProver& operator=(const StackProver&&) = delete;
    /**
    * \brief Straightforward get method.
    */
    std::tuple<VariableIndex*, FunctionIndex*, PredicateIndex*, TermIndex*> get_indexes() {
      auto result = std::make_tuple(&var_index, &fun_index, &pred_index, &term_index);
      return result;
    }
    /**
    * \brief Straightforward get method.
    */
    string get_status() const { return status; }
    /**
    * \brief Set a timeout.
    *
    * A StackProver is always constructed to have no timeout. This sets
    * a timeout to use in seconds. The parameters are separate from the
    * params::???? values as the latter apply globally whereas these allow
    * for schedules to be constructed.
    *
    * @param time the time to stop: you will need to know about the 
    *             standard library!
    */
    void set_timeout(chrono::steady_clock::time_point time) {
      use_timeout = true;
      end_time = time;
    }
    /**
    * \brief Set the path for the problem being solved. U
    *
    * Used only to produce nice output.
    */
    void set_problem_path(fs::path& p) { problem_path = p; }
    /**
    * \brief Set the number of predicates.
    *
    * But *don't*! You should never need to do this.
    */
    void set_num_preds(size_t);
    /**
    * \brief Obviously, reads a problem from a TPTP file.
    *
    * Does pretty much all of the setup required.
    *
    * @param file_name Name of the file to use.
    * @param found_conjecture Used to indicate whether a 
    *                         conjecture is found in the problem.
    * @param fof_size Number of first-order formulas found.
    */
    void read_from_tptp_file(const string&, bool&, size_t&);
    /**
    * \brief After reading a problem in which = and/or 
    *        != appears, add the axioms for equality.
    *
    * @param equals_predicate Pointer to a Predicate representing 
    *                         equals. This will have been obtained 
    *                         as an output from parsing the input 
    *                         file.
    */
    void add_equality_axioms(Predicate*);
    /**
    * \brief Deterministically reorder the matrix n times.
    *
    * @param n Number of times to reorder.
    */
    void deterministic_reorder(uint32_t n) {
      matrix.deterministic_reorder(n);
    }
    /**
    * \brief Randomly reorder the matrix.
    */
    void random_reorder() {
      matrix.random_reorder();
    }
    /**
    * \brief Randomly reorder the literals in each clause 
    *        in the matrix.
    */
    void random_reorder_literals() {
      matrix.random_reorder_literals();
    }
    /**
    * \brief Show a nicely formatted matrix.
    */
    void show_matrix() {
      cout << "Matrix:" << endl;
      cout << matrix.to_string() << endl;
    }
    /**
    * \brief Get a reference to the matrix.
    */
    Matrix& get_matrix() {
      return matrix;
    };
    /**
    * \brief Find out whether the problem is 
    *        CNF only.
    */
    bool problem_is_cnf_only() const {
      return cnf_only;
    }
    /**
    * \brief Find out whether the problem's conjecture  
    *        is $true.
    */
    bool problem_has_true_conjecture() const {
      return conjecture_true;
    }
    /**
    * \brief Find out whether the problem's conjecture  
    *        is $false.
    */
    bool problem_has_false_conjecture() const {
      return conjecture_false;
    }
    /**
    * \brief Find out whether the problem's conjecture  
    *        is missing, in the sense that it didn't appear 
    *        in the input file.
    */
    bool problem_has_missing_conjecture() const {
      return conjecture_missing;
    }
    /**
    * \brief Find out whether the problem's   
    *        negated conjecture was simplified out.
    */
    bool problem_has_negated_conjecture_removed() const {
      return negated_conjecture_removed;
    }
    /**
    * \brief Find out from the parser whether the problem had 
    *        axioms before simplification.
    */
    bool problem_has_fof_axioms() const {
      return fof_has_axioms;
    }
    /**
    * \brief Find out from the parser whether the problem had axioms 
    *        after simplification.
    */
    bool simplified_problem_has_fof_axioms() const {
      return simplified_fof_has_axioms;
    }
    string get_tptp_conversion_string() const {
      return tptp_conversion_string;
    }
    /**
    * \brief Show a Prolog-formatted proof.
    */
    void show_tptp_proof() {
      cout << endl << "% Problem matrix:" << endl;
      matrix.show_tptp();
      cout << endl << "% Proof stack:" << endl;
      proof_printer.show_tptp();
    }
    /**
    * \brief Here is where the magic happens. 
    *
    * You should only need to load the problem and call 
    * this method.
    */
    ProverOutcome prove();
    /**
    * \brief Get an internal representation of the 
    *        proof stack.
    */
    vector<pair<string, vector<size_t>>> get_internal_proof() const;
    /**
    * \brief Display counts of number of extensions tried and 
    *        so on.
    */
    void show_statistics() const;
    /* 
    * The remaining material is really just for debugging.
    */
    void show_matrix() const { cout << matrix << endl; }
    void show_path() const { cout << path << endl; }
    void show_stack();
    void show_right_stack();
    void show_term_index() { cout << term_index << endl; }      
    friend ostream& operator<<(ostream&, const StackProver&);
};

#endif
