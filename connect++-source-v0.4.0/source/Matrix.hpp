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

#ifndef MATRIX_HPP
#define MATRIX_HPP

#include<iostream>
#include<fstream>
#include<filesystem>
#include<iomanip>
#include<string>
#include<vector>
#include<tuple>
#include<algorithm>
#include<random>

#include "InferenceItem.hpp"
#include "Clause.hpp"
#include "ClauseComparisons.hpp"
#include "Unifier.hpp"
#include "Reorder.hpp"

using std::pair;
using std::tuple;
using std::vector;
using std::ostream;
using std::endl;
using std::setw;
using std::cout;
using std::filesystem::path;

/**
* \brief We want to be able to quickly identify where in 
*        each clause a particular literal lives
*        
* Store clause and position as pairs.
*/
using MatrixPairType = pair<ClauseNum, LitNum>;

/**
* \brief Representation of the Matrix within a proof.
*
* The Matrix itself never actually changes. However we do 
* want to be able to look things up quickly when finding 
* possible extension steps, so we build an index to help 
* with that.
*
* This class is also the natural place to implement the 
* finding of all extensions, and the start clause 
* heuristics.
*/
class Matrix {
private:
    /**
    * \brief The Matrix itself is just a set of Clauses.
    */
    vector<Clause> clauses;
    /**
    * \brief Keep track of which clauses are positive. 
    *
    * This allows start clause heuristics to be applied.
    */
    vector<bool> positive_clauses;
     /**
    * \brief Keep track of which clauses are negative. 
    *
    * This allows start clause heuristics to be applied.
    */
    vector<bool> negative_clauses;
     /**
    * \brief Keep track of which clauses are conjectures etc. 
    *
    * This allows start clause heuristics to be applied.
    */
    vector<string> clause_roles;
    /**
    * \brief You need to know how many equality axioms 
    *        there are in case you want to move them around.
    */
    uint32_t num_equals;
    /**
    * \brief It makes sense to keep a copy of the clauses 
    *        if your schedule reorders multiple times.
    */
    vector<Clause> clauses_copy;
     /**
    * \brief It makes sense to keep a copy of the roles
    *        if your schedule reorders multiple times.
    */
    vector<string> roles_copy;
    /**
    * \brief Remember whether you've saved a copy.
    */
    bool copy_saved;
    /**
    * \brief We want to be able to quickly identify where in 
    *        each clause a particular literal lives
    *        
    * Store clause and position as pairs in a row corresponding 
    * to the literal.
    */
    vector<vector<MatrixPairType>> index;
    /**
    * \brief Randomness for random reordering.
    */
    static std::mt19937 d;
    /**
    * \brief Find all possible extensions, given a Literal.
    *
    * Essentially this involves finding all the Clauses in the
    * Matrix containing a Literal complementary to the one of
    * interest, and selecting each of those Literals that unifies
    * with the one of interest. You can do this by traversing a
    * single row of the index.
    *
    * It's up to the caller to decide whether to clear the 
    * result.
    *
    * @param u Reference to a Unifier function object.
    * @param result Reference to a vector of InferenceItems.
    * @param lit Reference to the Literal of interest.
    * @param ind the index (position) of the Literal in its Clause.
    * @param var_index Reference to the VariableIndex.
    * @param term_index Reference to the TermIndex.
    */
    void find_extensions(Unifier&, vector<InferenceItem>&, const Literal&,
                         LitNum, VariableIndex&, TermIndex&);
    /**
    * \brief Store a copy of the clauses.
    */
    void make_clauses_copy() {
      clauses_copy.clear();
      clauses_copy = clauses;
      roles_copy.clear();
      roles_copy = clause_roles;
    }
    /**
    * \brief Template method for general sorting of clauses, which 
    *        sorts roles at the same time.
    *
    * ClauseComparisons.hpp contains function objects that can be used 
    * with this to implement different orderings.
    */
    template<class Comparison>
    void sort_clauses(Comparison comparison) {
      /*
      * Combine the clauses with their roles.
      */
      vector<ClauseAndRole> cr;
      size_t s = clauses.size();
      for (size_t i = 0; i < s; i++) {
        cr.push_back(ClauseAndRole(clauses[i], clause_roles[i]));
      }
      /*
      * Sort them according to the relevant ordering.
      */
      std::sort(cr.begin(), cr.end(), comparison);
      /*
      * Split them again and re-build the index.
      */
      clauses.clear();
      positive_clauses.clear();
      negative_clauses.clear();
      clause_roles.clear();
      size_t s2 = index.size();
      index.clear();
      index = vector<vector<MatrixPairType> >(s2, vector<MatrixPairType>());
      for (size_t i = 0; i < s; i++) {
        add_clause(cr[i].first, cr[i].second);
      }
    }
public:
    /**
    * \brief Use this constructor if you really want an empty 
    *        Matrix. 
    */
    Matrix()
    : clauses()
    , index()
    , positive_clauses()
    , negative_clauses()
    , clause_roles()
    , clauses_copy()
    , roles_copy()
    , copy_saved(false)
    {}
    /**
    * \brief Use this constructor when you know how many 
    *        predicates there are.
    *
    * @param num_predicates Number of predicates.
    */
    Matrix(size_t);
    /**
    * \brief You're never going to need to copy a Matrix.
    *
    * Let the compiler be your friend.
    */
    Matrix(const Matrix&) = delete;
    Matrix(const Matrix&&) = delete;
    Matrix& operator=(const Matrix&) = delete;
    Matrix& operator=(const Matrix&&) = delete;
    /**
    * \brief Straightforward get method.
    */
    ClauseNum get_num_clauses() const { return clauses.size(); }
    /**
    * \brief Straightforward get method.
    *
    * Beware - the parameter is not checked, so behave!
    *
    * @param i Index of item to get.
    */
    const Clause& operator[](size_t i) const { return clauses[i]; }
    /**
    * \brief Is a particular Clause positive?.
    *
    * @param i Index of Clause to check.
    */
    bool is_positive(size_t i) const { return positive_clauses[i]; }
    /**
    * \brief Is a particular Clause negative?.
    *
    * @param i Index of Clause to check.
    */
    bool is_negative(size_t i) const { return negative_clauses[i]; }
    /**
    * \brief Is a particular Clause a conjecture?
    *
    * @param i Index of Clause to check.
    */
    bool is_conjecture(size_t i) const;
    /**
    * \brief Straightforward set method.
    *
    * @param n Number of equality axioms.
    */
    inline void set_num_equals(uint32_t n) { num_equals = n; } 
    /**
    * \brief Use a simple heuristic to find a good start clause.
    *
    * Find a start clause that is positive/negative according to
    * the --negative flag, and if possible also a conjecture clause.
    * Also, indicate if there is no positive/negative clause, which 
    * means the problem is trivial.
    */
    pair<bool,size_t> find_start() const;
    /**
    * \brief Make an empty index.
    */
    void set_num_preds(size_t);
    /**
    * \brief Add a Clause to the Matrix and update the index accordingly.
    * 
    * Optionally add a clause role.
    *
    * @param clause Reference to the Clause.
    * @param role A string denoting the role of the clause. 
    */
    void add_clause(Clause&, string = "");
    /**
    * \brief Find all possible extensions given a Clause, but only 
    *        consider the first Literal in the Clause.
    *
    * See the documentation for find_extensions, which does all the
    * heavy lifting.
    *
    * @param u A reference to a Unifier function object.
    * @param result A reference to a vector of InferenceItems. 
    *               Start with this empty.
    * @param c The Clause of interest.
    * @param var_index A reference to the VariableIndex.
    * @param term_index A reference to the TermIndex.
    */
    void find_limited_extensions(Unifier&, vector<InferenceItem>&, Clause&,
                             VariableIndex&, TermIndex&);
    /**
    * \brief Find all possible extensions given a Clause, considering 
    *        all Literals in the Clause.
    *
    * See the documentation for find_extensions, which does all the
    * heavy lifting.
    *
    * @param u A reference to a Unifier function object.
    * @param result A reference to a vector of InferenceItems. 
    *               Start with this empty.
    * @param c The Clause of interest.
    * @param var_index A reference to the VariableIndex.
    * @param term_index A reference to the TermIndex.
    */
    void find_all_extensions(Unifier&, vector<InferenceItem>&, Clause&,
                             VariableIndex&, TermIndex&);
    /**
    * \brief Deterministic reorder of the clauses. 
    *
    * Call the reorder algorithm the specified number of times. This 
    * assumes you have stored a copy of the original clauses.
    *
    * @param n Number of times to call the reorder algorithm
    */
    void deterministic_reorder(size_t);
    /**
    * \brief Randomly reorder the matrix.
    */
    void random_reorder();
    /**
    * \brief Randomly reorder the literals in each clause 
    *        in the matrix.
    */
    void random_reorder_literals();
    /**
    * \brief Self-explanatory.
    *
    * BUT only do this to the matrix built at the start of the 
    * process, as it *assumes* the equality axioms are at the end of 
    * the matrix.
    */
    void move_equals_to_start();
    /*
    * Iteration on a Matrix is just iteration over the Clauses.
    */
    vector<Clause>::const_iterator cbegin() const { return clauses.cbegin(); }
    vector<Clause>::const_iterator cend() const { return clauses.cend(); }
    vector<Clause>::iterator begin() { return clauses.begin(); }
    vector<Clause>::iterator end() { return clauses.end(); }
    /**
    * \brief Make a string representation.
    */
    string to_string() const;
    /**
    * \brief Make a usable LaTeX representation.
    *
    * @param subbed Implement substitutions if true.
    */
    string make_LaTeX(bool = false) const;
    /**
    * \brief Write to a file that can be read by Prolog. 
    * 
    * This is for proof checking.
    *
    * @param path_to_file Reference to path object.
    */
    void write_to_prolog_file(const path&) const;
    /**
    * \brief Output in TPTP compatible format.
    */
    void show_tptp() const;
    /** 
    * \brief Self-explanatory. 
    *
    * Inspired by "Machine Learning 
    * Guidance for Connection Tableaux," Farber et al. 
    * 2020 although with a different measure of size and 
    * happening at a different place. 
    *
    * Makes use of the sort_clauses template.
    */
    void sort_clauses_by_increasing_size() {
      ClauseLengthCompare comparison;
      sort_clauses<ClauseLengthCompare>(comparison);
    }

    friend ostream& operator<<(ostream&, const Matrix&);
};


#endif
