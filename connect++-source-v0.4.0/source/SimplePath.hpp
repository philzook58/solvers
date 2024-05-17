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

#ifndef SIMPLEPATH_HPP
#define SIMPLEPATH_HPP

#include<iostream>
#include<vector>

#include "InferenceItem.hpp"
#include "Unifier.hpp"
#include "Clause.hpp"

using std::vector;
using std::ostream;
using std::endl;
using std::cout;

/**
* \brief Simple representation of the path within a proof tree.
*
* While the Path class (not part of the source distribution) keeps a 
* separate vector of literals for each possible predicate/negation c
* ombination so it's fast to get the potential literals for
* reductions, this does not. The reason is that this one needs 
* to be copied to support full backtracking, and I haven't yet looked 
* at optimising to see what the trade-off is between finding reductions 
* fast, and making copies of the path_index.
*
* This class is also a natural location for any methods used to 
* find reductions, and a natural location for the test_for_regularity
* method.
*/
class SimplePath {
private:
    /**
    * \brief Simple representation of a path as a vector of Literals. 
    */
    vector<Literal> path;
    uint32_t num_preds;
    uint32_t len;
    /**
    * \brief Find the reductions that you can perform for a specified 
    * Literal.
    *
    * This process simply requires you to find the complementary
    * Literals in the SimplePath that unify with the one specified.
    *
    * @param u A Unifier function object.
    * @param result A reference to a vector of InferenceItems.
    * @param lit A Literal that you want the reductions for.
    * @param index The index of lit. In this instance that means the
    *              index (position) in the Clause it comes from.
    */
    void find_reductions(Unifier&, vector<InferenceItem>&, const Literal&,
                         LitNum);
public:
    /**
    * \brief You should () usually never need a more compilcated 
    *        constructor. */
    SimplePath() : path(), num_preds(0), len(0) {}
    /**
    * \brief Use this constructor if you know how many predicates 
    *        there are.
    *
    * @param num_predicates Number of predicates. 
    */
    SimplePath(uint32_t);
    /**
    * \brief Straightforward get method.
    */
    inline uint32_t length() const { return len; }
    /**
    * \brief evert to the empty state without changing num_preds.
    */
    void clear();
    /**
    * \brief Set method for num_predicates.
    */
    inline void set_num_preds(size_t num_predicates) { num_preds = num_predicates; }
    /**
    * \brief Add a new Literal to the Path.
    *
    * @param lit Reference to Literal to add.
    */
    void push(const Literal&);
    /**
    * \brief Get the last Literal in the Path. Non-destructive.
    */
    Literal back() const;
    /**
    * \brief Remove the last item from the Path.
    */
    void pop();
    /**
    * \brief Regularity test.
    *
    * Taking substitutions into account, test whether any literal in the
    * clause appears in the path.
    *
    * @param c Reference to Clause to use.
    */
    bool test_for_regularity(Clause&) const;
    /**
    * \brief Given a Clause, find all possible reductions given 
    *        the current Path, but only for the first Literal in 
    *        the Clause.
    *
    * See also the documentation for find_reductions.
    *
    * @param u A reference to a Unifier function object.
    * @param result A reference to a vector of InferenceItems. Start with
    *               this empty.
    * @param c A Clause that you want the reductions for.
    */
    void find_limited_reductions(Unifier&, vector<InferenceItem>&,
                         Clause&);
    /**
    * \brief Given a Clause, find all possible reductions given 
    *        the current Path.
    *
    * See also the documentation for find_reductions.
    *
    * @param u A reference to a Unifier function object.
    * @param result A reference to a vector of InferenceItems. Start with
    *               this empty.
    * @param c A Clause that you want the reductions for.
    */
    void find_all_reductions(Unifier&, vector<InferenceItem>&,
                         Clause&);
    /**
    * \brief Show just the path.
    *
    * Use this if you don't need to see the index and other information.
    *
    * This method is slightly out of place here as it's mainly for 
    * compatability with the Path class, that is not currently part of the 
    * distribution, You can probably safely ignore it.
    *
    * @param out Reference to an ostream.
    */
    void show_path_only(ostream&);
    /**
    * \brief Convert the path to a string.
    *
    * @param subbed Implement substitution if true.
    */
    string to_string(bool = false) const;
    /**
    * \brief Convert the Path only to a LaTeX representation.
    *
    * @param subbed Implement substitutions if true.
    */
    string make_LaTeX(bool = false) const;
    /**
    * \brief Iterators just traverse the path vector. 
    */
    vector<Literal>::const_iterator cbegin() const { return path.cbegin(); }
    vector<Literal>::const_iterator cend() const { return path.cend(); }
    vector<Literal>::iterator begin() { return path.begin(); }
    vector<Literal>::iterator end() { return path.end(); }

    friend ostream& operator<<(ostream&, const SimplePath&);
};

#endif
