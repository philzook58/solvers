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

#ifndef CLAUSE_HPP
#define CLAUSE_HPP

#include<iostream>
#include<string>
#include<vector>
#include<random>
#include<algorithm>

#include "Literal.hpp"

using std::vector;
using std::string;
using std::ostream;
using std::endl;

/**
* \brief Possible results when simplifying a clause.
*/
enum class SimplificationResult {OK, Tautology, Contradiction};

/**
* \brief Representation of clauses.
*
* Essentially straightforward as they are just vectors of 
* Literals. Other classes do all the heavy lifting.
*/
class Clause {
private:
    /**
    * \brief A Clause is just a vector of Literals.
    */
    vector<Literal> c;
    /**
    * \brief Randomness for random reordering.
    */
    static std::mt19937 d;
public:
    Clause() : c() {}
    /**
    * \brief Construction is just taking a new vector of Literals.
    *
    * @param new_lits Reference to new vector of Literals.
    */
    Clause(const vector<Literal>& new_lits) : c(new_lits) {
    #ifdef DEBUGMESSAGES
        if (new_lits.size() == 0)
            cerr << "Why are you constructing an empty clause?" << endl;
    #endif
    }
    /**
    * \brief Straightforward get method.
    */
    inline size_t size() const { return c.size(); }
     /**
    * \brief Straightforward get method.
    */
    inline bool empty() const { return c.empty(); }
     /**
    * \brief Straightforward reset method.
    */
    inline void clear() { c.clear(); }
    /**
    * \brief A clause is positive if it has no negated literals.
    */
    bool is_positive() const;
    /**
    * \brief A clause is negative if it has only negated literals.
    */
    bool is_negative() const;
    /**
    * \brief Get rid of identical literals. 
    *
    * This does *not* take account of substitutions as 
    * it is mainly used for simplification before any 
    * substitutions happen.
    */
    void remove_duplicates();
    /**
    * \brief Check whether the clause contains complementary 
    * literals.
    *
    * This does *not* take account of substitutions as 
    * it is mainly used for simplification before any 
    * substitutions happen.
    */
    bool has_complementary_literals() const;
    /**
    * \brief Add a literal, making sure you don't duplicate.
    *
    * Yes, yes a set<> would be a good idea, but vectors are 
    * easy, nicer if you want indexes amd nicer for the cache.
    *
    * @param l Reference to Literal to add
    */
    void add_lit(const Literal&);
    /**
    * \brief Get rid of the specified Literal.
    *
    * @param l Index of literal to remove.
    */
    void drop_literal(LitNum);
    /**
    * \brief Get rid of and return the specified Literal.
    *
    * @param l Index of literal to remove.
    */
    Literal extract_literal(LitNum);
    /**
    * \brief Direct read of the specified Literal.
    *
    * There is no check on whether you've given a sensible index, 
    * so behave yourself!
    *
    * @param  i Index of required Literal
    */
    Literal& operator[](size_t);
    /**
    * \brief Make a copy of an entire clause, introducing new 
    *        variables.
    *
    * Straightforward because the heavy lifting is done 
    * elsewhere.
    *
    * @param vi Reference to the VariableIndex
    * @param ti Reference to the TermIndex
    */
    Clause make_copy_with_new_vars(VariableIndex&, TermIndex&) const;
     /**
    * \brief Simplify a clause by dealing with $true, $false, 
    *        complementary literals, and duplicates.
    */
    SimplificationResult simplify(); 
    /**
    * \brief Randomly re-order the literals.
    */
    void random_reorder();
    /**
    * \brief Convert to a string.
    *
    * @param subbed Implement substitutions if true.
    */
    string to_string(bool = false) const;
    /**
    * \brief Convert to a string that can be read by Prolog. 
    *
    * Does not apply substitutions.
    */
    string to_prolog_string() const;
    /**
    * \brief Convert to a string that is compatible with the 
    * TPTP. 
    *
    * Does not apply substitutions.
    */
    string to_tptp_string() const;
    /**
    * \brief Convert the clause to a LaTeX representation. 
    *
    * Assumes you are in Math Mode.
    *
    * @param subbed implement substitution if true.
    */
    string make_LaTeX(bool = false) const;

    vector<Literal>::const_iterator cbegin() const { return c.cbegin(); }
    vector<Literal>::const_iterator cend() const { return c.cend(); }
    vector<Literal>::iterator begin() { return c.begin(); }
    vector<Literal>::iterator end() { return c.end(); }

    friend ostream& operator<<(ostream&, const Clause&);
};

#endif
