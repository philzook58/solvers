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

#ifndef UNIFIER_HPP
#define UNIFIER_HPP

#include<iostream>
#include<string>
#include<deque>

#include "Substitution.hpp"
#include "Literal.hpp"

using std::deque;
using std::pair;
using std::ostream;
using std::endl;
using std::string;

/**
* \brief The unification algorithm used deals fundamentally 
*        with pairs of Terms.
*/
using UPair = pair<Term* ,Term*>;
/**
* \brief Enumeration of possible outcomes from attempting 
*        unification.
*/
enum class UnificationOutcome {Succeed, ConflictFail, OccursFail};
/**
* \brief Obviously, you want to be able to print out unification 
*        outcomes. This is mostly for debugging purposes.
*/
ostream& operator<<(ostream&, const UnificationOutcome&);
/**
* \brief Wrap up various applications of unificiation into a 
*        single class: all the unification you need to do happens
*        here.
*
* You may find yourself unifying Terms, Literals and so on. This 
* puts it all in one place. The class is a function class with 
* various overloaded operator() methods.
*
* All the real work happens in the "complete_unification" method.
*
* See the Wikipedia page. This is apparently due to Montelli and
* Montanari (1982). Looking at "An Efficient Unification Algorithm --
* yes, indeed it is. The algorithm as stated in the paper is
* nondeterministic, and apparently you get a bunch of different
* outcomes depending on the details of the implementation.
*
* So: this one uses a queue, taking something from the end and
* placing any results at the beginning. 
*
* Note that some modifications have to be made compared with the
* paper's presentation, because the method used to make 
* substitutions takes immediate effect. As a result, 
* substitutions get removed by the Delete rule, so you might 
* as well remove them immediately. Also, when substituting x=? 
* you don't need to check whether x appears in the other equations.
*/
class Unifier {
private:
    /**
    * \brief Build the resulting substitution here.
    */
    Substitution s;
    /**
    * \brief Queue used by complete_unification method.
    */
    deque<UPair> to_do;
    /**
    * \brief Implementation of unification: all the real work 
    *        happens here.
    */
    UnificationOutcome complete_unification();
public:
    /**
    * \brief There isn't really much to initialize.
    */
    Unifier() : s(), to_do() {}
    /**
    * \brief You really only need one Unifier!
    *
    * As always, copying is a bad idea so let the compiler help 
    * you out.
    */
    Unifier(const Unifier&) = delete;
    Unifier(const Unifier&&) = delete;
    Unifier& operator=(const Unifier&) = delete;
    Unifier& operator=(const Unifier&&) = delete;
    /**
    * \brief Trivial get methods for the result.
    */
    Substitution get_substitution() const { return s; }
    /**
    * \brief Implementation of unification for a pair of Terms.
    *
    * See the Wikipedia page. This is apparently due to 
    * Montelli and Montanari (1982). Looking at "An Efficient 
    * Unification Algorithm -- yes, indeed it is.
    *
    * See also the documentation for complete_unification.
    *
    * @param term1 Pointer to first term
    * @param term2 Pointer to second term
    */
    UnificationOutcome operator()(Term*, Term*);
    /**
    * \brief The same as the main operator(), but you've already 
    *        extracted the arguments for the things of 
    *        interest into lists.
    *
    * @param t1s Reference to vector of pointers to Terms
    * @param t2s Reference to vector of pointers to Terms
    */
    UnificationOutcome operator()(const vector<Term*>&,
                                  const vector<Term*>&);
    /**
    * \brief Unification of Literals.
    *
    * @param l1 Pointer to first Literal
    * @param l2 Pointer to second Literal
    */
    UnificationOutcome operator()(Literal*, Literal*);
    /**
    * Unification of Literals.
    *
    * @param l1 Reference to first Literal
    * @param l2 Reference to second Literal
    */
    UnificationOutcome operator()(const Literal&, const Literal&);
    /**
    * \brief Apply the backtracking process to the 
    *        substitution that has been constructed.
    */
    void backtrack();
    /**
    * \brief Make a nice string representation.
    *
    * @param subbed Use substitutions if true.
    */
    string to_string(bool subbed = false) const {
        return s.to_string(subbed);
    }

    friend ostream& operator<<(ostream&, const Unifier&);
};

#endif
