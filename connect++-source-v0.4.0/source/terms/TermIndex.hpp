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

#ifndef TERMINDEX_HPP
#define TERMINDEX_HPP

#include <iostream>
#include <vector>
#include <unordered_map>

/*
* Not necessarily needed -- only if HASHCONSTERMS is defined. 
* But no harm in including it.
*/
#include "TermHash.hpp"

using std::unordered_map;
using std::vector;
using std::ostream;
using std::endl;

/**
* \brief Look after terms, (ideally) using hash consing to avoid 
*        storing copies of terms.
*
* Everything is implemented such that this ignores whether or not 
* Variables are substituted. (Because to do otherwise isn't 
* necessary.)
*
* At present this is the best of two worlds. Unfortunately, use of 
* unordered_map with Term and proper hash consing can result in 
* strange errors, on *some* compilers but not others, and 
* I'm not too sure where they come from, although there seems 
* to be a problem with memory allocation/deallocation. Using 
* the unordered_map means allowing various kinds of copying 
* of Terms, which I'd rather not do, and that may be the place 
* to look.s
* 
* Despite this, early indications are that it's definitely
* worth using the full-blown hash table. If you allow HASHCONSTERMS 
* to be defined in BasicTypes.hpp you will compile with full 
* hash consing. Otherwise you'll get the alternative.
*
* The alternative version has the same behaviour but is likely to be 
* a little less efficient. The fact that it works just fine
* on every compiler I've tried suggests that something very 
* obscure might be happening in the bowels of the hashed 
* version to make memory errors show up. TODO...
*
* You should *only* use this to make Terms. As long as you 
* do that then this class takes all the responsibility for 
* memory allocation and deallocation for Terms.
*/
class TermIndex {
private:

    /**
    * \brief Hash table for storing pointers to 
    *        where Terms are actually stored. 
    * 
    * The key is the Term itself. term_hash is defined 
    * in TermHash.hpp.
    */
#ifdef HASHCONSTERMS
    unordered_map<Term, Term*, term_hash> index;
#endif
    /**
    * \brief Used (1) by the alternative storage method, not 
    *        doing full hash consing; and (2) to make 
    *        destruction easy.
    */
    vector<Term*> term_pointers;
    /**
    * \brief Find a term in the index.
    *
    * @param t The term you want to look up.
    */ 
    Term* find(const Term&);
public:
    
#ifdef HASHCONSTERMS
    TermIndex() : index(), term_pointers() {}
#else
    TermIndex() : term_pointers() {}
#endif

    ~TermIndex();
    /**
    * \brief Don't allow copying as this is a terrible idea.
    *
    * As usual, let the compiler be your friend.
    */
    TermIndex(const TermIndex&) = delete;
    TermIndex(const TermIndex&&) = delete;
    TermIndex& operator=(const TermIndex&) = delete;
    TermIndex& operator=(const TermIndex&&) = delete;
    /**
    * \brief Basic get method.
    */
    size_t get_size() const { return term_pointers.size(); }
    /**
    * \brief Self-explanatory: add a Term containing a variable to 
    *        the index.
    *
    * It's only actually added if it's not already present. If 
    * present, a pointer to the existing copy is returned.
    *
    * @param vp Pointer to Variable for which an equivalent Term 
    * is to be added
    */
    Term* add_variable_term(Variable*);
    /**
    * \brief Self-explanatory: add a Term containing a function to 
    *        the index.
    *
    * It's only actually added if it's not already present. If 
    * present, a pointer to the existing copy is returned.
    *
    * @param fp Pointer to a Function for which an appropriate Term 
    * is to be added
    * @param args Vector of pointers to Terms constituting the 
    * arguments for the new function Term to be added.
    */
    Term* add_function_term(Function*, const vector<Term*>&);
    /**
    * \brief Replace a variable in a term with an alternative, 
    * maintaining the structure of the TermIndex.
    *
    * The first two arguments are variables and the third a
    * general term. Replace one variable with another while keeping the
    * structure of the index correct. Replacement replaces any
    * substitutions for the variable being replaced with those applied
    * to the new one. You should probably not do that as ideally the
    * index should only contain unsubstituted variables.
    *
    * @param new_v Pointer to a Variable to use as replacement. 
    * @param old_v Pointer to a Variable to be replaced.
    * @param t Pointer to Term to make the replacement for. This 
    *          should already be in the index. 
    */
    Term* replace_variable_in_term(Variable*, Variable*, Term*);
    /**
    * \brief Minor variation on replace_variable_in_term. 
    *
    * ONLY use this if the new Term is in the index!
    *
    * @param new_t Pointer to a Term to use as replacement. 
    * @param old_v Pointer to a Variable to be replaced.
    * @param t Pointer to Term to make the replacement for. This 
    *          should already be in the index. 
    */
    Term* replace_variable_in_term_with_term(Term*, Variable*, Term*);

    friend ostream& operator<<(ostream&, const TermIndex&);
};

#endif
