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

#ifndef PREDICATEINDEX_HPP
#define PREDICATEINDEX_HPP

#include<iostream>
#include<iomanip>
#include<string>
#include<vector>
#include<unordered_map>

#include "Predicate.hpp"
#include "FunctionHash.hpp"

using std::pair;
using std::vector;
using std::unordered_map;
using std::string;
using std::ostream;
using std::endl;
using std::cerr;

using PredIndexType = pair<string, Arity>;
using PredMapType = pair<PredIndexType, Predicate*>;

/**
 * \brief Management of Predicate objects.
 *
 * Note that the unordered_map can use the hash function from
 * FunctionHash.hpp.
 *
 * As usual *only* use this to make Predicates. As long as 
 * you do so then it takes care of memory allocation and 
 * deallocation.
 */
class PredicateIndex {
private:
    /** 
    * \brief Pointers to all predicates.
    */
    vector<Predicate*> preds;
    /** 
    * \brief Fast lookup using name and arity.
    */
    unordered_map<PredIndexType, Predicate*, fun_hash> name_index;
    /** 
    * \brief Automatically generate IDs.
    */
    ID next_index;
    /**
    * \brief Automatically generate IDs for definitional
    *        predicates.
    */
    ID next_definitional_id;
public:
    PredicateIndex();
    ~PredicateIndex();
    /**
    * \brief Copying these is a terrible idea.
    * 
    * As usual, let the compiler help you out.
    */
    PredicateIndex(const PredicateIndex&) = delete;
    PredicateIndex(const PredicateIndex&&) = delete;
    PredicateIndex& operator=(const PredicateIndex&) = delete;
    PredicateIndex& operator=(const PredicateIndex&&) = delete;
    /**
    * \brief Basic get method.
    */
    inline size_t get_num_preds() const { return preds.size(); }
    /**
    * \brief Self-explanatory.
    *
    * @param name Name of new Predicate.
    * @param arity Arity of new Predicate.
    */
    Predicate* add_predicate(const string&, Arity);
    /**
    * \brief Self-explanatory.
    *
    * @param fun_name Name of Predicate.
    * @param arity Arity of Predicate.
    */
    Predicate* find_predicate(const string&, Arity);
    /**
    * \brief Find the largest arity appearing in the index.
    */
    Arity find_maximum_arity() const;
    /**
    * \brief Sometimes $true and $false appear in the TPTP 
    *        collection. See if you included them during the 
    *        parsing.
    */
    bool true_false_added() const;
    /**
    * \brief Access to Predicate pointers, but  
    *        don't mess with them!
    */
    Predicate* operator[](size_t i) { return preds[i]; }
    /**
    * \brief Make a new, unique definitional predicate.
    *
    * @param arity Arity of predicate.
    */
    Predicate* make_definitional_predicate(Arity arity) {
        return add_predicate(
            params::definitional_predicate_prefix + std::to_string(next_definitional_id++), 
            arity);
    }

    friend ostream& operator<<(ostream&, const PredicateIndex&);
};

#endif
