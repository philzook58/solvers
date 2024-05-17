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

#ifndef TERMHASH_HPP
#define TERMHASH_HPP

#include <boost/container_hash/hash.hpp>

#include "Term.hpp"

/**
* \brief Hashing for terms using the Boost library.
*
* You need to be able to hash Terms, as the term index stores them
* in an unordered_map. (Well, it will eventually. This is currently 
* unused.)
*/
struct term_hash {
    size_t operator()(const Term& t) const {
        size_t hash = 0;
        for (size_t i = 0; i < t.arity(); i++)
            boost::hash_combine(hash, t[i]);
        boost::hash_combine(hash, t.get_v());
        boost::hash_combine(hash, t.get_f());
        return hash;
    }
};

#endif
