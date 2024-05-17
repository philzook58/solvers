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

#ifndef FUNCTIONHASH_HPP
#define FUNCTIONHASH_HPP

#include<string>

#include <boost/container_hash/hash.hpp>

#include "BasicTypes.hpp"

using std::string;
using std::pair;

/**
* \brief Hashing for functions using the Boost library for hashing.
*
* You need to be able to hash pairs of function name and arity, as
* the function index stores them in an unordered_map.
*/
struct fun_hash {
    size_t operator()(const pair<string, Arity>& f) const {
        size_t hash = 0;
        boost::hash_combine(hash, f.first);
        boost::hash_combine(hash, f.second);
        return hash;
    }
};

#endif
