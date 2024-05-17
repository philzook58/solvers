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

#ifndef CLAUSE_COMPARISONS_HPP
#define CLAUSE_COMPARISONS_HPP

#include "Clause.hpp"

using ClauseAndRole = pair<Clause, string>;

/**
* \brief Provide a function object to compare clauses by size.
*
* As clause roles always get re-ordered with clauses this 
* actually acts on pairs. 
*/
struct ClauseLengthCompare {
    bool operator()(const ClauseAndRole& c1, 
                    const ClauseAndRole& c2) const {
        return (c1.first.size() < c2.first.size());
    }
};

#endif