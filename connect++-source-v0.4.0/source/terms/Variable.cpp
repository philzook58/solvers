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

#include "Variable.hpp"
/**
 * \brief Some methods are in Term.cpp to make the dependencies work.
 *
 * What?!! Where is everything?!! The file you need is Term.cpp.
 */

 /**
 * This is mainly for debugging. If you want actual representations 
 * then use Variable::to_string or similar.
 */
ostream& operator<<(ostream& out, const Variable& v) {
    out << "Var: " << setw(params::output_width) << v.name
        <<" ID: " << setw(params::output_width) << v.id;
    if (v.substitution != nullptr)
        out << " Subbed";
    return out;
}
