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

#include "Function.hpp"

//----------------------------------------------------------------------
string Function::to_string() const {
  colour_string::ColourString cs(params::use_colours);
  return cs(name).green();
}
//----------------------------------------------------------------------
string Function::make_LaTeX() const {
  string s ("\\text{");
  s += latex_escape_characters(name);
  s += "}";
  return s;
}
//----------------------------------------------------------------------
/**
* \brief Really only for debugging.
*
* Use Function::to_string if you want something pretty.
*/
ostream& operator<<(ostream& out, const Function& f) {
    out << "Function: " << setw(params::output_width) << f.id
        << " Name: " << setw(params::output_width + 20) << f.name
        << " Arity: " << setw(params::output_width) << f.arity;
    return out;
}
