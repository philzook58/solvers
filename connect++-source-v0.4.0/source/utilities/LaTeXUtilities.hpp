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

#ifndef LATEXUTILITIES_HPP
#define LATEXUTILITIES_HPP

#include <iostream>

#include "Parameters.hpp"

using std::string;

/**
* \brief Take a string and apply some LaTeX escapes where necessary.
*
* In some cases, when taking the name of a Variable or similar and 
* translating to LaTeX, the name will contain characters that needs to 
* be escaped. This does it.
*/
string latex_escape_characters(const string&);
/**
* \brief Take a LaTeX string and make a very basic attempt to 
*        limit its length.
*
* You're going to have to be very careful if you use this because it 
* makes absolutely no attempt (yet) to avoid breaking any 
* LaTeX in the input string.
*/
string latex_truncate_to_length(const string&);

#endif