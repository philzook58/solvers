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

#include "LaTeXUtilities.hpp"

//-----------------------------------------------------------------
string latex_escape_characters(const string& s) {
  string result;
  for (char c : s) {
    switch (c) {
      case '_':
        result += "\\_";
        break;
      case '%':
        result += "\\%";
        break;
      case '$':
        result += "\\$";
        break;
      case '#':
        result += "\\#";
        break;
      case '&':
        result += "\\&";
        break;
      default:
        result += c;
    }
  }
  return result;
}
//-----------------------------------------------------------------
string latex_truncate_to_length(const string& s) {
  string s2 = s.substr(0, params::latex_truncation_length);
  if (s2.size() < s.size())
    s2 += "\\ldots";
  return s2;
}