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

#include "Exceptions.hpp"

//--------------------------------------------------------------
file_open_exception::file_open_exception(const std::string& s)
: message() {
  message += "Failed to open file: ";
  message += s;
}
//--------------------------------------------------------------
const char* file_open_exception::what() const noexcept {
  return message.c_str();
}
//--------------------------------------------------------------
file_read_exception::file_read_exception(const std::string& s)
: message() {
  message += "Failed to read file: ";
  message += s;
}
//--------------------------------------------------------------
const char* file_read_exception::what() const noexcept {
  return message.c_str();
}
//--------------------------------------------------------------
file_parse_exception::file_parse_exception(const std::string& s)
: message() {
  message += "Failed to parse file: ";
  message += s;
}
//--------------------------------------------------------------
const char* file_parse_exception::what() const noexcept {
  return message.c_str();
}
