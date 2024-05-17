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

#ifndef EXCEPTIONS_HPP
#define EXCEPTIONS_HPP

#include <iostream>
#include <exception>
#include <string>

/**
* \brief Exception used by the 
*        application in main(...).
*/
class file_open_exception : public std::exception {
private:
  std::string message;
public:
  file_open_exception(const std::string&);
  virtual const char* what() const noexcept;
};
/**
* \brief Exception used by the 
*        application in main(...).
*/
class file_read_exception : public std::exception {
private:
  std::string message;
public:
  file_read_exception(const std::string&);
  virtual const char* what() const noexcept;
};
/**
* \brief Exception used by the 
*        application in main(...).
*/
class file_parse_exception : public std::exception {
private:
  std::string message;
public:
  file_parse_exception(const std::string&);
  virtual const char* what() const noexcept;
};

#endif
