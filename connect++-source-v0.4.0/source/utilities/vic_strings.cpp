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

#include "vic_strings.hpp"

namespace unicode_symbols {
  std::string LogSym::neg           = std::string("\u00ac");
  std::string LogSym::unicode_space = std::string("\u00a0");
  std::string LogSym::or_sym        = std::string("\u22c1");
  std::string LogSym::and_sym       = std::string("\u22c0");
  std::string LogSym::true_sym      = std::string("\u22a4");
  std::string LogSym::false_sym     = std::string("\u22a5");
  std::string LogSym::forall        = std::string("\u2200");
  std::string LogSym::exists        = std::string("\u2203");
  std::string LogSym::ifthen        = std::string("\u2192");
  std::string LogSym::iff           = std::string("\u2194");
}
//--------------------------------------------------------------
namespace ansi_escape_colours {
  uint8_t Colour::num_colours = 10;
  std::string Colour::nocol   = std::string("\033[0m");
  std::string Colour::red     = std::string("\033[38;5;9m");
  std::string Colour::green   = std::string("\033[38;5;10m");
  std::string Colour::blue    = std::string("\033[38;5;12m");
  std::string Colour::lblue   = std::string("\033[38;5;14m");
  std::string Colour::orange  = std::string("\033[38;5;208m");
  std::string Colour::yellow  = std::string("\033[38;5;11m");
  std::string Colour::purple  = std::string("\033[38;5;13m");
  std::string Colour::grey    = std::string("\033[38;5;242m");
  std::string Colour::lgrey   = std::string("\033[38;5;248m");

  std::string Colour::name_to_string(const ColourName& name) {
    switch(name) {
    case ColourName::NOCOL:
      return Colour::nocol;
      break;
    case ColourName::RED:
      return Colour::red;
      break;
    case ColourName::GREEN:
      return Colour::green;
      break;
    case ColourName::BLUE:
      return Colour::blue;
      break;
    case ColourName::LBLUE:
      return Colour::lblue;
      break;
    case ColourName::ORANGE:
      return Colour::orange;
      break;
    case ColourName::YELLOW:
      return Colour::yellow;
      break;
    case ColourName::PURPLE:
      return Colour::purple;
      break;
    case ColourName::GREY:
      return Colour::grey;
      break;
    case ColourName::LGREY:
      return Colour::lgrey;
      break;
    default:
      return Colour::nocol;
      break;
    }
  }
}
//--------------------------------------------------------------
namespace verbose_print {

uint8_t VPrint::verbosity = 0;

//--------------------------------------------------------------
/**
* Print something, plus optionally newlines, if verbosity 
* warrants it. 
*
* @param v verbosity level
* @param s string
* @param n print newlines?
* @param nl number of newlines
*/
void VPrint::operator()(uint8_t v, const string& s, bool n, uint8_t nl) {
  if (v <= verbosity) {
    std::cout << s;
    if (n) {
      for (uint8_t i = 0; i < nl; i++) {
        std::cout << std::endl;
      }
    }
  }
}
//--------------------------------------------------------------
/**
* Print something, plus optionally newlines, if verbosity 
* warrants it. 
*
* @param v verbosity level
* @param s string
* @param n print newlines?
* @param nl number of newlines
*/
void VPrint::operator()(uint8_t v, char* s, bool n, uint8_t nl) {
  if (v <= verbosity) {
    std::cout << s;
    if (n) {
      for (uint8_t i = 0; i < nl; i++) {
        std::cout << std::endl;
      }
    }
  }
}
//--------------------------------------------------------------
/**
* Print a number of newlines if verbosity warrants it.
*/
void VPrint::nl(uint8_t v, uint8_t nl) {
  if (v <= verbosity) {
    for (uint8_t i = 0; i < nl; i++) {
      std::cout << std::endl;
    }
  }
}
}