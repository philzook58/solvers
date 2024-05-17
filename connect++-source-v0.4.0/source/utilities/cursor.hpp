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

#ifndef CURSER_HPP
#define CURSER_HPP

#include<iostream>
#include<string>

using std::string;
using std::to_string;

namespace cursor_symbols {

/**
* \brief Simple library for doing things involving moving the curser when 
* producing terminal output. 
*
* This is achieved using ANSI escape 
* codes, see:
*
* https://en.wikipedia.org/wiki/ANSI_escape_code#CSIsection
*
* That page is hard to decipher. Suffice to say that the left-hand-side
* of the table for "CSI introducers" is interpreted as follows:
*
* \033[ n A - move curser n places up.
* \033[ n B - move curser n places down.
*
* ... and so on. Colours are then the "Set Graphic Rendition" part that
* appears as "CSI n m" and translates to ""\033[ n m".
*/
  class Cursor {
  private:
    static string ESC;
  public:
    Cursor() {};

    static string up(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "A";
      }
      return s;
    }
    static string down(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "B";
      }
      return s;
    }
    static string right(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "C";
      }
      return s;
    }
    static string left(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "D";
      }
      return s;
    }
    static string down_n_lines(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "E";
      }
      return s;
    }
    static string up_n_lines(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "F";
      }
      return s;
    }
    static string to_column(uint8_t n) {
      string s;
      if (n >= 1) {
        s += ESC;
        s += to_string(n);
        s += "G";
      }
      return s;
    }
    /**
    * Origin is top left corner. n is row and m is column.
    */
    static string to(uint8_t n, uint8_t m) {
      string s;
      if (n >= 1 && m >= 1) {
        s += ESC;
        s += to_string(n);
        s += ";";
        s += to_string(m);
        s += "H";
      }
      return s;
    }
    /**
    * 0 - to screen end.
    * 1 - to screen beginning.
    * 2 - whole screen.
    * 3 - 2 + erase scrolling back buffer.
    */
    static string erase_display(uint8_t n) {
      string s;
      if (n >= 0) {
        s += ESC;
        s += to_string(n);
        s += "J";
      }
      return s;
    }
    /**
    * 0 - to end.
    * 1 - to beginning.
    * 2 - whole line.
    */
    static string erase_line(uint8_t n) {
      string s;
      if (n >= 0) {
        s += ESC;
        s += to_string(n);
        s += "K";
      }
      return s;
    }
  };
}

#endif
