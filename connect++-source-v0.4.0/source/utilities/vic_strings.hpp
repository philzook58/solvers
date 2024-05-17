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

#ifndef VICSTRING_HPP
#define VICSTRING_HPP

#include<iostream>
#include<vector>
#include<string>

/**
* \brief vic_string - "verbose/indented/coloured"
*
* A simple library for doing fancy string output to
* a terminal. Also includes some logic symbols.
*/

//--------------------------------------------------------------
namespace unicode_symbols {
  /**
  * Codes needed to display logical symbols in terminal output.
  */
  struct LogSym {
    static std::string neg;
    static std::string unicode_space;
    static std::string or_sym;
    static std::string and_sym;
    static std::string true_sym;
    static std::string false_sym;
    static std::string forall;
    static std::string exists;
    static std::string ifthen;
    static std::string iff;
  };
}
//--------------------------------------------------------------
namespace ansi_escape_colours {
  /**
  * Names for colours applied to terminal output.
  */
  enum class ColourName {NOCOL,
			 RED,
			 GREEN,
			 BLUE,
			 LBLUE,
			 ORANGE,
			 YELLOW,
			 PURPLE,
			 GREY,
			 LGREY
  };
  /**
   * Codes for colours. These are standard, see:
   *
   * https://en.wikipedia.org/wiki/ANSI_escape_code
   *
   * The third digit is 6-bit RGB, 16 + 36R + 6G + B. 0 to 15
   * are standard colours and the rest (232 to 255) are
   * greyscale.
   */
  struct Colour {
    static uint8_t num_colours;
    static std::string nocol;
    static std::string red;
    static std::string green;
    static std::string blue;
    static std::string lblue;
    static std::string orange;
    static std::string yellow;
    static std::string purple;
    static std::string grey;
    static std::string lgrey;

    static std::string name_to_string(const ColourName&);
  };
}
//--------------------------------------------------------------
using std::ostream;
using std::string;

namespace colour_string {
  using namespace ansi_escape_colours;
  /**
   * \brief Simple addition of colour to strings and ostreams.
   *
   * The format is:
   *
   * cout << col("Hello").red() ...;
   *
   * Also incorporates a map allowing the format:
   *
   * col.set_map(2, ColourName::PURPLE);
   * cout << col("Hello", 2) << ...
   *
   * so that assignment of colours can easily be changed
   */
  class ColourString {
  private:
    uint8_t num_colours;
    bool use_colours;
    std::vector<ColourName> map;
    string s;
  public:
    ColourString(bool uc)
      : num_colours(Colour::num_colours)
      , use_colours(uc)
      , map()
      , s()
    {
      map = { ColourName::NOCOL,
	      ColourName::RED,
	      ColourName::GREEN,
	      ColourName::BLUE,
	      ColourName::LBLUE,
	      ColourName::ORANGE,
	      ColourName::YELLOW,
	      ColourName::PURPLE,
	      ColourName::GREY,
	      ColourName::LGREY };
    }

    /*
     * Straighforward gets and sets.
     */
    bool get_use_colours() const { return use_colours; }
    void set_use_colours(bool b) { use_colours = b; }
    void set_map(uint8_t i, ColourName colour) {
      if (i >= 0 && i < Colour::num_colours)
        map[i] = colour;
    }
    /**
     * This sets the member string. The idea is to allow other
     * methods to add the colour to it.
     */
    ColourString operator()(const string& _s) {
      s = _s;
      return *this;
    }
    /**
     * Make a coloured string using the map.
     *
     * Does not affect the stored string.
     */
    string operator()(const string& _s, size_t num) {
      if (use_colours && num >=0 && num < map.size())
	     return Colour::name_to_string(map[num]) + _s + Colour::nocol;
      else
	     return _s;
    }

    /*
     *Individual colour setters.
     */
    string red()    {
      if (use_colours)
	     return Colour::red + s + Colour::nocol;
      else
        return s;
    }
    string green()  {
      if (use_colours)
	     return Colour::green + s + Colour::nocol;
      else
	     return s;
    }
    string blue()   {
      if (use_colours)
        return Colour::blue + s + Colour::nocol;
       else
	      return s;
    }
    string lblue()  {
      if (use_colours)
	      return Colour::lblue + s + Colour::nocol;
      else
	    return s;
    }
    string orange() {
      if (use_colours)
	      return Colour::orange + s + Colour::nocol;
      else
	      return s;
    }
    string yellow() {
      if (use_colours)
	      return Colour::yellow + s + Colour::nocol;
      else
	      return s;
    }
    string purple() {
      if (use_colours)
	      return Colour::purple + s + Colour::nocol;
      else
	      return s;
    }
    string grey()   {
      if (use_colours)
	      return Colour::grey + s + Colour::nocol;
      else
	      return s;
    }
    string lgrey()  {
      if (use_colours)
	      return Colour::lgrey + s + Colour::nocol;
      else
	      return s;
    }
  };
}

//--------------------------------------------------------------
namespace verbose_print {
  /**
  * Print strings and optionally newlines on the terminal 
  * output, taking verbosity into account.
  */
  class VPrint {
  private:
    static uint8_t verbosity;
  public:
    VPrint() = delete;
    VPrint(uint8_t v) { verbosity = v; }
    void operator()(uint8_t, const string&, bool = false, uint8_t = 1);
    void operator()(uint8_t, char*, bool = false, uint8_t = 1);
    void nl(uint8_t, uint8_t = 1);
  };
}

//--------------------------------------------------------------
namespace commas {
  /**
  * \brief Simple function object for putting commas in lists.
  *
  * This avoids a *load* of repeated code when you have reason to 
  * output a lot of things with comma-separated lists.
  *
  * Initialize the object with the actual length of the list 
  * you want to print. 
  * 
  * Each time you call comma() you'll get a comma or an empty string 
  * with just enough commas to format the list correctly.
  */
  class comma {
    private:
      size_t target;
      size_t i;
    public:
      /**
      * \brief Wouldn't make any sense. 
      */
      comma() = delete;
      /**
      * \brief Initialise with the length of the list you're printing.
      */
      comma(size_t _target)
      : i(1), target(_target) {}
      /**
      * \brief The magic happens here! 
      */
      string operator()() {
        if (i < target) {
          i++;
          return string(", ");
        }
        return string("");
      }
  };
}

#endif