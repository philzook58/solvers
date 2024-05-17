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

#ifndef SCHEDULE_HPP
#define SCHEDULE_HPP

#include<iostream>
#include<string>
#include<filesystem>
#include <fstream>

#include <boost/spirit/include/qi.hpp>

#include "Parameters.hpp"
#include "Exceptions.hpp"

using std::string;
using std::vector;
using std::ifstream;
using std::ostream;
using std::cout;
using std::cerr;
using std::endl;
using std::pair;
using namespace boost::spirit;
using Iter = string::const_iterator;

namespace fs = std::filesystem;

/**
* \brief Hide all the global stuff in this namespace.
*
* It's easiest to implement a parser using the relevant boost 
* libraries if you use globals to store things as you parse.
* Hiding them in a namespace makes the use of globals a bit 
* less reprehensible.
*/
namespace schedule {
/**
* \brief Possible kinds of schedule step.
*/
enum class schedule_step {
  all_definitional,
  no_definitional,
  reorder,
  rand_reorder,
  rand_lits,
  all_start,
  pos_neg_start,
  conjecture_start,
  restrict_start,
  no_regularity,
  all_lemmata,
  all_reductions,
  all_extensions,
  no_lemmata,
  all_backtrack,
  lemmata_backtrack,
  reduction_backtrack,
  extension_backtrack,
  explore_left_trees,
  complete,
  start_depth,
  depth_inc,
  limit_by_tree_depth
};
string to_string(const schedule_step&);
/**
* \brief Wrap up the parsing process and the operation of 
*        a schedule in a single class.
*
* This covers parsing, and also the sequencing, including 
* manipulation of parameters for each step, of a schedule 
* stored in a file.
*
* The main elements of a file exactly mimic the command line 
* options, so a single step in a schedule acts exactly as 
* though the relevant options had been supplied to a single 
* call from the command line.
*
* Aside from that, a line ends with a semicolon, and there is 
* a number at the start of the line specifying a percentage of 
* the timeout. The last line should start with 0, specifying 
* "all remaining".
*/
class Schedule {
private:
    /** 
    * \brief Representation of a schedule.
    *
    * Each element is a vector of pairs. Each pair is an identifier for 
    * a step, and an integer. Times are dealt with elsewhere.
    */
    vector<vector<pair<schedule_step,unsigned int>>> schedule;
    /**
    * \brief Times for each member of a schedule.
    */
    vector<unsigned int> times;
    /**
    * \brief Keep track of which step in the schedule we're on. 
    */
    size_t schedule_step_number;
    /**
    * \brief Apply the settings for a single step in a schedule.
    */
    void apply_item(const pair<schedule_step,unsigned int>&);
public:
    /**
    * \brief You only need this constructor because everything will 
    * be filled in by the parser.
    */
    Schedule() : schedule(), times(), schedule_step_number(0) {};
    /**
    * \brief Go back to the beginning of the schedule but leave 
    * everything else intact.
    */
    void reset_schedule() { schedule_step_number = 0; }
    /**
    * \brief Make a string representation of a line in the schedule.
    *
    * @param n Line to convert.
    * @return String representation.
    */
    string step_to_string(size_t) const;
    /**
    * \brief Self-explanatory.
    *
    * Produces an empty schedule if parsing fails.
    *
    * @param path Path of file to read from.
    */
    void read_schedule_from_file(fs::path);
    /**
    * \brief Apply the settings for the next step in the schedule.
    *
    * @return True and the percentage of time to run for if 
    *         successful, false and 0 otherwise.
    */
    pair<bool,unsigned int> set_next_schedule();

    friend ostream& operator<<(ostream&, const Schedule&);
};
/**
* \brief Semantic action for parser.
*/
struct add_time {
    void operator()(unsigned int, qi::unused_type, qi::unused_type) const;
};
/**
* \brief Semantic action for parser.
*/
struct set_value {
    void operator()(unsigned int, qi::unused_type, qi::unused_type) const;
};
/**
* \brief Semantic action for parser.
*/
struct set_step {
    void operator()(string, qi::unused_type, qi::unused_type) const;
};
/**
* \brief Semantic action for parser.
*/
struct add_step {
    void operator()(qi::unused_type, qi::unused_type) const;
};
/**
* \brief Semantic action for parser.
*/
struct next_settings {
    void operator()(qi::unused_type, qi::unused_type) const;
};

}

#endif