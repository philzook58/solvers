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

#include "Schedule.hpp"

namespace schedule {

//--------------------------------------------------------------
string to_string(const schedule_step& s) {
    switch (s) {
        case schedule_step::all_definitional:
            return string("--all-definitional");
            break;
        case schedule_step::no_definitional:
            return string("--no-definitional");
            break;
        case schedule_step::reorder:
            return string("--reorder");
            break;
        case schedule_step::rand_reorder:
            return string("--random-reorder");
            break;
        case schedule_step::rand_lits:
            return string("--random-reorder-literals");
            break;
        case schedule_step::all_start:
            return string("--all-start");
            break;
        case schedule_step::pos_neg_start:
            return string("--pos-neg-start");
            break;
        case schedule_step::conjecture_start:
            return string("--conjecture-start");
            break;
        case schedule_step::restrict_start:
            return string("--restrict-start");
            break;
        case schedule_step::no_regularity:
            return string("--no-regularity");
            break;
        case schedule_step::all_lemmata:
            return string("--all-lemmata");
            break;
        case schedule_step::all_reductions:
            return string("--all-reductions");
            break;
        case schedule_step::all_extensions:
            return string("--all-extensions");
            break;
        case schedule_step::no_lemmata:
            return string("--no-lemmata");
            break;
        case schedule_step::all_backtrack:
            return string("--all-backtrack");
            break;
        case schedule_step::lemmata_backtrack:
            return string("--lemmata-backtrack");
            break;
        case schedule_step::reduction_backtrack:
            return string("--reduction-backtrack");
            break;
        case schedule_step::extension_backtrack:
            return string("--extension-backtrack");
            break;
        case schedule_step::explore_left_trees:
            return string("--explore-left-trees");
            break;
        case schedule_step::complete:
            return string("--complete");
            break;
        case schedule_step::start_depth:
            return string("--start-depth");
            break;
        case schedule_step::depth_inc:
            return string("--depth-increment");
            break;
        case schedule_step::limit_by_tree_depth:
            return string("--limit-by-tree-depth");
            break;
        default:
            break;
    }
    return string("");
}
//--------------------------------------------------------------
// Basic material for parser semantic actions.
//--------------------------------------------------------------
unsigned int value = 0;
unsigned int current_time = 0;
string step;
vector<pair<schedule_step, unsigned int>> current_settings;
vector<vector<pair<schedule_step, unsigned int>>> new_schedule;
vector<unsigned int> new_times;
//--------------------------------------------------------------
// Parser semantic actions.
//--------------------------------------------------------------
void add_time::operator()(unsigned int t, qi::unused_type,
                    qi::unused_type) const { 
    current_time = t; 
}
void set_value::operator()(unsigned int v, qi::unused_type,
                    qi::unused_type) const { 
    value = v; 
}
void set_step::operator()(string s, qi::unused_type,
                    qi::unused_type) const { 
    step = s; 
}
void add_step::operator()(qi::unused_type, qi::unused_type) const {
    schedule_step step2;
    if (step == "--all-definitional") step2 = schedule_step::all_definitional;
    if (step == "--no-definitional") step2 = schedule_step::no_definitional;
    if (step == "--reorder") step2 = schedule_step::reorder;
    // Remember: you *do* need the extra space!
    if (step == "--random-reorder ") step2 = schedule_step::rand_reorder;
    if (step == "--random-reorder-literals") step2 = schedule_step::rand_lits;
    if (step == "--all-start") step2 = schedule_step::all_start;
    if (step == "--pos-neg-start") step2 = schedule_step::pos_neg_start;
    if (step == "--conjecture-start") step2 = schedule_step::conjecture_start;
    if (step == "--restrict-start") step2 = schedule_step::restrict_start;
    if (step == "--no-regularity") step2 = schedule_step::no_regularity;
    if (step == "--all-lemmata") step2 = schedule_step::all_lemmata;
    if (step == "--all-reductions") step2 = schedule_step::all_reductions;
    if (step == "--all-extensions") step2 = schedule_step::all_extensions;
    if (step == "--no-lemmata") step2 = schedule_step::no_lemmata;
    if (step == "--all-backtrack") step2 = schedule_step::all_backtrack;
    if (step == "--lemmata-backtrack") step2 = schedule_step::lemmata_backtrack;
    if (step == "--reduction-backtrack") step2 = schedule_step::reduction_backtrack;
    if (step == "--extension-backtrack") step2 = schedule_step::extension_backtrack;
    if (step == "--explore-left-trees") step2 = schedule_step::explore_left_trees;
    if (step == "--complete") step2 = schedule_step::complete;
    if (step == "--start-depth") step2 = schedule_step::start_depth;
    if (step == "--depth-increment") step2 = schedule_step::depth_inc;
    if (step == "--limit-by-tree-depth") step2 = schedule_step::limit_by_tree_depth;
    current_settings.push_back(pair<schedule_step, unsigned int>(step2, value));
    step = "";
    value = 0;
}
void next_settings::operator()(qi::unused_type, qi::unused_type) const {
    new_schedule.push_back(current_settings);
    new_times.push_back(current_time);
    current_time = 0;
    current_settings.clear();
}
//--------------------------------------------------------------
// Basic material for parser.
//--------------------------------------------------------------
qi::rule<Iter, string()> schedule_word =
    ascii::string("--all-definitional")
    | ascii::string("--no-definitional")
    // Yes, you do need the extra space so that it doesn't get recognized 
    // instead of --random-reorder-literals!
    | ascii::string("--random-reorder ")
    | ascii::string("--random-reorder-literals")
    | ascii::string("--all-start")
    | ascii::string("--pos-neg-start")
    | ascii::string("--conjecture-start")
    | ascii::string("--restrict-start")
    | ascii::string("--no-regularity")
    | ascii::string("--all-lemmata")
    | ascii::string("--all-reductions")
    | ascii::string("--all-extensions")
    | ascii::string("--no-lemmata")
    | ascii::string("--all-backtrack")
    | ascii::string("--lemmata-backtrack")
    | ascii::string("--reduction-backtrack")
    | ascii::string("--extension-backtrack")
    | ascii::string("--explore-left-trees")
    | ascii::string("--limit-by-tree-depth");

qi::rule<Iter, string()> schedule_word_param =
      ascii::string("--complete")
      | ascii::string("--reorder")
      | ascii::string("--start-depth")
      | ascii::string("--depth-increment");
//--------------------------------------------------------------
// Grammar for parser.
//--------------------------------------------------------------
template<typename It>
  struct schedule_grammar
  : qi::grammar<It, ascii::space_type>
  {
      schedule_grammar()
      : schedule_grammar::base_type(schedule) {
          
          schedule_item %= 
            ((schedule_word [set_step()])
            | ((schedule_word_param [set_step()]) 
               >> (qi::uint_) [set_value()]));

          schedule_line %= 
            ((qi::uint_ [add_time()])
            >> *(schedule_item [add_step()]) 
            >> lit(';') [next_settings()]);

          schedule %= *schedule_line;
      }
      qi::rule<Iter, ascii::space_type> schedule_item;
      qi::rule<Iter, ascii::space_type> schedule_line;
      qi::rule<Iter, ascii::space_type> schedule;
  };
//--------------------------------------------------------------
// Implementation of Schedule.
//--------------------------------------------------------------
void Schedule::read_schedule_from_file(fs::path path) {
    string file_contents;
    if (path == "default") {
        params::set_default_schedule();
        file_contents = params::default_schedule;
    }
    else {
        ifstream file;
        file.open(path);
        if (file.fail()) {
            throw (file_open_exception(path));
        }
        string current_line;
        std::getline(file, current_line);
        file_contents += current_line;
        while (file.good()) {
            std::getline(file, current_line);
            file_contents += current_line;
        }
        file.close();
    }
   
    Iter start = file_contents.begin();
    Iter end = file_contents.end();

    schedule_grammar<Iter> g;
    bool result = qi::phrase_parse(start, end, g, ascii::space);

    if (start != end || !result) {
        std::cerr << "Failed to parse schedule file." << endl;
        new_schedule.clear();
        new_times.clear();
    }
    schedule = new_schedule;
    times = new_times;
    if (times.back() != 0)
        std::cerr << "Warning: the last time entry in the schedule should be 0" << endl;
    unsigned int total = 0;
    for (unsigned int t : times) 
        total += t;
    if (total > 100) 
        std::cerr << "Warning: your time percentages add up to more than 100" << endl;
}   
//--------------------------------------------------------------
void Schedule::apply_item(const pair<schedule_step,unsigned int>& item) {
    schedule_step step = item.first;
    unsigned int value = item.second;
    switch (step) {
        case schedule_step::all_definitional:
            if (params::no_definitional) {
                params::no_definitional = false;
                cerr << "Warning: --all-definitional cancels --no-definitional." << endl;
            }
            params::all_definitional = true;
            break;
        case schedule_step::no_definitional:
            if (params::all_definitional) {
                params::all_definitional = false;
                cerr << "Warning: --no-definitional cancels --all-definitional." << endl;
            }
            params::no_definitional = true;
            break;
        case schedule_step::reorder:
            params::deterministic_reorder = true;
            params::number_of_reorders = value;
            break;
        case schedule_step::rand_reorder:
            params::random_reorder = true;
            break;
        case schedule_step::rand_lits:
            params::random_reorder_literals = true;
            break;
        case schedule_step::all_start:
            params::set_all_start();
            break;
        case schedule_step::pos_neg_start:
            if (params::all_start) {
                cerr << "Warning: are you sure you want to mix --all-start with --pos-neg-start?" << endl;
            }
            params::all_pos_neg_start = true;
            break;
        case schedule_step::conjecture_start:
            if (params::all_start) {
                cerr << "Warning: are you sure you want to mix --all-start with --conjecture-start?" << endl;
            }
            params::conjecture_start = true;
            break;
        case schedule_step::restrict_start:
            if (params::all_start) {
                cerr << "Warning: are you sure you want to mix --all-start with --restrict-start?" << endl;
            }
            params::restrict_start = true;
            break;
        case schedule_step::no_regularity:
            params::use_regularity_test = false;
            break;
        case schedule_step::all_lemmata:
            params::limit_lemmata = false;
            break;
        case schedule_step::all_reductions:
            params::limit_reductions = false;
            break;
        case schedule_step::all_extensions:
            params::limit_extensions = false;
            break;
        case schedule_step::no_lemmata:
            params::use_lemmata = false;
            break;
        case schedule_step::all_backtrack:
            params::set_all_backtrack();
            break;
        case schedule_step::lemmata_backtrack:
            params::limit_bt_lemmas = false;
            break;
        case schedule_step::reduction_backtrack:
            params::limit_bt_reductions = false;
            break;
        case schedule_step::extension_backtrack:
            params::limit_bt_extensions = false;
            break;
        case schedule_step::explore_left_trees:
            params::limit_bt_extensions_left_tree = false;
            break;
        case schedule_step::complete:
            params::switch_to_complete = value;
            break;
        case schedule_step::start_depth:
            params::start_depth = value;
            break;
        case schedule_step::depth_inc:
            params::depth_increment = value;
            break;
        case schedule_step::limit_by_tree_depth:
            params::limit_by_tree_depth = true;
            break;
        default:
            break;
    }
}
//--------------------------------------------------------------
 pair<bool,unsigned int> Schedule::set_next_schedule() {
    params::set_default_schedule_parameters();
    pair<bool,unsigned int> result(false,0);
    if (schedule_step_number == schedule.size())
        return result;
    for(size_t i = 0; i < schedule[schedule_step_number].size(); i++) {
        apply_item((schedule[schedule_step_number])[i]);
    }
    result.first = true;
    result.second = times[schedule_step_number];
    schedule_step_number++;
    /*
    * Make sure there is something specified as a start clause.
    */
    if (params::no_start_options()) {
        params::correct_missing_start_options();
    }
    return result;
 }
 //--------------------------------------------------------------
 string Schedule::step_to_string(size_t n) const {
    string result("Time: ");
    if (n < schedule.size()) {
        result += std::to_string(times[n]);
        for (size_t j = 0; j < schedule[n].size(); j++) {
            result += " (";
            result += to_string((schedule[n])[j].first);
            result += ", ";
            result += std::to_string((schedule[n])[j].second);
            result += ")";
        }
    }
    return result; 
 }
 //--------------------------------------------------------------
 ostream& operator<<(ostream& out, const Schedule& s) {
    for (size_t i = 0; i < s.schedule.size(); i++) {
        out << s.step_to_string(i) << endl;
    }
    return out;
 }

}