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

#include "Parameters.hpp"

//------------------------------------------------------------------
// Cosmetic output options.
//------------------------------------------------------------------
uint8_t params::verbosity = 2;
bool params::use_colours = true;
uint8_t params::indent_size = 4;
uint8_t params::output_width = 7;
uint32_t params::output_frequency = 50000;
bool params::output_terms_with_substitution = false;
std::string params::problem_name = "Unknown";
bool params::write_output_summary = false;
std::string params::definitional_predicate_prefix = "_def";
std::string params::unique_var_prefix = "_u";
std::string params::unique_skolem_prefix = "skolem";
bool params::first_parse = true;
//------------------------------------------------------------------
// CNF conversion.
//------------------------------------------------------------------
bool params::miniscope = true;
bool params::all_definitional = false;
bool params::no_definitional = false;
//------------------------------------------------------------------
// Equality axioms.
 //------------------------------------------------------------------
bool params::add_equality_axioms = true;
bool params::equality_axioms_at_start = true;
bool params::all_distinct_objects = false;
bool params::no_distinct_objects = false;
//------------------------------------------------------------------
// Reordering
//------------------------------------------------------------------
unsigned params::random_seed = 0;
uint32_t params::boost_random_seed = 0;
bool params::deterministic_reorder = false;
uint32_t params::number_of_reorders = 0;
bool params::random_reorder = false;
bool params::random_reorder_literals = false;
//------------------------------------------------------------------
// Timeout.
//------------------------------------------------------------------
bool params::timeout = false;
uint32_t params::timeout_value = UINT32_MAX;
//------------------------------------------------------------------
// Use of schedule.
//------------------------------------------------------------------
bool params::use_schedule = false;
//------------------------------------------------------------------
// Positive/negative representation.
//------------------------------------------------------------------
bool params::positive_representation = false;
//------------------------------------------------------------------
// Deepening.
//------------------------------------------------------------------
uint32_t params::start_depth = 2;
uint32_t params::depth_limit = UINT32_MAX;
uint32_t params::depth_increment = 1;
bool params::limit_by_tree_depth = false;
bool params::depth_limit_all = false;
//------------------------------------------------------------------
// Start clauses.
//------------------------------------------------------------------
bool params::all_start = false;
bool params::all_pos_neg_start = false;
bool params::conjecture_start = false;
bool params::restrict_start = false;
//------------------------------------------------------------------
// Use of regularity test.
//------------------------------------------------------------------
bool params::use_regularity_test = true;
//------------------------------------------------------------------
// Various basic limitations of search.
//------------------------------------------------------------------
bool params::use_lemmata = true;
bool params::limit_lemmata = true;
bool params::limit_reductions = true;
bool params::limit_extensions = true;
bool params::limit_bt_all = true;
bool params::limit_bt_lemmas = true;
bool params::limit_bt_reductions = true;
bool params::limit_bt_extensions = true;
bool params::limit_bt_extensions_left_tree = true;
//------------------------------------------------------------------
// Move to a complete search.
//------------------------------------------------------------------
uint32_t params::switch_to_complete = UINT32_MAX;
//------------------------------------------------------------------
// Generation of proof for output.
//------------------------------------------------------------------
bool params::verify_proof_verbose = false;
bool params::verify_proof = false;
bool params::build_proof = false;
bool params::generate_LaTeX_proof = false;
bool params::sub_LaTeX_proof = false;
int params::latex_truncation_length = 25;
bool params::latex_tiny_proof = false;
bool params::latex_include_matrix = true;
bool params::generate_Prolog_proof = false;
bool params::generate_tptp_proof = false;
//------------------------------------------------------------------
// Assorted file paths.
//------------------------------------------------------------------
std::filesystem::path params::LaTeX_proof_path = "latex_proof.tex";
std::filesystem::path params::Prolog_matrix_path = "matrix.pl";
std::filesystem::path params::Prolog_proof_path = "proof.pl";
std::filesystem::path params::output_summary_path = "output_summary.txt";
std::filesystem::path params::schedule_path = ".";
std::filesystem::path params::tptp_path = ".";
std::filesystem::path params::pwd_path = ".";
std::filesystem::path params::connectpp_path = ".";
std::filesystem::path params::full_problem_path;
//------------------------------------------------------------------
// Default schedule.
//------------------------------------------------------------------
std::string params::default_schedule;

void params::set_default_schedule() {
  default_schedule =  "10  --complete 7                                                                                                           ;\n";
  default_schedule += "15  --conjecture-start --all-definitional                                                                                  ;\n";
  default_schedule += "15  --no-definitional  --restrict-start                                                                                    ;\n";
  default_schedule += "10  --restrict-start   --all-backtrack                                                                                     ;\n";
  default_schedule += "5   --all-definitional                                                                                                     ;\n";
  default_schedule += "4   --conjecture-start --no-definitional                                                                                   ;\n";
  default_schedule += "2   --all-definitional --restrict-start                                                                                    ;\n";
  default_schedule += "2   --restrict-start                                                                                                       ;\n";
  default_schedule += "1   --conjecture-start --all-definitional          --all-backtrack                                                         ;\n";
  default_schedule += "4   --random-reorder   --random-reorder-literals   --conjecture-start --no-definitional   --restrict-start                 ;\n"; 
  default_schedule += "4   --random-reorder   --random-reorder-literals   --all-definitional --restrict-start                                     ;\n";
  default_schedule += "2   --random-reorder   --random-reorder-literals   --all-definitional --restrict-start                                     ;\n";
  default_schedule += "2   --random-reorder   --random-reorder-literals   --all-definitional --restrict-start                                     ;\n";
  default_schedule += "2   --random-reorder   --random-reorder-literals   --no-definitional                                                       ;\n";
  default_schedule += "2   --random-reorder   --random-reorder-literals   --conjecture-start --all-definitional                                   ;\n";
  default_schedule += "2   --random-reorder   --random-reorder-literals   --conjecture-start --all-definitional                                   ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --all-definitional                                   ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --all-definitional                                   ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --no-definitional   --restrict-start                 ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --no-definitional   --restrict-start                 ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --no-definitional   --restrict-start                 ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --no-definitional   --restrict-start --all-backtrack ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --conjecture-start --no-definitional   --restrict-start --all-backtrack ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --all-definitional --restrict-start    --all-backtrack                  ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --all-definitional --restrict-start                                     ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --all-definitional --restrict-start                                     ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --no-definitional                                                       ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --no-definitional                                                       ;\n";
  default_schedule += "1   --random-reorder   --random-reorder-literals   --no-definitional  --restrict-start    --all-backtrack                  ;\n";
  default_schedule += "0   --all-definitional --all-backtrack                                                                                     ;\n";
}
//------------------------------------------------------------------------
bool params::show_clauses = false;
//------------------------------------------------------------------
void params::set_default_schedule_parameters() {
  all_definitional = false;
  no_definitional = false;

  deterministic_reorder = false;
  number_of_reorders = 0;
  random_reorder = false;
  random_reorder_literals = false;

  start_depth = 2;
  depth_increment = 1;
  limit_by_tree_depth = false;

  all_start = false;
  all_pos_neg_start = false;
  conjecture_start = false;
  restrict_start = false;

  use_regularity_test = true;
  
  use_lemmata = true;
  limit_lemmata = true;
  limit_reductions = true;
  limit_extensions = true;
  limit_bt_all = true;
  limit_bt_lemmas = true;
  limit_bt_reductions = true;
  limit_bt_extensions = true;
  limit_bt_extensions_left_tree = true;

  switch_to_complete = UINT32_MAX;
}
//------------------------------------------------------------------------
void params::set_complete_parameters() {
  all_start = false;
  all_pos_neg_start = true;
  conjecture_start = false;
  restrict_start = false;

  limit_bt_all = false;
  limit_bt_reductions = false;
  limit_bt_extensions = false;
  limit_bt_extensions_left_tree = false;
}
//------------------------------------------------------------------------
bool params::search_is_complete() {
  bool start_conditions_ok =
    (all_pos_neg_start || all_start) && !restrict_start && !conjecture_start;

  // You don't care about lemmas.
  bool backtracking_ok =
    !limit_bt_all && !limit_bt_reductions && !limit_bt_extensions &&
    !limit_bt_extensions_left_tree;

  return start_conditions_ok && backtracking_ok;
}
//------------------------------------------------------------------------
void params::set_all_backtrack() {
  limit_bt_all = false;
  limit_bt_lemmas = false;
  limit_bt_reductions = false;
  limit_bt_extensions = false;
  limit_bt_extensions_left_tree = false;
}
//------------------------------------------------------------------------
bool params::no_start_options() {
  return !all_start &&
  !all_pos_neg_start &&
  !conjecture_start && 
  !restrict_start;
}
//------------------------------------------------------------------------
void params::correct_missing_start_options() {
  all_start = false;
  all_pos_neg_start = true;
  conjecture_start = false;
  restrict_start = false;
}
//------------------------------------------------------------------------
void params::set_all_start() {
  all_start = true;
  all_pos_neg_start = false;
  conjecture_start = false;
  restrict_start = false;
}