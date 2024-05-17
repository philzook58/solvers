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

#ifndef PARAMETERS_HPP
#define PARAMETERS_HPP

#include <cstdint>
#include <filesystem>

/**
* \brief Structure containing all the command line and
*        other options.
*
* Pretty much everything is static, because that makes sense.
*
* There are also a small number of methods for setting 
* defaults and testing for whether the configuration used 
* leads to a complete search.
*
* In most cases the name of the parameter should make it 
* self-explanatory. So parameters are only explicitly 
* documented where necessary.
*/
struct params {
  //------------------------------------------------------------------
  // Cosmetic output options.
  //------------------------------------------------------------------
  static uint8_t verbosity; 
  static bool use_colours;  
  static uint8_t indent_size; 
  static uint8_t output_width;
  static uint32_t output_frequency;
  static bool output_terms_with_substitution; // Only applies to the use of 
                                              // operator<<
  static std::string problem_name;
  static bool write_output_summary;
  static std::string definitional_predicate_prefix;
  static std::string unique_var_prefix;
  static std::string unique_skolem_prefix;
  static bool first_parse;
  //------------------------------------------------------------------
  // CNF conversion.
  //------------------------------------------------------------------
  static bool miniscope;
  static bool all_definitional;
  static bool no_definitional;
  //------------------------------------------------------------------
  // Equality axioms.
  //------------------------------------------------------------------
  static bool add_equality_axioms;
  static bool equality_axioms_at_start; 
  static bool all_distinct_objects;
  static bool no_distinct_objects;
  //------------------------------------------------------------------
  // Reordering
  //------------------------------------------------------------------
  static unsigned random_seed;
  static uint32_t boost_random_seed;
  static bool deterministic_reorder; 
  static uint32_t number_of_reorders;
  static bool random_reorder;
  static bool random_reorder_literals;
  //------------------------------------------------------------------
  // Timeout.
  //------------------------------------------------------------------
  static bool timeout;
  static uint32_t timeout_value;
  //------------------------------------------------------------------
  // Use of schedule.
  //------------------------------------------------------------------
  static bool use_schedule; 
  //------------------------------------------------------------------
  // Positive/negative representation.
  //------------------------------------------------------------------
  static bool positive_representation;
  //------------------------------------------------------------------
  // Deepening.
  //------------------------------------------------------------------
  static uint32_t start_depth; 
  static uint32_t depth_limit; 
  static uint32_t depth_increment; 
  static bool limit_by_tree_depth; 
  static bool depth_limit_all;
  //------------------------------------------------------------------
  // Start clauses.
  //------------------------------------------------------------------
  static bool all_start; 
  static bool all_pos_neg_start; 
  static bool conjecture_start; 
  static bool restrict_start; 
  //------------------------------------------------------------------
  // Use of regularity test.
  //------------------------------------------------------------------
  static bool use_regularity_test; 
  //------------------------------------------------------------------
  // Various basic limitations of search.
  //------------------------------------------------------------------
  static bool use_lemmata; 
  static bool limit_lemmata; 
  static bool limit_reductions; 
  static bool limit_extensions; 
  static bool limit_bt_all; 
  static bool limit_bt_lemmas; 
  static bool limit_bt_reductions; 
  static bool limit_bt_extensions; 
  static bool limit_bt_extensions_left_tree; 
  //------------------------------------------------------------------
  // Move to a complete search.
  //------------------------------------------------------------------
  static uint32_t switch_to_complete; 
  //------------------------------------------------------------------
  // Generation of proof for output.
  //------------------------------------------------------------------
  static bool verify_proof_verbose;
  static bool verify_proof;
  static bool build_proof; 
  static bool generate_LaTeX_proof; 
  static bool sub_LaTeX_proof; 
  static int latex_truncation_length;
  static bool latex_tiny_proof;
  static bool latex_include_matrix;
  static bool generate_Prolog_proof;
  static bool generate_tptp_proof;
  //------------------------------------------------------------------
  // Assorted file paths.
  //------------------------------------------------------------------
  static std::filesystem::path LaTeX_proof_path;
  static std::filesystem::path Prolog_matrix_path;
  static std::filesystem::path Prolog_proof_path;
  static std::filesystem::path output_summary_path;
  static std::filesystem::path schedule_path;
  static std::filesystem::path tptp_path;
  static std::filesystem::path pwd_path;
  static std::filesystem::path connectpp_path;
  static std::filesystem::path full_problem_path;
  //------------------------------------------------------------------
  // Default schedule.
  //------------------------------------------------------------------
  static std::string default_schedule;
  static void set_default_schedule();
  //------------------------------------------------------------------
  // Other output options.
  //------------------------------------------------------------------
  static bool show_clauses;
  /**
  * \brief Self-explanatory.
  * 
  * IMPORTANT: these should match the values set in Parameters.cpp, 
  * as the assumption is that a schedule modifies them using 
  * commands mimicking the command line options.
  */
  static void set_default_schedule_parameters();
  /**
  * \brief Change the parameters to make the search complete.
  */
  static void set_complete_parameters();
  /**
  * \brief Self-explanatory.
  */
  static bool search_is_complete();
  /**
  * \brief Self-explanatory.
  */
  static void set_all_backtrack();
  /**
  * \brief Self-explanatory.
  */
  static bool no_start_options();
  /**
  * \brief Self-explanatory.
  */
  static void correct_missing_start_options();
  /**
  * \brief Self-explanatory.
  */
  static void set_all_start();
};

#endif
