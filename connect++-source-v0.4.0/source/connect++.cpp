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

#include <iostream>
#include <vector>
#include <chrono>
#include <filesystem>
#include <ctime>
#include <cstdlib>
#include <csignal>

#include <boost/program_options.hpp>

#include "connect++-version.hpp"

#include "StackProver.hpp"
#include "Schedule.hpp"
#include "ProofChecker.hpp"

using std::cout;
using std::endl;
using std::get;

namespace fs = std::filesystem;
namespace chrono = std::chrono;
namespace po = boost::program_options;

using namespace verbose_print;
using namespace boost::spirit;

/*
* Various signal handlers.
*/
void SIGINT_handler(int p) {
  cout << endl << "% SZS status Error for " 
       << params::problem_name 
       << " : terminated by SIGINT." << endl;
  exit(EXIT_FAILURE);
}
void SIGXCPU_handler(int p) {
  cout << endl << "% SZS status Timeout for "
       << params::problem_name
       << " : terminated by SIGXCPU." << endl;
  exit(EXIT_FAILURE);
}
void SIGALRM_handler(int p) {
  cout << endl << "% SZS status Timeout for " 
       << params::problem_name 
       << " : terminated by SIGALRM." << endl;
  exit(EXIT_FAILURE);
}

int main(int argc, char** argv) {
  /*
  * Start the timer...
  */
  chrono::steady_clock::time_point startTime;
  startTime = chrono::steady_clock::now();
  /*
  * Set up handlers for signals.
  */
  std::signal(SIGINT, SIGINT_handler);
  std::signal(SIGXCPU, SIGXCPU_handler);
  std::signal(SIGALRM, SIGALRM_handler);
  /*
  * Pick up relevant environment variables for the 
  * TPTP library etc. Some of these may be overidden by a 
  * command line argument later.
  */
  char* tptp_env = getenv("TPTP");
  if (tptp_env != nullptr) {
     params::tptp_path = fs::path(tptp_env);
  }
  char* pwd_env = getenv("PWD");
  if (pwd_env != nullptr) {
     params::pwd_path = fs::path(pwd_env);
  }
  char* path_env = getenv("CONNECTPP_PATH");
  if (path_env != nullptr) {
     params::connectpp_path = fs::path(path_env);
  }
  else {
     params::connectpp_path = params::pwd_path;
  }
  /*
  * Initially, use the Boost Program Options library to decipher
  * what's been added in the command line and deal with it.
  */
  po::options_description main_options("Basic options");
  main_options.add_options()
    ("help,h", 
        "Show this message.")
    ("version", 
        "Show version number.")
    ("input,i", po::value<string>(), 
        "Input filename.")
    ("output,o", po::value<string>(), 
        "Write a short output summary (file, status, outcome, time etc) to the specified file. Using \"default\" places it in \"./output_summary.txt\"" )
    ("no-equality", 
        "Don't add equality axioms. (For example, if they were added elsewhere.) NOTE: also inhibits adding of distinct object axioms.")
    ("equality-last", 
        "Place equality axioms at the end of the matrix, not the beginning")
    ("all-distinct-objects", 
        "By default Connect++ follows the TPTP convention of considering \"foobar\" to be a distinct object. This option makes *all* constants distinct.")
    ("no-distinct-objects", 
        "By default Connect++ follows the TPTP convention of considering \"foobar\" to be a distinct object. This option disables that behaviour, so constants can be equal to others.")
    ("timeout,t", po::value<int>(), 
        "Timeout in seconds. (Default UINT32_MAX).")
    ("show-default-schedule", 
        "Display the build-in default schedule and halt.")
    ("schedule,s", po::value<string>(), 
        "Instead of running with fixed parameters, use a schedule from the specified file. Use value \"default\" for the default schedule. If no --timeout is specified use 600s.")
    ("random-seed", po::value<int>(), 
        "Specify the (non-negative, integer) seed to use for random number generation. Default 0.")
    ("tptp", po::value<string>(), 
        "Specify a path for the TPTP. Alternative to using the TPTP environment variable.")
    ("path", po::value<string>(), 
        "Specify the path for output files other than the one produced by --output. Alternative to using the CONNECTPP_PATH environment variable."); 

  po::options_description conversion_options("Clause conversion");
  conversion_options.add_options()
    ("no-definitional", 
        "Don't apply definitional transformation for any formula.")
    ("all-definitional", 
        "Apply definitional transformation to all formulas.")
    ("reorder,r", po::value<int>(), 
        "Reorder the clauses a specified number of times.")
    ("random-reorder",  
        "Randomly reorder the clauses.")
    ("random-reorder-literals",  
        "Randomly reorder the literals in each clause in the matrix.")
    ("no-miniscope", 
        "Don't miniscope when converting to CNF.")
    ("show-clauses",  
        "Show translation of first-order formulas to clauses and halt.");

  po::options_description output_options("Output formatting");
  output_options.add_options()
    ("verbosity,v", po::value<int>(), 
        "Set verbosity level (0-3). Default is 2.")
    ("no-colour", 
        "Don't use colour to highlight output.")
    ("sub-output", 
        "Include substitutions when writing output.")
    ("indent", po::value<int>(), 
        "Set indentation size. (Default 4.)")
    ("out-int", po::value<int>(), 
        "Interval for updating output (default 50,000).");

  po::options_description search_options("Search control");
  search_options.add_options()
    ("all-start", 
        "Use all start clauses. (Overides other start clause options.)")
    ("pos-neg-start", 
        "Use all positive/negative start clauses, according to representation (currently always negative). (Interacts with other start clause options.)")
    ("conjecture-start", 
        "Use all conjecture clauses as start clauses. (Interacts with other start clause options.)")
    ("restrict-start", 
        "Only use one start clause. (Interacts with other start clause options.)")
    ("no-regularity", 
        "Don't use the regularity test.")
    ("all-reductions", 
        "Compute reductions for all literals in the clause, not just the first one.")
    ("all-extensions", 
        "Compute extensions for all literals in the clause, not just the first one.")
    ("all-lemmata", 
        "When using lemmata, consider all literals in the clause, not just the first one.")
    ("no-lemmata", 
        "Do not use lemmata.");

  po::options_description backtrack_options("Backtracking");
  backtrack_options.add_options()
    ("all-backtrack", 
        "Do not limit any backtracking.")
    ("lemmata-backtrack", 
        "Do not limit backtracking for lemmata.")
    ("reduction-backtrack", 
        "Do not limit backtracking for reductions.")
    ("extension-backtrack",
        "Do not limit backtracking for extensions.")
    ("explore-left-trees", 
        "Apply backtracking within left extension trees.")
    ("complete,c", po::value<int>(), 
        "Start again with a complete search on reaching the specified depth. (Default UINT32_MAX.)");

  po::options_description depth_options("Depth limiting");
  depth_options.add_options()
    ("depth-limit,d", po::value<int>(), 
        "Maximum depth/path length. (Default UINT32_MAX.)")
    ("start-depth", po::value<int>(), 
        "Initial depth/path length. (Default 1.)")
    ("depth-increment", po::value<int>(), 
        "Increment for iterative deepening. (Default 1.)")
    ("depth-limit-all", 
        "By default we do not depth limit on reductions or lemmata. Set this if you want to.")
    ("limit-by-tree-depth", 
        "Use tree depth (not path length) for deepening.");

  po::options_description proof_options("Proof generation");
  proof_options.add_options()
    ("tptp-proof", 
        "Generate a proof compatible with the TPTP. Note that what constitutes a TPTP-compatible proof in connection calculus is currently a moving target, so the format is subject to change. Output is to stdout.")
    ("prolog-proof", 
        "Generate Prolog format files proof.pl and matrix.pl and store in the $CONNECTPP_PATH directory. You can check these using the check_proof utility.")
    ("full-verify", 
        "Verify any proof found using the internal proof checker. Use this version to get a detailed description of the verification sent to stdout.")
    ("verify", 
        "Verify any proof found using the internal proof checker. Use this version for a quiet verification that only adds \"Verified\" or \"FaliedVerification\" to the output string."); 

  po::options_description latex_options("LaTeX output");
  latex_options.add_options()
    ("latex", po::value<string>(), 
        "Make a LaTeX file containing a typeset proof. Use \"default\" for \"./latex_proof.tex\" or specify a destination.")
    ("sub-latex", 
        "Include substitutions in the LaTeX proof.")
    ("tiny-latex", 
        "Typeset the latex proof in a tiny font.")
    ("latex-no-matrix", 
        "Don't include the matrix in the LaTeX proof.");

  po::options_description all_options("Options");
  all_options.add(main_options)
    .add(conversion_options)
    .add(output_options)
    .add(search_options)
    .add(backtrack_options)
    .add(depth_options)
    .add(proof_options)
    .add(latex_options);

  po::positional_options_description pos_opts;
  pos_opts.add("input", -1);
  po::variables_map vars_map;
  try {
    po::store(po::command_line_parser(argc, argv).
              options(all_options).
              positional(pos_opts).
              run(), vars_map);
  }
  /*
  * If the command line options are in error then we exit here.
  */
  catch (boost::program_options::error& err) {
      cout << "% SZS status Error for "
           << params::problem_name << " : " << err.what() << endl;
      return EXIT_FAILURE;
  }
  po::notify(vars_map);
  /*
  * We had a correct parse of the command line, so now we deal with 
  * the options.
  */
  if (vars_map.count("help")) {
    cout << all_options << endl;
    return EXIT_SUCCESS;
  }
  if (vars_map.count("version")) {
    cout << "Connect++ Version V" << VERSION << "." << endl;
    cout << "Copyright © 2021-24 Sean Holden. All rights reserved." << endl;
    return EXIT_SUCCESS;
  }
  if (vars_map.count("verbosity")) {
    int v = vars_map["verbosity"].as<int>();
    if (v >= 0 && v <= 3) 
      params::verbosity = v;
    else
      cerr << "Verbosity should be between 0 and 3. Using default." << endl;
  }
  VPrint show(params::verbosity);
  if (vars_map.count("sub-output")) {
      params::output_terms_with_substitution = true;
  }
  if (vars_map.count("indent")) {
    int i = vars_map["indent"].as<int>();
    if (i >= 0 && i <= UINT8_MAX)
      params::indent_size = i;
    else
      cerr << "Indent size is negative or too large. Using default." << endl;
  }
  if (vars_map.count("out-int")) {
    int i = vars_map["out-int"].as<int>();
    if (i > 0 && i <= UINT32_MAX)
      params::output_frequency = i;
    else
      cerr << "Interval is negative or too large. Using default." << endl;
  }
  if (vars_map.count("no-equality")) {
    params::add_equality_axioms = false;
  }
  if (vars_map.count("equality-last")) {
    params::equality_axioms_at_start = false;
  }
  if (vars_map.count("all-distinct-objects")) {
    params::all_distinct_objects = true;
  }
  if (vars_map.count("no-distinct-objects")) {
    if (params::all_distinct_objects) {
      cerr << "Cancelled --all-distinct-objects." << endl;
      params::all_distinct_objects = false;
    }
    params::no_distinct_objects = true;
  }
  if (vars_map.count("timeout")) {
    params::timeout = true;
    int t = vars_map["timeout"].as<int>();
    if (t > 0) {
      if (t >= 10)
        params::timeout_value = t;
      else {
        cerr << "Timeout is too small. Using 10 seconds." << endl;
        params::timeout_value = 10;
      }
    }
    else
      cerr << "Timeout should be positive. Using default." << endl;
  }
  if (vars_map.count("show-default-schedule")) {
    params::set_default_schedule();
    cout << params::default_schedule << endl;
    exit(EXIT_SUCCESS);
  }
  if (vars_map.count("path")) {
    params::connectpp_path = vars_map["path"].as<string>();
  }
  // You should now have all the paths you need, so 
  // finalize them where possible.
  params::LaTeX_proof_path 
    = params::pwd_path / params::LaTeX_proof_path;
  params::Prolog_matrix_path 
    = params::connectpp_path / params::Prolog_matrix_path;
  params::Prolog_proof_path 
    = params::connectpp_path / params::Prolog_proof_path;
  params::output_summary_path 
    = params::pwd_path / params::output_summary_path;

  if (vars_map.count("output")) {
    params::write_output_summary = true;
    string op = vars_map["output"].as<string>();
    if (op != "default")
      params::output_summary_path = op;
  }
  if (vars_map.count("all-definitional")) {
    params::all_definitional = true;
  }
  if (vars_map.count("no-definitional")) {
    params::no_definitional = true;
    if (params::all_definitional) {
      cerr << "Setting --no-definitional has cancelled --all-definitional." << endl;
      params::all_definitional = false;
    }
  }
  schedule::Schedule schedule;
  if (vars_map.count("schedule")) {
    params::use_schedule = true;
    if (!params::timeout) {
      params::timeout = true;
      params::timeout_value = 600;
    }
    params::schedule_path = vars_map["schedule"].as<string>();
    try {
      schedule.read_schedule_from_file(params::schedule_path);
    }
    catch (std::exception& err) {
      cout << "% SZS status Error for "
           << params::problem_name << " : " << err.what() << endl;
      return EXIT_FAILURE;
    }
  }
  /*
  * Note: overides $TPTP environment variable, which is read 
  * earlier.
  */
  if (vars_map.count("tptp")) {
    params::tptp_path = vars_map["tptp"].as<string>();
  }
  if (vars_map.count("reorder")) {
    int n = vars_map["reorder"].as<int>();
    if (n > 0) {
      params::deterministic_reorder = true;
      params::number_of_reorders = n;
    }
    else 
      cerr << "Number of re-orders should be positive. Skipping." << endl;
  }
   if (vars_map.count("random-seed")) {
    int seed = vars_map["random-seed"].as<int>();
    if (seed >= 0) {
      params::random_seed = static_cast<unsigned>(seed);
      params::boost_random_seed = static_cast<uint32_t>(seed);
    }
    else{
      cerr << "Error: random seed must be a non-negative integer. Using default of 0." << endl;
    }
  }
  if (vars_map.count("random-reorder")) {
    params::random_reorder = true;
  }
  if (vars_map.count("random-reorder-literals")) {
    params::random_reorder_literals = true;
  }
  if (vars_map.count("no-miniscope")) {
    params::miniscope = false;
  }
  if (vars_map.count("show-clauses")) {
    params::show_clauses = true;
  }
  if (vars_map.count("no-colour")) {
    params::use_colours = false;
  }
  /*
  * Set up the path for the input file. A path to the TPTP may 
  * have been set by now either by picking up the $TPTP environment 
  * variable or using a command-line option. 
  *
  * This looks really over-engineered, but the complexity that 
  * follows in dealing with TPTP includes probably makes that 
  * a good idea.
  *
  * The desired behaviour here is:
  * 
  * - If it's an absolute path then we're done.
  *
  * - If it's a relative path then see if it exists.
  * 
  * - If it doesn't exist then look for it relative 
  *   $TPTP.   
  */
  fs::path initial_path;
  bool found_file = false;
  if (vars_map.count("input")) {
    // Get what was on the command line.
    initial_path = vars_map["input"].as<string>();

    // Is it relative?
    if (initial_path.is_relative()) {
      // If it's relative, does it exist?
      if (fs::exists(initial_path)) {
        // It's an existing, relative path, so expand it. Belt 
        // and braces - make sure you catch things...
        try {
          initial_path = fs::canonical(initial_path);
        }
        catch (std::filesystem::filesystem_error& err) {
          cout << "% SZS status Error for " 
               << params::problem_name << " : " 
               << err.what() << endl;
          return EXIT_FAILURE;
        }
        found_file = true;
      }
      // It's relative, but doesn't exist...
      else {
         // So see if it's relative to $TPTP.
         fs::path tptp_path(params::tptp_path);
         initial_path = tptp_path / initial_path;
         // Does it exist now?
         if (fs::exists(initial_path)) {
          // Yes! Expand it. Belt and braces again...
          try {
            initial_path = fs::canonical(initial_path);
          }
          catch (std::filesystem::filesystem_error& err) {
            cout << "% SZS status Error for " 
                 << params::problem_name << " : " 
                 << err.what() << endl;
            return EXIT_FAILURE;
          }
          found_file = true;
        }
      }
    }
    else {
      // It's an absolute path.
      if (initial_path.is_absolute() && fs::exists(initial_path)) {
        // Found it! Tidy it up. (Yes, belt and braces etc...)
        try {
          initial_path = fs::canonical(initial_path);
        }
        catch (std::filesystem::filesystem_error& err) {
            cout << "% SZS status Error for " 
                 << params::problem_name << " : " 
                 << err.what() << endl;
            return EXIT_FAILURE;
        }
        found_file = true;
      }
    }
  }
  else {
    cout << "% SZS status Error for " 
         << params::problem_name << " : no problem specified."  << endl;
    return EXIT_FAILURE;
  }
  // Have we found an existibng file?
  if (!found_file) {
    cout << "% SZS status Error for " 
         << params::problem_name << " : the specified file does not exist."  << endl;
    return EXIT_FAILURE;
  }
  // At this point we have a nice, tidy absolute path.
  params::full_problem_path = initial_path;
  params::full_problem_path.remove_filename();
  params::problem_name = initial_path.stem().string();
  fs::path path = initial_path;

  /*
  * Finished sorting out the file/path. Back to the other 
  * options.
  */
  if (vars_map.count("depth-limit")) {
    int l = vars_map["depth-limit"].as<int>();
    if (l > 1)
      params::depth_limit = l;
    else
      cerr << "Depth limit should be positive. Using default." << endl;
  }
  if (vars_map.count("start-depth")) {
    int l = vars_map["start-depth"].as<int>();
    if (l > 1 && l <= params::depth_limit)
      params::start_depth = l;
    else
      cerr << "Start depth should be positive and bounded by the maximum depth. Using default." << endl;
  }
  if (vars_map.count("depth-increment")) {
    int l = vars_map["depth-increment"].as<int>();
    if (l > 0)
      params::depth_increment = l;
    else
      cerr << "Depth increment should be positive. Using default." << endl;
  }
  if (vars_map.count("depth-limit-all")) {
    params::depth_limit_all = true;
  }
  if (vars_map.count("limit-by-tree-depth")) {
    params::limit_by_tree_depth = true;
  }
  /**
  * Start options can appear in combinations. The method 
  * StackProver::set_up_start_clauses deals with these. In 
  * summary:
  *
  * - all-start overides everthing.
  *
  * - the remaining three are combined and the method tries 
  *   to do that sensibly. So for example, if you have pos-neg-start 
  *   and restrict-start you should just get a single pos or neg 
  *   clause as a start clause. 
  */
  if (vars_map.count("restrict-start")) {
    params::restrict_start = true;
  }
  if (vars_map.count("pos-neg-start")) {
    params::all_pos_neg_start = true;
  }
  if (vars_map.count("conjecture-start")) {
    params::conjecture_start = true;
  }
  if (vars_map.count("all-start")) {
    show(2, string("--all-start set. This cancels all other start options."), true);
    params::set_all_start();
  }
  /*
  * Careful! It is possible that no start options were set. If that's 
  * the case just set a sensible one.
  */
  if (params::no_start_options()) {
    params::correct_missing_start_options();
  }
  if (vars_map.count("no-regularity")) {
    params::use_regularity_test = false;
  }
  if (vars_map.count("lemmata-backtrack")) {
    params::limit_bt_lemmas = false;
  }
  if (vars_map.count("reduction-backtrack")) {
    params::limit_bt_reductions = false;
  }
  if (vars_map.count("extension-backtrack")) {
    params::limit_bt_extensions = false;
  }
  if (vars_map.count("explore-left-trees")) {
    params::limit_bt_extensions_left_tree = false;
  }
  if (vars_map.count("all-backtrack")) {
    show(2, string("--all-backtrack set. This prevails over all other backtracking options."), true);
    params::set_all_backtrack();
  }
  if (vars_map.count("all-reductions")) {
    params::limit_reductions = false;
  }
   if (vars_map.count("all-extensions")) {
    params::limit_extensions = false;
  }
  if (vars_map.count("all-lemmata")) {
    params::limit_lemmata = false;
  }
  if (vars_map.count("no-lemmata")) {
    params::use_lemmata = false;
  }
  if (vars_map.count("complete")) {
    int d = vars_map["complete"].as<int>();
    if (d >= params::start_depth)
      params::switch_to_complete = d;
    else {
      cerr << "Switch to complete search must happen after start depth. Using start depth." << endl;
      params::switch_to_complete = params::start_depth;
    }
  }
  if (vars_map.count("latex")) {
      params::generate_LaTeX_proof = true;
      params::build_proof = true;
      string lp = vars_map["latex"].as<string>();
      if (lp != "default")
        params::LaTeX_proof_path = lp;
  }
  if (vars_map.count("sub-latex")) {
      params::sub_LaTeX_proof = true;
  }
  if (vars_map.count("tiny-latex")) {
      params::latex_tiny_proof = true;
  }
  if (vars_map.count("latex-no-matrix")) {
      params::latex_include_matrix = false;
  }
  if (vars_map.count("tptp-proof")) {
    params::generate_tptp_proof = true;
    params::build_proof = true;
  }
  if (vars_map.count("prolog-proof")) {
    params::generate_Prolog_proof = true;
    params::build_proof = true;
  }
  if (vars_map.count("verify")) {
      params::verify_proof = true;
      params::build_proof = true;
  }
  if (vars_map.count("full-verify")) {
      params::verify_proof = true;
      params::verify_proof_verbose = true;
      params::build_proof = true;
  }
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  /*
  * Now we're ready to start the party.
  */
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  /*
  * First, state the time we're starting at.
  */
  show(1, string("Connect++ V"));
  show(1, string(VERSION));
  show(1, string(" started at: "));
  time_t date_and_time;
  time(&date_and_time);
  show(1, asctime(localtime(&date_and_time)));
  /**
  * You'll obviously be needing a prover. 
  *
  * But it's not that simple! If we're running with 
  * no schedule then we'll just need one. However 
  * if we're running with a schedule then the matrix can be 
  * different for different sets of parameters, in particular 
  * because of --no-definitional and --all-definitional.
  * We'll therefore use three different provers and 
  * switch between them.
  */
  StackProver prover_standard;
  StackProver prover_all_definitional;
  StackProver prover_no_definitional;
  StackProver* prover = &prover_standard;
  /**
  * See if you can read the supplied input file.
  *
  * But make sure that if you're using a schedule, you 
  * make one for the default settings.
  */
  if (params::use_schedule) {
    params::no_definitional = false;
    params::all_definitional = false;
  }
  show(1, string("Reading from: "));
  show(1, path.c_str(), true);
  bool found_conjecture = false;
  size_t fof_size = 0;
  try {
    prover_standard.read_from_tptp_file(path.c_str(), found_conjecture, fof_size);
  }
  catch (std::exception& err) {
    cout << "% SZS status Error for " 
         << params::problem_name << " : " 
         << err.what() << endl;
    return EXIT_FAILURE;
  }
  /**
  * If you're using a schedule, then set up provers for the 
  * extra cases.
  */
  if (params::use_schedule) {
    params::all_definitional = true;
    try {
      prover_all_definitional.read_from_tptp_file(path.c_str(), found_conjecture, fof_size);
    }
    catch (std::exception& err) {
      cout << "% SZS status Error for " 
           << params::problem_name << " : " 
           << err.what() << endl;
      return EXIT_FAILURE;
    }
    params::all_definitional = false;
    params::no_definitional = true;
    try {
      prover_no_definitional.read_from_tptp_file(path.c_str(), found_conjecture, fof_size);
    }
    catch (std::exception& err) {
      cout << "% SZS status Error for " 
           << params::problem_name << " : " 
           << err.what() << endl;
      return EXIT_FAILURE;
    }
  }
  /**
  * How long did all that take?
  */
  chrono::milliseconds parse_time =
    chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - startTime);
  show(1, string("Total parse and conversion time: "));
  show(1, std::to_string(parse_time.count()));
  show(1, string(" milliseconds."), true);

  prover_standard.set_problem_path(path);
  prover_all_definitional.set_problem_path(path);
  prover_no_definitional.set_problem_path(path);

  show(2, string("Starting proof attempt for: "), false);
  show(2, params::problem_name, true);
  /**
  * Now you're ready to try to prove something...
  */
  ProverOutcome prover_outcome;
  ProverOutcome final_outcome;
  final_outcome = ProverOutcome::TimeOut;
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  /*
  * No schedule.
  */
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  if (!params::use_schedule) {
    /**
    * We're not using a schedule, so just run once using the
    * command line options. 
    */
    /**
    * You want any timeout to include everything...
    */
    if (params::timeout) {
      chrono::seconds timeout_duration(params::timeout_value);
      prover_standard.set_timeout(startTime + timeout_duration);
    }
    /*
    * Run the prover.
    */
    prover_outcome = prover_standard.prove();
    final_outcome = prover_outcome;
  }
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  /*
  * A schedule is being used.
  */
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  else {
    /**
    * Run using the specified or default schedule. 
    */
    if (!params::timeout) {
      params::timeout = true;
      params::timeout_value = 600;
    }
    /* 
    * Convert to milliseconds and get a standard chunk of time.
    */
    chrono::milliseconds time_chunk((params::timeout_value * 1000) / 100);
    chrono::steady_clock::time_point start_time = startTime;
    chrono::milliseconds chunk_time;
    /*
    * If we're using a schedule, then it's already been read from the relevant 
    * file, so we can start it now.
    */
    size_t schedule_step_number = 1;
    pair<bool, unsigned int> next_schedule = 
              schedule.set_next_schedule();
    if (params::verbosity > 0)
      cout << endl;
    /*
    * Try each step of the schedule in turn.
    */
    while (next_schedule.first) {
      show(1, string("Schedule step "));
      show(1, std::to_string(schedule_step_number));
      show(1, string(": "));
      show(1, schedule.step_to_string(schedule_step_number - 1), true);
      /**
      * Set the appropriate prover to use.
      */
      if (params::all_definitional) {
        prover = &prover_all_definitional;
      }
      else if (params::no_definitional) {
        prover = &prover_no_definitional;
      }
      else {
        prover = &prover_standard;
      }
      /**
      * Set the timeouts.
      */
      if (next_schedule.second == 0) { 
        prover->set_timeout(startTime + chrono::seconds(params::timeout_value));
      }
      else if (schedule_step_number == 1) {
        prover->set_timeout(startTime + (next_schedule.second * time_chunk));
      }
      else {
        prover->set_timeout(start_time + (next_schedule.second * time_chunk));
      }

      prover_outcome = prover->prove();
      
      if (prover_outcome == ProverOutcome::Valid ||
        prover_outcome == ProverOutcome::Error ||
        prover_outcome == ProverOutcome::False) {
          final_outcome = prover_outcome;
          break;
      }
      
      chunk_time = chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - start_time);
      
      show.nl(1, 2);
      show(1, string("Timeout after "));
      show(1, std::to_string(chunk_time.count()));
      show(1, string(" milliseconds"), true);

      start_time = chrono::steady_clock::now();
      schedule_step_number++;
      next_schedule = schedule.set_next_schedule();
    }
  }
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  // We're done, so tidy up.
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  //------------------------------------------------------------------------
  if (params::verbosity > 0) {
    cout << endl;
    prover->show_statistics();
  }
  /**
  * Stop the timer.
  */
  chrono::milliseconds runTime =
    chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - startTime);
  show(1, string("Total run time: "));
  show(1, std::to_string(runTime.count()));
  show(1, string(" milliseconds."), true);
  /*
   * Display the outcome.
   *
   * Note that there are a bunch of special cases here, depending on 
   * some possible outcomes of the original clause simplification:
   *
   * - You have fof (+cnf, +maybe equality) axioms, and the conjecture can be $false, or empty, 
   *   or something.
   *
   * - You have no axioms (after simplification) and there's a conjecture 
   *   which is not $true or $false but may be empty.
   */
   string status(prover->get_status());
   string outcome;
   
   bool cnf = prover->problem_is_cnf_only();
   bool conj_true = prover->problem_has_true_conjecture();
   bool conj_false = prover->problem_has_false_conjecture();
   bool conj_missing = prover->problem_has_missing_conjecture();
   bool neg_conj_removed = prover->problem_has_negated_conjecture_removed();
   bool fof_has_axioms = prover->problem_has_fof_axioms();
   bool simplified_has_axioms = prover->simplified_problem_has_fof_axioms();

   cout << "% SZS status ";
   switch (final_outcome) {
    case ProverOutcome::Valid:
      // It's a proved CNF-only problem.
      if (cnf) 
        outcome = "Unsatisfiable";
      // It's a proved FOF problem.
      else {
        // The problem has axioms.
        if (simplified_has_axioms) {
          // Axioms and $true conjecture.
          if (conj_true) {
            outcome = "ContradictoryAxioms";
          }
          // Axioms and $false conjecture.
          else if (conj_false || neg_conj_removed) {
            outcome = "ContradictoryAxioms";
          }
          // There was no conjecture. In this case we treat the 
          // axioms as a conjecture, according to the SZS specs.
          else if (conj_missing) {
            outcome = "Unsatisfiable";
          }
          // Axioms and negated conjecture.
          else {
            outcome = "Theorem";
          }
        }
        // The problem doesn't have axioms. Uuurgh... we have to distinguish 
        // between problems that had none in the first place, and problems 
        // where they were simplified out.
        //
        // Luckily they turn out to be the same.
        else {
          // There's no conjecture because it was essentially $false.
          if (neg_conj_removed) {
            outcome = "Error";
          }
          // No axioms remaining, but there is a negated conjecture.
          else 
            outcome = "Theorem";
        }    
      }
      break;
    case ProverOutcome::False:
      // It's a refuted CNF-only problem.
      if (cnf)
        outcome = "Satisfiable";
      // It's a refuted FOF problem.
      else {
        if (simplified_has_axioms) {
          if (conj_true) {
            outcome = "Error";
          }
          else if (conj_false || neg_conj_removed) {
            outcome = "CounterSatisfiable";
          }
          else if (conj_missing) {
            outcome = "Satisfiable";
          }
          else {
            outcome = "CounterSatisfiable";
          }
        }
        else {
          // There's no conjecture, and the axioms are $true.
          if (conj_missing)
            outcome = "Theorem";
          // There's no conjecture because it was essentially $false.
          else if (neg_conj_removed) {
            outcome = "Error";
          }
          // No axioms remaining, but there is a negated conjecture.
          else 
            outcome = "CounterSatisfiable";
        }
      }
      break;
    case ProverOutcome::PathLenLimit:
      outcome = "GaveUp";
      break;
    case ProverOutcome::Error:
      outcome = "Error";
      break;
    case ProverOutcome::TimeOut:
      // This is a slightly odd case that can arise if, for example, a 
      // depth limit is set that causes all options to run out without 
      // actually reaching a timeout.
      if (chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - startTime).count() < (params::timeout_value * 1000))
        outcome = "GaveUp";
      else
        outcome = "Timeout";
      break;
    default:
      outcome = "Error";
      break;
  }
  cout << outcome << " for " << params::problem_name;
  /*
  * If needed, verify the proof.
  */
  bool verified = false;
  if (params::verify_proof && final_outcome == ProverOutcome::Valid) {
    std::tuple<VariableIndex*, 
               FunctionIndex*, 
               PredicateIndex*, 
               TermIndex*>
               inds = prover->get_indexes();

    vector<pair<string, vector<size_t>>> 
               internal_proof(prover->get_internal_proof());

    ProofChecker checker(prover->get_matrix(),
                         internal_proof,
                         get<0>(inds), get<3>(inds));
    
    bool verification_outcome;
    string outcome_string;
    if (params::verify_proof_verbose) {
      pair<bool, string> outcome = checker.check_proof_verbose();
      verification_outcome = outcome.first;
      outcome_string = outcome.second;
    }
    else {
      verification_outcome = checker.check_proof();
    }

    if (verification_outcome) {
        verified = true;
        cout << " : Verified";
    }
    else {
        cout << " : FailedVerification";
    }

    if (params::verify_proof_verbose) {
      cout << endl << "% SZS output start Proof for " << params::problem_name << endl << endl;
      cout << outcome_string << endl;
      cout << "% SZS output end Proof for " << params::problem_name << endl;
    }
  }
  cout << endl;
  /*
  * Leave a minimal file with some outcome information.
  */
  if (params::write_output_summary) {
    try {
      std::ofstream out_file(params::output_summary_path);
      out_file << "ProblemName: " << params::problem_name << endl;
      if (found_conjecture) 
        out_file << "ConjectureFound" << endl;
      else  
        out_file << "NoConjectureFound" << endl; 
      if (status == "") 
        status = "NoStatus";
      out_file << "ProblemStatus: " << status << endl;
      out_file << "ProverOutcome: " << outcome << endl;
      if (params::verify_proof && final_outcome == ProverOutcome::Valid) {
        if (verified) 
          out_file << "Verified" << endl;
        else
          out_file << "FailedVerification" << endl; 
      }
      else
        out_file << "NoVerify" << endl;
      out_file << "Time: " << runTime.count() << endl;
      out_file.close();
    }
    catch (std::exception& err) {
      cerr << "Error: can't write output summary." << endl;
    }
  }
  /*
  * If necessary, write a TPTP proof to stdout.
  */
  if (params::generate_tptp_proof && (final_outcome == ProverOutcome::Valid)) {
    cout << "% SZS output start Proof for " << params::problem_name << endl;
    cout << prover->get_tptp_conversion_string();
    prover->show_tptp_proof();
    cout << "% SZS output end Proof for " << params::problem_name << endl;
  }
  return EXIT_SUCCESS;
}
