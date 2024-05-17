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

#include "StackProver.hpp"

uint32_t StackProver::reductions_tried = 0;
uint32_t StackProver::extensions_tried = 0;
uint32_t StackProver::lemmata_tried = 0;
uint32_t StackProver::right_branches_started = 0;

//----------------------------------------------------------------------
StackProver::StackProver()
: num_preds(0)
, var_index()
, fun_index()
, term_index()
, pred_index()
, sub_stack()
, results()
, matrix()
, path()
, new_C()
, lemmata()
, u()
, action(InferenceItemType::Start)
, si(nullptr)
, current_depth_limit(0)
, current_depth(1)
, depth_limit_reached(false)
, status()
, tptp_conversion_string()
, stack()
, right_branch_stack()
, backtrack(false)
, proof_printer(&stack)
, problem_path()
, output_interval(params::output_frequency)
, proof_count(0)
, use_timeout(false)
, end_time()
, show(params::verbosity)
, cnf_only(false)
, conjecture_true(false)
, conjecture_false(false)
, conjecture_missing(false)
, negated_conjecture_removed(false)
, fof_has_axioms(false)
, simplified_fof_has_axioms(false)
{}
//----------------------------------------------------------------------
void StackProver::set_num_preds(size_t n) {
  num_preds = n;
  matrix.set_num_preds(n);
  path.set_num_preds(n);
}
//----------------------------------------------------------------------
void StackProver::read_from_tptp_file(const string& file_name, 
                                      bool& found_conjecture,
                                      size_t& fof_size) {
    TPTPParser parser(&var_index, &fun_index, &term_index, &pred_index, &matrix);
    parser.parse_tptp_from_file(file_name);
    status = parser.get_problem_status();
    bool equality = parser.equality_used();
    found_conjecture = parser.conjecture_present();
    fof_size = parser.number_of_fof_formulas();
    Predicate* equals_predicate = parser.get_equals_predicate();
    cnf_only = parser.problem_is_cnf_only();
    conjecture_true = parser.fof_conjecture_is_true();
    conjecture_false = parser.fof_conjecture_is_false();
    conjecture_missing = parser.fof_conjecture_is_missing();
    negated_conjecture_removed = parser.fof_negated_conjecture_removed();
    fof_has_axioms = parser.fof_has_axioms();
    simplified_fof_has_axioms = parser.simplified_fof_has_axioms();
    tptp_conversion_string = parser.get_tptp_conversion_string();
    parser.clear();
    num_preds = pred_index.get_num_preds();
    /*
    * num_preds for Matrix is set by parser.
    */
    path.set_num_preds(num_preds);

    if (params::show_clauses) {
      std::exit(EXIT_SUCCESS);
    }

    if (status != string("") && params::first_parse) {
      show(1, string("Problem status found: "));
      show(1, status, true);
    }
    if (equality && params::add_equality_axioms) {
      if (params::first_parse) {
        show(1, string("Problem involves equality: adding axioms for =."), true);
        params::first_parse = false;
      }
      add_equality_axioms(equals_predicate);
      if (params::equality_axioms_at_start) {
        matrix.move_equals_to_start();
      }
    }
    /*
    * Any further variables will be anonymous.
    */
    var_index.set_all_names_added();

    if (params::generate_Prolog_proof && params::build_proof) {
      matrix.write_to_prolog_file(params::Prolog_matrix_path);
    }
 }
//----------------------------------------------------------------------
void StackProver::add_equality_axioms(Predicate* equals_predicate) {
  /*
  * Equality axioms as described in Handbook of Automated
  * Reasoning, Volume 1, page 615.
  */
  Arity max_fun_arity = fun_index.find_maximum_arity();
  Arity max_pred_arity = pred_index.find_maximum_arity();
  /*
  * You need at least three variables to describe these, and
  * twice as many as the arity of the biggest predicate or
  * function.
  */
  uint32_t max_arity = max_fun_arity;
  if (max_pred_arity > max_arity)
    max_arity = max_pred_arity;
  if (max_arity < 3)
    max_arity = 3;
  vector<Term*> xs;
  vector<Term*> ys;
  string xvar("__eqx_");
  string yvar("__eqy_");
  for (size_t i = 0; i < max_arity; i++) {
    Variable* xvarp = var_index.add_named_var(xvar + std::to_string(i));
    Variable* yvarp = var_index.add_named_var(yvar + std::to_string(i));
    xs.push_back(term_index.add_variable_term(xvarp));
    ys.push_back(term_index.add_variable_term(yvarp));
  }
  /*
  * How you construct these depends on which representation you're using.
  * It's easy enough to show that the difference is only a case
  * of swapping negations. See for example "Equality Preprocessing in
  * Connection Calculi", Oliver and Otten.
  */
  bool pol = !params::positive_representation;
  uint32_t n_added = 0;
  /*
  * Axiom for reflexivity.
  */
  vector<Term*> ref;
  ref.push_back(xs[0]);
  ref.push_back(xs[0]);
  Literal reflexive(equals_predicate, ref, 2, pol);
  Clause ref_c;
  ref_c.add_lit(reflexive);
  matrix.add_clause(ref_c, "equality");
  n_added++;
  /*
  * Axiom for symmetry.
  */
  vector<Term*> xy;
  xy.push_back(xs[0]);
  xy.push_back(xs[1]);
  vector<Term*> yx;
  yx.push_back(xs[1]);
  yx.push_back(xs[0]);
  Literal sym1(equals_predicate, xy, 2, !pol);
  Literal sym2(equals_predicate, yx, 2, pol);
  Clause sym_c;
  sym_c.add_lit(sym1);
  sym_c.add_lit(sym2);
  matrix.add_clause(sym_c, "equality");
  n_added++;
  /*
  * Axiom for transitivity.
  */
  vector<Term*> yz;
  yz.push_back(xs[1]);
  yz.push_back(xs[2]);
  vector<Term*> xz;
  xz.push_back(xs[0]);
  xz.push_back(xs[2]);
  Literal tr1(equals_predicate, xy, 2, !pol);
  Literal tr2(equals_predicate, yz, 2, !pol);
  Literal tr3(equals_predicate, xz, 2, pol);
  Clause tr_c;
  tr_c.add_lit(tr1);
  tr_c.add_lit(tr2);
  tr_c.add_lit(tr3);
  matrix.add_clause(tr_c, "equality");
  n_added++;
  /*
  * Function substitution.
  */
  for (size_t j = 0; j < fun_index.get_size(); j++) {
    Function* p = fun_index[j];
    Arity ar =  p->get_arity();
    if (ar > 0) {
      Clause c;
      vector<Term*> x1xn;
      vector<Term*> y1yn;
      for (size_t i = 0; i < ar; i++) {
        x1xn.push_back(xs[i]);
        y1yn.push_back(ys[i]);
        vector<Term*> xiyi;
        xiyi.push_back(xs[i]);
        xiyi.push_back(ys[i]);
        Literal eq_lit(equals_predicate, xiyi, 2, !pol);
        c.add_lit(eq_lit);
      }
      vector<Term*> t;
      t.push_back(term_index.add_function_term(p, x1xn));
      t.push_back(term_index.add_function_term(p, y1yn));
      Literal f_lit(equals_predicate, t, 2, pol);
      c.add_lit(f_lit);
      matrix.add_clause(c, "equality");
      n_added++;
    }
  }
  /*
  * Predicate substitution.
  */
  for (size_t j = 0; j < pred_index.get_num_preds(); j++) {
    Predicate* p = pred_index[j];
    Arity ar =  p->get_arity();
    if (ar > 0 && p != equals_predicate) {
      Clause c;
      vector<Term*> x1xn;
      vector<Term*> y1yn;
      for (size_t i = 0; i < ar; i++) {
        x1xn.push_back(xs[i]);
        y1yn.push_back(ys[i]);
        vector<Term*> xiyi;
        xiyi.push_back(xs[i]);
        xiyi.push_back(ys[i]);
        Literal eq_lit(equals_predicate, xiyi, 2, !pol);
        c.add_lit(eq_lit);
      }
      Literal p_lit1(p, x1xn, ar, !pol);
      Literal p_lit2(p, y1yn, ar, pol);
      c.add_lit(p_lit1);
      c.add_lit(p_lit2);
      matrix.add_clause(c, "equality");
      n_added++;
    }
  }
  /*
  * Distinct objects
  */
  Arity min_arity = fun_index.find_minimum_arity();
  if (!params::no_distinct_objects && min_arity == 0) {
    vector<Term*> all_distinct_constants;
    vector<Term*> empty_args;
    for (size_t i = 0; i < fun_index.get_size(); i++) {
      Function* p = fun_index[i];
      Arity ar = p->get_arity(); 
      // Remember, you don't want to do this for Skolem constants.
      string name = p->get_name();
      string prefix = name.string::substr(0,params::unique_skolem_prefix.length());
      bool is_skolem = (params::unique_skolem_prefix.string::compare(0, string::npos, prefix) == 0) &&
                       (params::unique_skolem_prefix.length() < name.length());
      bool is_quoted = (name[0] == '\"' && name[name.size() - 1] == '\"');
      if (ar == 0 && 
          !is_skolem && 
          (params::all_distinct_objects || is_quoted)) {
        Term* t = term_index.add_function_term(p, empty_args);
        all_distinct_constants.push_back(t);
      }
    }
    size_t s = all_distinct_constants.size();
    if (s > 1) {
      for (size_t i = s - 1; i > 0; i--) {
        for (size_t j = 0; j < i; j++) {
          Clause c;
          vector<Term*> args;
          args.push_back(all_distinct_constants[i]);
          args.push_back(all_distinct_constants[j]);
          Literal eq_lit(equals_predicate, args, 2, !pol);
          c.add_lit(eq_lit);
          matrix.add_clause(c, "distinct_objects");
          n_added++;          
        }
      }
    }
  }
  matrix.set_num_equals(n_added);
}
//----------------------------------------------------------------------
void StackProver::populate_stack_item() {
  /*
  * Don't waste your time if the regularity test applies.
  */
  if (params::use_regularity_test && !path.test_for_regularity(new_C))
    return;
  /*
  * Don't try to populate axioms.
  */
  if (new_C.size() == 0) {
    return;
  }
  /*
  * NOTE: As these are being stacked, lemmata are actually tried 
  * first.
  */
  /*
  * Extensions
  */
  if (params::limit_extensions) 
    matrix.find_limited_extensions(u, si->actions, new_C, var_index, term_index);
  else 
    matrix.find_all_extensions(u, si->actions, new_C, var_index, term_index);
  /*
  * Reductions
  */
  if (params::limit_reductions) 
    path.find_limited_reductions(u, si->actions, new_C);
  else 
    path.find_all_reductions(u, si->actions, new_C);
  /*
  * Lemmata
  */
  if (params::use_lemmata) {
    if (params::limit_lemmata) 
      lemmata.find_initial_lemmata(si->actions, new_C);
    else 
      lemmata.find_all_lemmata(si->actions, new_C);
  }
}
//----------------------------------------------------------------------
bool StackProver::depth_limited() {
  bool result = ((params::limit_by_tree_depth && (current_depth >= current_depth_limit))
      ||
      (!params::limit_by_tree_depth && (si->p.length() >= current_depth_limit)));
  if (result)
    depth_limit_reached = true;
  return result;
}
//----------------------------------------------------------------------
bool StackProver::axiom() const {
  return si->c.empty();
}
//----------------------------------------------------------------------
void StackProver::extend_with_action() {
  /*
  * Add a new StackItem using the next action from the list stored 
  * in the StackItem currently in play. If necessary, also 
  * add something to right_branch_stack. Populate the new list of 
  * actions and update si.
  */
  action = si->actions.back();
  si->actions.pop_back();
  current_depth++;
  /*
  * Why are the scope rules for switch so odd???
  */
  Clause old_C;
  Lemmata old_Lem;
  switch (action.T) {
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    // Lemmata.
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    case InferenceItemType::Lemma:
      lemmata_tried++;
      /*
      * If you are restricting backtracking for lemmata then
      * at this point you can remove all alternatives.
      */
      if (params::limit_bt_lemmas)
        si->restrict_backtrack();
      /*
      * Work out the new state.
      */
      new_C = si->c;
      new_C.drop_literal(action.Lindex);
      path = si->p;
      lemmata = si->l;
      /*
      * Extend the stack.
      */
      stack.push_back(StackItem(StackItemType::Lemmata, new_C, path, 
                                lemmata, current_depth));
      stack.back().set_this_action(action);
      break;
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    // Reduction.
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    case InferenceItemType::Reduction:
      reductions_tried++;
      /*
      * If you are restricting backtracking for reductions then
      * at this point you can remove all alternatives.
      */
      if (params::limit_bt_reductions)
        si->restrict_backtrack();
      /*
      * Reductions have a substitution, so apply it and remember 
      * in case you need to undo it later.
      */
      action.sigma.apply();
      sub_stack.push_all(action.sigma);
      /*
      * Work out the new state.
      */
      new_C = si->c;
      new_C.drop_literal(action.Lindex);
      path = si->p;
      lemmata = si->l;
      lemmata.push_back(action.L);
      /*
      * Extend the stack.
      */
      stack.push_back(StackItem(StackItemType::Reduction, new_C, path, 
                                lemmata, action.sigma, current_depth));
      stack.back().set_this_action(action);
      break;
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    // Extension.
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    //----------------------------------------------------------------------
    case InferenceItemType::Extension:
      extensions_tried++;
      /*
      * You're going to generate new variables, so remember where to 
      * backtrack to.
      */
      var_index.add_backtrack_point();
      /*
      * This is an Extension, so you're going to add something to 
      * right_branch_stack.
      */
      path = si->p;
      old_C = si->c;
      old_C.drop_literal(action.Lindex);
      old_Lem = si->l;
      old_Lem.push_back(action.L);
      /*
      * DON'T do populate_stack_item here! That can wait until you actually 
      * use the right branch. In fact it *has* to wait because we might 
      * apply substitutions that affect it.
      */ 
      right_branch_stack.push_back(StackItem(StackItemType::RightBranch, old_C, 
                                             path, old_Lem, current_depth));
      /*
      * The right branch needs to know where to restrict backtracking.
      */
      right_branch_stack.back().set_bt_restriction_index(stack.size() - 1);
      /*
      * Now you can deal with the left branch.
      */
      new_C = matrix[action.C_2].make_copy_with_new_vars(var_index, term_index);
      /*
      * Extensions have a substitution, so apply it and remember 
      * in case you need to undo it later.
      */
      action.sigma.apply();
      sub_stack.push_all(action.sigma);
      /*
      * Work out the new state.
      */
      new_C.drop_literal(action.Lprime);
      path.push(action.L);
      lemmata = si->l;
      /*
      * Extend the stack.
      */
      stack.push_back(StackItem(StackItemType::LeftBranch, new_C, path, 
                                lemmata, action.sigma, current_depth));
      stack.back().set_this_action(action);
      break;
    default:
      cerr << "PANIC!!! You should only have a lemmata, reduction or an extension here!"
           << endl;
      break;
  }
  /*
  * Finally, move si on and work out the next bunch of possible actions.
  */
  si = &stack.back();
  populate_stack_item();
}
//----------------------------------------------------------------------
void StackProver::process_axiom_forward() {
  /*
  * When you're moving forward in the search and you hit an axiom, 
  * you need to see whether there are right branches still needing 
  * to be dealt with. 
  *
  * Note that an empty right_branch_stack - meaning that you've 
  * found a proof - is dealt with by go().
  *
  * this_action does not get populated for the new StackItem in 
  * this case.
  */
  right_branches_started++;
  /*
  * Move the next right branch to the stack.
  */
  stack.push_back(right_branch_stack.back());
  right_branch_stack.pop_back();
  /*
  * Reset si.
  */
  si = &stack.back();
  /*
  * Set up the new state.
  */
  new_C = si->c;
  path = si->p;
  lemmata = si->l;
  current_depth = si->depth;
  /*
  * We deliberately delayed doing this, so do it now. (See 
  * documentation for StackProver::extend_with_action.)
  */
  populate_stack_item();
  /*
  * At this point you are starting a right branch, so
  * if you are restricting backtracking you remove all
  * alternatives from the relevant point in the stack.
  */
  if (params::limit_bt_extensions) {
    stack[si->bt_restriction_index].restrict_backtrack();
  }
}
//----------------------------------------------------------------------
void StackProver::backtrack_once() {
  backtrack = true;
  stack.pop_back();
  si = &stack.back();
  current_depth = si->depth;
}
//----------------------------------------------------------------------
void StackProver::reduction_backtrack() {
  sub_stack.backtrack();
  backtrack_once();
}
//----------------------------------------------------------------------
void StackProver::lemmata_backtrack() {
  backtrack_once();
}
//----------------------------------------------------------------------
void StackProver::left_extension_backtrack() {
  /*
  * You're backtracking through a left branch, so you 
  * need to remember to get rid of the corresponding 
  * right branch as well.
  */
  right_branch_stack.pop_back();
  var_index.backtrack();
  sub_stack.backtrack();
  backtrack_once();
}
//----------------------------------------------------------------------
/**
* \brief Here be DRAGONS.
*
* Care needed here. If the state is a right branch,
* then it may or may not have to go back on right_branch_stack 
* as you may or may not need to try it again, depending on the 
* settings.
*
* If you get this wrong you get a REALLY evil bug, because with the 
* standard restricted backtracking you put it back on the stack 
* when it's not needed. You then end up with extra things in 
* the proof certificate which invalidate it, even though you 
* can take them out and possibly get something valid.
*
* Guess how I know this!
*
* TODO: when I implement params::hard_prune it needs to 
* be considered here.
*/
void StackProver::right_extension_backtrack() {
  /*
  * If you're not limiting backtracking for extensions, or 
  * you *are*, but you're still exploring left trees, then this 
  * is straightforward: just put the item back on right_branch_stack 
  * so that it gets explored again later.
  */
  if (!params::limit_bt_extensions || 
      ((params::limit_bt_extensions || params::limit_bt_all) && 
        !params::limit_bt_extensions_left_tree)) {
    /*
    * Why is this necessary? After we backtrack we may make different 
    * substitutions, so in revisiting the right branch different 
    * possibilties may apply, so we re-compute them later.
    */
    stack.back().clear(); 
    right_branch_stack.push_back(stack.back());
    backtrack_once();
    return;
  }
  /*
  * We know we are limiting backtracking for extensions, and we 
  * are not exploring the left tree.
  *
  * Care is needed if you're not backtracking within the left
  * part of the tree. You need to move back down the stack,
  * deleting everything while also making sure that sub_stack
  * and var_index are correctly maintained. Also, you don't
  * want to return anything to right_branch_stack.
  *
  * This goes back to where the relevant literal was selected. 
  * Thus if you are not limiting the possibilities to only those 
  * for the first literal, it's open to the backtracking 
  * restriction to leave other possibilites to be tried, and 
  * they get picked up from this point.
  */
  if (params::limit_bt_extensions_left_tree) {
    size_t target_index = si->bt_restriction_index;
    size_t current_index = stack.size() - 1;
    while (current_index > target_index) {
      switch (si->item_type) {
        case StackItemType::Lemmata:
          break;
        case StackItemType::Reduction:
          sub_stack.backtrack();
          break;
        case StackItemType::LeftBranch:
          var_index.backtrack();
          sub_stack.backtrack();
          break;
        case StackItemType::RightBranch:
          break;
        default:
          cerr << "Something is VERY WRONG!" << endl;
          break;
      }
      backtrack_once();
      current_index--;
    }
  }
}
//----------------------------------------------------------------------
ProverResult StackProver::go() {
  /*
  * Having set up a single entry on the stack, containing a start 
  * state, search for a proof.
  *
  * Either you return by ending at the start state with nothing left
  * to try, by finding a proof, by depth limiting or by timing out.
  *
  * The backtrack variable is important here - when true you are 
  * (surprise surprise) backtracking. So mostly each case in the 
  * following switch is divided according to whether you're going 
  * forward or backtracking.  
  */
  while(true) {
    /*
    * Test for and deal with a timeout.
    */
    if (use_timeout && chrono::steady_clock::now() > end_time)
      return ProverResult::TimeOut;
    /*
    * Say what's going on.
    */
    if (output_interval.tick() && params::verbosity >= 2) {
      cout << cursor_symbols::Cursor::to_column(1);
      cout << cursor_symbols::Cursor::erase_line(2);
      cout << "Reductions: " << reductions_tried << " Extensions: " << extensions_tried;
      cout << " Lemmata: " << lemmata_tried << " Right branches: " << right_branches_started;
      cout << " Stack size: " << stack.size();
      cout.flush();
    }
    /*
    * si must point to the back of the stack at this point.
    *
    * Remember that extend_with_action will deal with this for you.
    */
    switch (si->item_type) {
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      // Deal with the start state. Essentially straightforward. Just 
      // deal with a completed search, otherwise work out the 
      // possibly actions and get on with it.
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      case StackItemType::Start:
        backtrack = false;
        if (si->actions.empty())
          return ProverResult::OptionsExhausted;
        else
          extend_with_action();
        break;
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      // Lemmata. Again, mostly straightforward. 
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      case StackItemType::Lemmata:
        /*
        * Operation is essentially similar to the reduction case.
        *
        * First deal with moving forward.
        */
        if (!backtrack) {
          if (axiom()) {
            /*
            * Either you've found a proof or you try a right branch.
            */
            if (right_branch_stack.empty())
              return ProverResult::Valid;
            else
              process_axiom_forward();
          }
          /*
          * Backtrack because of depth limiting.
          */
          else if (depth_limited() && params::depth_limit_all)
            lemmata_backtrack();
          /*
          * Backtrack because there's nothing left to try.
          */
          else if (si->actions.empty())
            lemmata_backtrack();
          /*
          * There must be something left to try, so try it.
          */
          else
            extend_with_action();
        }
        /*
        * We are moving down the stack.
        */
        else {
          /*
          * If you're backtracking then you need to jump over axioms.
          */
          if (axiom())
            lemmata_backtrack();
          /*
          * If you're not at an axiom then you can start going forward
          * again.
          */
          else
            backtrack = false;
        }
        break;
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      // Reduction. Almost identical to Lemmata, but note the 
      // slightly different backtracking requirement to take account 
      // of undoing the substitution.
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      case StackItemType::Reduction:
        /*
        * We are moving up the stack.
        */
        if (!backtrack) {
          if (axiom()) {
            /*
            * Either you've found a proof or you try a right branch.
            */
            if (right_branch_stack.empty())
              return ProverResult::Valid;
            else
              process_axiom_forward();
          }
          /*
          * Backtrack because of depth limiting.
          */
          else if (depth_limited() && params::depth_limit_all)
            reduction_backtrack();
          /*
          * Backtrack because there's nothing left to try.
          */
          else if (si->actions.empty())
            reduction_backtrack();
          /*
          * There must be something left to try, so try it.
          */
          else
            extend_with_action();
        }
        /*
        * We are moving down the stack.
        */
        else {
          /*
          * If you're backtracking then you need to jump over axioms.
          */
          if (axiom())
            reduction_backtrack();
          /*
          * If you're not at an axiom then you can start going forward
          * again.
          */
          else
            backtrack = false;
        }
        break;
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      // Left branch of Extension. Mostly similar to the Reduction 
      // and Lemmata cases, but the backtrack is again different to 
      // take care of the new variables, the substitution, and the 
      // right_branch_stack.
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      case StackItemType::LeftBranch:
        /*
        * Operation is essentially similar to the Reduction and 
        * Lemmata cases. See those for corresponding comments.
        */
        if (!backtrack) {
          if (axiom())
            process_axiom_forward();
          else if (depth_limited())
            left_extension_backtrack();
          else if (si->actions.empty())
            left_extension_backtrack();
          else
            extend_with_action();
        }
        /*
        * We are moving down the stack.
        */
        else {
          if (axiom())
            left_extension_backtrack();
          else
            backtrack = false;
        }
        break;
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      // Right branch of Extension. Mostly similar to the Reduction 
      // and Lemmata cases, but the backtrack is now much more 
      // delicate. See the documentation for right_extension_backtrack.
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      //----------------------------------------------------------------
      case StackItemType::RightBranch:
        /*
        * Operation is essentially similar to the reduction case.
        */
        if (!backtrack) {
          if (axiom()) {
            if (right_branch_stack.empty())
              return ProverResult::Valid;
            else
              process_axiom_forward();
          }
          else if (depth_limited())
            right_extension_backtrack();
          else if (si->actions.empty())
            right_extension_backtrack();
          else
            extend_with_action();
        }
        /*
        * We are moving down the stack.
        */
        else {
          if (axiom())
            right_extension_backtrack();
          else
            backtrack = false;
        }
        break;
      //----------------------------------------------------------------
      default:
        cerr << "Something is VERY WRONG!" << endl;
        break;
    }
  }
  return ProverResult::Error;
}
//----------------------------------------------------------------------
// Set start clauses according to current options.
//
// Note that restrict_start with !all_pos_neg_start and !conjecture_start
// should never be available as it would make no sense.
//
// all_pos_neg_start along with conjecture_start are on a best-effort
// basis - you may end up with nothing.
//----------------------------------------------------------------------
void StackProver::set_up_start_clauses() {
  results.clear();
  size_t m_size = matrix.get_num_clauses();
  /*
  * Make sure noone has messed up and not set any start 
  * clause optionss.
  */
  if (params::no_start_options())
    params::correct_missing_start_options();
  /*
  * The allstart option overides everything else so this is easy.
  */
  if (params::all_start) {
    for (size_t i = 0; i < m_size; i++) {
      results.push_back(StartClauseStatus::Start);
    }
    return;
  }
  bool first_clause_included = false;
  /*
  * params::all_pos_neg_start indicates use of positive
  * or negative start clauses according to the representation.
  * When you don't also have conjecture_start, either include
  * all, or just the first possibility found.
  */
  if (params::all_pos_neg_start && !params::conjecture_start) {
    for (size_t i = 0; i < m_size; i++) {
      if (
           (
             (params::positive_representation && matrix.is_positive(i))
             ||
             (!params::positive_representation && matrix.is_negative(i))
           )
           &&
           (!(params::restrict_start && first_clause_included))
         ) {
           results.push_back(StartClauseStatus::Start);
           first_clause_included = true;
      }
      else {
        results.push_back(StartClauseStatus::NoStart);
      }
    }
  }
  /*
  * Similar case if you have conjecture_start but not all_pos_neg_start.
  */
  else if (!params::all_pos_neg_start && params::conjecture_start) {
    for (size_t i = 0; i < m_size; i++) {
      if (matrix.is_conjecture(i)
          &&
          (!(params::restrict_start && first_clause_included))) {
            results.push_back(StartClauseStatus::Start);
            first_clause_included = true;
      }
      else {
        results.push_back(StartClauseStatus::NoStart);
      }
    }
  }
  /*
  * The tricky case is when you want to combine pos/neg clauses,
  * conjecture clauses, and restriction in some other way.
  *
  * Assume here that you have all_pos_neg_start and conjecture_start.
  */
  else {
    for (size_t i = 0; i < m_size; i++) {
      if (matrix.is_conjecture(i)
          &&
          (
            (params::positive_representation && matrix.is_positive(i))
            ||
            (!params::positive_representation && matrix.is_negative(i))
          )
          &&
          !(params::restrict_start && first_clause_included)) {
            results.push_back(StartClauseStatus::Start);
            first_clause_included = true;
          }
      else {
        results.push_back(StartClauseStatus::NoStart);
      }
    }
  }
  /*
  * There's a rare possibility that---because either there was no 
  * (negated) conjecture clause in the problem, or they were 
  * simplified out---at this point no start clause has been 
  * selected. If that's the case, either use all positive/negative 
  * clauses or just the first, according to the parameters set. 
  *
  * Note: this must choose at least one start clause because problems 
  * without a positive and negative clause have already been solved.
  */
  if (!first_clause_included) {
    if (params::verbosity > 2) {
      cout << "Note: you're asking for a conjecture to start, but there are none!" << endl;
      cout << "      depending on the other parameter settings, we will use one or " << endl;
      cout << "      all of the negative clauses." << endl;
    }
    // Don't forget this! If you get here you have a whole bunch of 
    // NoStart in results!
    results.clear(); 
    for (size_t i = 0; i < m_size; i++) { 
      if ((
             (params::positive_representation && matrix.is_positive(i))
             ||
             (!params::positive_representation && matrix.is_negative(i))
         ) && 
         !(params::restrict_start && first_clause_included)) {
        results.push_back(StartClauseStatus::Start);
        first_clause_included = true;
      }
      else {
        results.push_back(StartClauseStatus::NoStart);
      }
    }
  }
}
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------------------------------------------------------------
// Find a single proof using iterative deepening search.
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//----------------------------------------------------------------------
ProverOutcome StackProver::prove() {
  /** 
  * Make sure you deal with reordering. 
  */
  if (params::deterministic_reorder) {
    deterministic_reorder(params::number_of_reorders);
  }
  if (params::random_reorder) {
    random_reorder();
  }
  if (params::random_reorder_literals) {
    random_reorder_literals();
  }
  pair<bool, size_t> start_clause = matrix.find_start();
  /*
  * If the initial clauses don't have a positive and a negative
  * clause then the problem is trivial.
  */
  if (!start_clause.first) {
    return ProverOutcome::False;
  }
  /*
  * Deal with the possible ways to set up start clause(s) according to
  * the options. Keep track of which start clauses are in use, and if
  * necessary what outcomes for them have been seen so far.
  */
  set_up_start_clauses();
  /*
  * Main loop for iterative deepening search.
  */
  bool switched_to_complete = false;
  for (current_depth_limit = params::start_depth;
       current_depth_limit <= params::depth_limit;
       current_depth_limit += params::depth_increment) {
    /*
    * See if the parameters dictate that it's time to convert to 
    * a complete search.
    */
    if (current_depth_limit >= params::switch_to_complete
        && !switched_to_complete) {
      params::set_complete_parameters();
      /*
      * You may have changed some parameters, so make sure all relevant 
      * start clauses now get tried.
      */
      set_up_start_clauses();
      current_depth_limit = params::start_depth;
      switched_to_complete = true;
      colour_string::ColourString cs(params::use_colours);
      show.nl(1);
      show(1, cs("Switching to complete search.").orange(), true);
    }
    show.nl(1);
    show(1, string("SEARCH TO DEPTH: "));
    show(1, std::to_string(current_depth_limit), true);
    /*
    * Generate each possible start move, and try to prove from
    * it.
    */
    size_t start_clause_index = 0;
    for (const Clause& C : matrix) {
      /* 
      * Find the next start clause.
      */
      if (results[start_clause_index] == StartClauseStatus::NoStart
          || results[start_clause_index] == StartClauseStatus::False) {
        start_clause_index++;
        continue;
      }
      /*
      * Reset everything to use the current start clause.
      *
      * TODO: this is slightly messy at present because 
      * the var_index doesn't necessarily get reset in the 
      * most efficient way possible if a previous schedule 
      * attempt timed out. (You'd need to go back down 
      * the stack and backtrack it as necessary.) This is 
      * of course irrelevant 
      * because it just means you might not get full re-use of
      * new variable names, but all the same it would be nice 
      * to fix.
      */
      var_index.add_backtrack_point();
      new_C = C.make_copy_with_new_vars(var_index, term_index);
      reset_for_start();
      /* 
      * Say what's going on.
      */
      show(1, string("START from clause "));
      show(1, std::to_string(start_clause_index + 1));
      show(1, string(" of "));
      show(1, std::to_string(matrix.get_num_clauses()));
      show(2, string(": "));
      show(2, new_C.to_string(), true);
      cout.flush();
      /*
      * Set up the initial stack item containing the start clause, and 
      * populate it.
      */
      StackItem start_item(StackItemType::Start, new_C, path, lemmata, 1);
      start_item.set_this_action(InferenceItem(InferenceItemType::Start, start_clause_index));
      stack.push_back(start_item);
      si = &stack.back();
      populate_stack_item();
      /*
      * Start with depth 1, as this makes sense when reading output if you're
      * using depth of recursion or path length.
      */
      current_depth = 1;
      /*
      * Liftoff!!!
      */
      ProverResult result = go();
      /*
      * Dealing with the outcome takes some care and depends on 
      * the parameters being used.
      */
      switch (result) {
        case ProverResult::Valid:
          proof_count++;
          if (params::build_proof) {
            if (params::generate_LaTeX_proof) {
              proof_printer.make_LaTeX(params::LaTeX_proof_path,
                                       problem_path,
                                       matrix.make_LaTeX());
            }
            if (params::generate_Prolog_proof) {
              fs::path prolog_path = params::Prolog_proof_path;
              proof_printer.make_Prolog(prolog_path);
            }
          }
          show(1, string(": Found proof number "));
          show(1, std::to_string(proof_count), true);
          return ProverOutcome::Valid;
          break;
        case ProverResult::Error:
          return ProverOutcome::Error;
          break;
        case ProverResult::TimeOut:
          return ProverOutcome::TimeOut;
          break;
        case ProverResult::OptionsExhausted:
          /*
          * If you ran out of options because you reached the depth
          * limit then you still need to continue.
          */
          if (depth_limit_reached) {
            show(1, string(": Depth limited"), true);
          }
          /*
          * If you ran out of options without reaching the depth limit, then
          * what you do depends on whether or not the search is complete.
          */
          else {
            if (params::search_is_complete()) {
              results[start_clause_index] = StartClauseStatus::False;
              show(1, string(": False"), true);
            }
          }
          start_clause_index++;
          break;
        default:
          return ProverOutcome::Error;
          break;
      }
      /*
      * This is necessary. Yes, I've checked. Think about it: you need 
      * one extra backtrack to undo the new variables generated when you 
      * make a start clause.
      */
      var_index.backtrack();
    }
    /*
    * Loop for start moves ends here.
    *
    * If everything was False then the theorem is False, otherwise
    * at least one attempt was depth-limited.
    */
    bool all_false = true;
    for (StartClauseStatus& outcome : results) {
      if (outcome == StartClauseStatus::Start) {
        all_false = false;
        break;
      }
    }
    if (all_false)
      return ProverOutcome::False;
  }
  /*
  * Iterative deepening loop ends here.
  */
  return ProverOutcome::PathLenLimit;
}
//----------------------------------------------------------------------
vector<pair<string, vector<size_t>>> StackProver::get_internal_proof() const {
  return proof_printer.make_internal();
}
//----------------------------------------------------------------------
void StackProver::show_stack() {
  cout << "--------------------------------------------------------" << endl;
  cout << "Stack:" << endl;
  cout << "--------------------------------------------------------" << endl;
  for (auto s : stack) {
    cout << s << endl;
  }
  cout << "--------------------------------------------------------" << endl;
}
//----------------------------------------------------------------------
void StackProver::show_right_stack() {
  cout << "--------------------------------------------------------" << endl;
  cout << "Right Stack:" << endl;
  cout << "--------------------------------------------------------" << endl;
  for (auto s : right_branch_stack) {
    cout << s << endl;
  }
  cout << "--------------------------------------------------------" << endl;
}
//----------------------------------------------------------------------
void StackProver::show_statistics() const {
  verbose_print::VPrint show(params::verbosity);
  show(1, string("Reductions: "));
  show(1, std::to_string(reductions_tried));
  show(1, string(" Extensions: "));
  show(1, std::to_string(extensions_tried));
  show(1, string(" Lemmata: "));
  show(1, std::to_string(lemmata_tried));
  show(1, string(" Right branches: "));
  show(1, std::to_string(right_branches_started), true);
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const StackProver& p) {
    out << "Current state of the RecursiveProver object" << endl;
    out << "-------------------------------------------" << endl << endl;
    out << p.var_index << endl;
    out << p.fun_index << endl;
    out << p.term_index << endl;
    out << p.path << endl;
    out << p.matrix << endl;
    return out;
}
