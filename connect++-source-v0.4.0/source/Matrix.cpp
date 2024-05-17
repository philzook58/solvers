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

#include "Matrix.hpp"

std::mt19937 Matrix::d(params::random_seed);

//----------------------------------------------------------------------
Matrix::Matrix(size_t num_predicates)
: clauses()
, index((num_predicates * 2), vector<MatrixPairType>())
, positive_clauses()
, negative_clauses()
, clause_roles()
, num_equals(0)
, clauses_copy()
, roles_copy()
, copy_saved(false)
{}
//----------------------------------------------------------------------
void Matrix::set_num_preds(size_t num_predicates) {
    index = vector<vector<MatrixPairType> >((num_predicates * 2), vector<MatrixPairType>());
}
//----------------------------------------------------------------------
bool Matrix::is_conjecture(size_t i) const {
  return clause_roles[i] == "negated_conjecture" ||
         clause_roles[i] == "conjecture";
}
//----------------------------------------------------------------------
pair<bool,size_t> Matrix::find_start() const {
  bool found_positive = false;
  bool found_negative = false;
  size_t first_positive = 0;
  size_t first_negative = 0;
  bool found_candidate = false;
  size_t candidate = 0;
  size_t i = 0;
  for (bool positive : positive_clauses) {
    if (positive_clauses[i]) {
      if (!found_positive) {
        first_positive = i;
        found_positive = true;
      }
    }
    if (negative_clauses[i]) {
      if (!found_negative) {
        first_negative = i;
        found_negative = true;
      }
    }
    if (is_conjecture(i) && !found_candidate) {
      if ((params::positive_representation && positive_clauses[i]) ||
         (!params::positive_representation && negative_clauses[i])) {
            found_candidate = true;
            candidate = i;
      }
    }
    i++;
  }
  if (!(found_positive && found_negative))
    return pair<bool,size_t>(false, 0);
  if (found_candidate)
    return pair<bool, size_t>(true, candidate);
  else if (params::positive_representation)
    return pair<bool, size_t>(true, first_positive);
  else
    return pair<bool, size_t>(true, first_negative);
}
//----------------------------------------------------------------------
void Matrix::add_clause(Clause& clause, string role) {
    ClauseNum clause_number = clauses.size();
    LitNum literal_number = 0;
    for (size_t j = 0; j < clause.size(); j++) {
        size_t i = clause[j].get_pred_as_index();
        index[i].push_back(MatrixPairType(clause_number, literal_number));
        literal_number++;
    }
    clauses.push_back(clause);
    positive_clauses.push_back(clause.is_positive());
    negative_clauses.push_back(clause.is_negative());
    clause_roles.push_back(role);
}
//----------------------------------------------------------------------
void Matrix::deterministic_reorder(size_t n) {
  /**
  * Only store a copy of the clauses the first time you do this.
  */
  if (!copy_saved) {
    copy_saved = true;
    make_clauses_copy();
  }
  /*
  * Find a suitably reordered set of indices.
  */
  vector<uint32_t> new_order;
  size_t s = clauses.size();
  for (size_t i = 0; i < s; i++)
    new_order.push_back(i);
  new_order = deterministic_reorder_n_times<uint32_t>(new_order, n);
  /*
  * Clear and rebuild as necessary.
  */
  clauses.clear();
  positive_clauses.clear();
  negative_clauses.clear();
  clause_roles.clear();
  size_t s2 = index.size();
  index.clear();
  index = vector<vector<MatrixPairType> >(s2, vector<MatrixPairType>());
  for (size_t i = 0; i < s; i++) {
    add_clause(clauses_copy[new_order[i]], roles_copy[new_order[i]]);
  }
}
//----------------------------------------------------------------------
void Matrix::random_reorder() {
  vector<Clause> saved_clauses(clauses);
  vector<string> saved_clause_roles(clause_roles);
  /*
  * Find a suitably reordered set of indices.
  */
  vector<uint32_t> new_order;
  size_t s = clauses.size();
  for (size_t i = 0; i < s; i++)
    new_order.push_back(i);
  std::shuffle(new_order.begin(), new_order.end(), d);
  /*
  * Clear and rebuild as necessary.
  */
  clauses.clear();
  positive_clauses.clear();
  negative_clauses.clear();
  clause_roles.clear();
  size_t s2 = index.size();
  index.clear();
  index = vector<vector<MatrixPairType> >(s2, vector<MatrixPairType>());
  for (size_t i = 0; i < s; i++) {
    add_clause(saved_clauses[new_order[i]], saved_clause_roles[new_order[i]]);
  }
}
//----------------------------------------------------------------------
void Matrix::random_reorder_literals() {
  vector<Clause> saved_clauses(clauses);
  vector<string> saved_clause_roles(clause_roles);
  size_t s = clauses.size();
  /*
  * Clear and rebuild as necessary, reordering as you go.
  */
  clauses.clear();
  positive_clauses.clear();
  negative_clauses.clear();
  clause_roles.clear();
  size_t s2 = index.size();
  index.clear();
  index = vector<vector<MatrixPairType> >(s2, vector<MatrixPairType>());
  for (size_t i = 0; i < s; i++) {
    Clause c(saved_clauses[i]);
    c.random_reorder();
    add_clause(c, saved_clause_roles[i]);
  }
}
//----------------------------------------------------------------------
void Matrix::move_equals_to_start() {
  if (num_equals == 0) {
    cerr << "Why are you trying to move equality axioms - there aren't any?" << endl;
    return;
  }
  make_clauses_copy();
  clauses.clear();
  positive_clauses.clear();
  negative_clauses.clear();
  clause_roles.clear();
  size_t s2 = index.size();
  index.clear();
  index = vector<vector<MatrixPairType> >(s2, vector<MatrixPairType>());
  size_t n_clauses = clauses_copy.size();
  for (size_t i = n_clauses - num_equals; i < n_clauses; i++) {
    add_clause(clauses_copy[i], roles_copy[i]);
  }
  for (size_t i = 0; i < n_clauses - num_equals; i++) {
    add_clause(clauses_copy[i], roles_copy[i]);
  }
  clauses_copy.clear();
  roles_copy.clear();
}
//----------------------------------------------------------------------
void Matrix::find_extensions(Unifier& u, vector<InferenceItem>& result,
                             const Literal& lit, LitNum ind,
                             VariableIndex& var_index, TermIndex& term_index) {
    Literal neg_lit(lit);
    neg_lit.invert();
    size_t i = neg_lit.get_pred_as_index();
    for (const MatrixPairType& p : index[i]) {
        ClauseNum c_num = p.first;
        LitNum l_num = p.second;
        var_index.add_backtrack_point();
        Clause new_c = (clauses[c_num]).make_copy_with_new_vars(var_index, term_index);
        UnificationOutcome outcome = u(neg_lit, new_c[l_num]);
        if (outcome == UnificationOutcome::Succeed) {
            result.push_back(InferenceItem(InferenceItemType::Extension, lit, ind,
                            c_num, l_num, u.get_substitution()));
        }
        var_index.backtrack();
        u.backtrack();
    }
}
//----------------------------------------------------------------------
void Matrix::find_limited_extensions(Unifier& u, vector<InferenceItem>& result,
                         Clause& c, VariableIndex& var_index,
                         TermIndex& term_index) {
  if (c.size() == 0) {
    cerr << "You shouldn't be looking for extensions with an empty clause" << endl;
    return;
  }
  find_extensions(u, result, c[0], 0, var_index, term_index);
}
//----------------------------------------------------------------------
void Matrix::find_all_extensions(Unifier& u, vector<InferenceItem>& result,
                         Clause& c, VariableIndex& var_index,
                         TermIndex& term_index) {
  if (c.size() == 0) {
    cerr << "You shouldn't be looking for extensions with an empty clause" << endl;
    return;
  }
  for (size_t index = 0; index < c.size(); index++) {
      find_extensions(u, result, c[index], index, var_index, term_index);
  }
}
//----------------------------------------------------------------------
string Matrix::to_string() const {
  string result;
  colour_string::ColourString cs(params::use_colours);
  size_t i = 0;
  for (const Clause& c : clauses) {
    if (is_conjecture(i))
      result += cs("*").orange();
    else
      result += " ";
    if (positive_clauses[i])
      result += cs("+").orange();
    else if (negative_clauses[i])
      result += cs("-").orange();
    else
      result += " ";
    result += " ";
    i++;
    result += c.to_string();
    result += "\n";
  }
  return result;
}
//----------------------------------------------------------------------
string Matrix::make_LaTeX(bool subbed) const {
  string s ("\\[\n\\begin{split}\n");
  s += "\\textcolor{magenta}{M} = ";
  for (const Clause& c : clauses) {
    s += "&\\,";
    s += c.make_LaTeX(subbed);
    s += "\\\\";
  }
  s += "\n\\end{split}\n\\]\n";

  return s;
}
//----------------------------------------------------------------------
void Matrix::write_to_prolog_file(const path& path_to_file) const {
  std::ofstream file(path_to_file);
  size_t matrix_i = 0;
  // Nasty hack needed to stop the proof checker from printing 
  // a bunch of warnings when reading the matrix.
  file << ":- style_check(-singleton)." << std::endl;
  for (const Clause& c : clauses) {
    file << "matrix(";
    file << std::to_string(matrix_i++);
    file << ", ";
    file << c.to_prolog_string();
    file << ").";
    file << std::endl;
  }
  file.close();
}
//----------------------------------------------------------------------
void Matrix::show_tptp() const {
  size_t matrix_i = 0;
  for (const Clause& c : clauses) {
    cout << "cnf(matrix-";
    cout << std::to_string(matrix_i++);
    cout << ", plain, ";
    cout << c.to_tptp_string();
    cout << ").";
    cout << std::endl;
  }
}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const Matrix& m) {
    out << "Clauses in matrix:" << endl;
    out << "------------------" << endl;
    size_t i = 0;
    for (const Clause& c : m.clauses)
        out << setw(params::output_width) << i++
        << ": " << c << endl;
    vector<string> index_lits(m.index.size(), string(""));
    for (Clause c : m.clauses)
      for (size_t i = 0; i < c.size(); i++)
        index_lits[c[i].get_pred_as_index()] = c[i].get_small_lit();
    i = 0;
    out << endl << "Index: (Clause, Literal):" << endl;
    out <<         "-------------------------" << endl;
    for (vector<MatrixPairType> v : m.index) {
        out << setw(params::output_width + 20) << index_lits[i++] << ": ";
        for (MatrixPairType p : v) {
            out << "(" << p.first << ", " << p.second << ") ";
        }
        out << endl;
    }
    return out;
}

