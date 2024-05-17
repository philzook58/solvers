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

#include "ProofPrinter.hpp"

void show_internal_proof(const ProofType& proof) {
  size_t i = 0;
  for (const ProofLine& line : proof) {
    cout << "Proof step " << i << ": ";
    cout << line.first << " (";
    for (size_t n : line.second) {
      cout << " " << n;
    }
    cout << " )" << endl;
    i++;
   }
}
//---------------------------------------------------------------------
string ProofPrinter::make_LaTeX_state(StackItem* item_p) const {
  string s;
  s += "{";
  s += (item_p->c).make_LaTeX(params::sub_LaTeX_proof);
  s += ", \\textcolor{magenta}{M}, ";
  s += (item_p->p).make_LaTeX(params::sub_LaTeX_proof);
  s += ", ";
  s += (item_p->l).make_LaTeX(params::sub_LaTeX_proof);
  s += "}\n";
  return s;
}
//---------------------------------------------------------------------
string ProofPrinter::make_LaTeX_subtree(StackItem* item_p) const {
  string s;
  string axiom_s("\\prfbyaxiom{Axiom}");
  StackItem* next_p = item_p + 1;
  StackItem* right_item_p;
  switch (item_p->item_type) {
    case StackItemType::Start:
      s += make_LaTeX_subtree(next_p);
      s += make_LaTeX_state(item_p);
      break;
    case StackItemType::Lemmata:
      s += "\\prftree[r]{Lem}{";
      if ((item_p->c).size() == 0)
        s += axiom_s;
      else
        s += make_LaTeX_subtree(next_p);
      s += make_LaTeX_state(item_p);
      s += "}";
      break;
    case StackItemType::Reduction:
      s += "\\prftree[r,l]{Red}{$";
      s += (item_p->sub).make_LaTeX(params::sub_LaTeX_proof);
      s += "$}{";
      if ((item_p->c).size() == 0)
        s += axiom_s;
      else
        s += make_LaTeX_subtree(next_p);
      s += make_LaTeX_state(item_p);
      s += "}";
      break;
    case StackItemType::LeftBranch:
      s += "\\prftree[r,l]{Ext}{$";
      s += (item_p->sub).make_LaTeX(params::sub_LaTeX_proof);
      s += "$}{";
      if ((item_p->c).size() == 0)
        s += axiom_s;
      else
        s += make_LaTeX_subtree(next_p);
      s += make_LaTeX_state(item_p);
      s += "}{";
      /*
      * You need to find the right subtree, which is the only thing at
      * the same depth as you currently are.
      */
      right_item_p = item_p + 1;
      while (right_item_p->depth != item_p->depth)
        right_item_p++;
      s += make_LaTeX_subtree(right_item_p);
      s += "}";
      break;
    case StackItemType::RightBranch:
      if ((item_p->c).size() == 0)
        s += axiom_s;
      else
        s += make_LaTeX_subtree(next_p);
      s += make_LaTeX_state(item_p);
      break;
    default:
      cerr << "Something is really wrong..." << endl;
      break;
  }
  return s;
}
//---------------------------------------------------------------------
void ProofPrinter::make_LaTeX(const path& path_to_file,
                       const path& path_to_input_file,
                       const string& matrix_as_latex) {
  std::ofstream file(path_to_file);

  // Get the contents of the LaTeX header and transfer into the
  // output file.
  /*
  std::ifstream latex_header_file(params::latex_header_file);
  string line;
  while (!latex_header_file.eof()) {
    std::getline(latex_header_file, line);
    file << line << endl;
  }
  latex_header_file.close();
  */
  file << "\\documentclass[10pt]{article}" << '\n';
  file << "\\usepackage{libertine}" << '\n';
  file << "\\usepackage{amsmath,amsfonts,amssymb}" << '\n';
  file << "\\usepackage{prftree}" << '\n';
  file << "\\usepackage{color}" << '\n';
  file << "\\usepackage[paperwidth = 750mm, paperheight = 1500mm,landscape]{geometry}" << '\n' << '\n';
  file << "\\begin{document}" << '\n';

  // Add details of the problem.
  file << "\\noindent\\begin{LARGE}\\textsc{Connect++}\\end{LARGE} \\\\" << endl << endl;
  file << "\\noindent Attempting to prove problem from file: ";
  file << "$\\mathtt{";
  file << latex_escape_characters(path_to_input_file.filename());
  file << "}$ \\\\" << endl << endl;
  if (params::latex_include_matrix) {
    file << "\\noindent Problem has matrix: " << endl << endl;
    file << matrix_as_latex << endl;
  }
  file << "\\noindent\\textsc{Proof}: \\\\" << endl << endl;

  if (params::latex_tiny_proof)
    file << "\\begin{tiny}" << endl;

  file << "\\[";

  /*
  *  Build a LaTeX representation of the Proof.
  */
  if (p != nullptr) {
    /*
    * Start move.
    */
    file << "\\prftree[r]{Start}{";
    file << make_LaTeX_subtree(&((*p)[0]));
    file << "}{\\epsilon, \\textcolor{magenta}{M}, \\epsilon, \\epsilon}\n";
  }

  file << "\\]";

  if (params::latex_tiny_proof)
    file << "\\end{tiny}" << endl;

  // Finish off the LaTeX file.
  /*
  std::ifstream latex_footer_file(params::latex_footer_file);
  while (!latex_footer_file.eof()) {
    std::getline(latex_footer_file, line);
    file << line << '\n';
  }
  latex_footer_file.close();
  */
  file << '\n' << '\n' << "\\end{document}" << '\n';

  file.close();

}
//---------------------------------------------------------------------
void ProofPrinter::make_Prolog(const path& path_to_file) {
  std::ofstream file(path_to_file);
  file << "proof_stack([" << std::endl;
  size_t s = p->size() - 1;
  size_t i = 0;
  for (const StackItem& si : *p) {
    switch (si.item_type) {
      case StackItemType::Start:
        file << "start(";
        file << std::to_string(si.this_action.C_2);
        file << ")";
        break;
      case StackItemType::Axiom:
        file << "axiom()";
        break;
      case StackItemType::Reduction:
        file << "reduction(";
        file << std::to_string(si.this_action.Lindex);
        file << ", ";
        file << std::to_string(si.this_action.index_in_path);
        file << ")";
        break;
      case StackItemType::LeftBranch:
        file << "left_branch(";
        file << std::to_string(si.this_action.Lindex);
        file << ", ";
        file << std::to_string(si.this_action.C_2);
        file << ", ";
        file << std::to_string(si.this_action.Lprime);
        file << ", ";
        file << std::to_string(si.depth);
        file << ")";
        break;
      case StackItemType::RightBranch:
        file << "right_branch(";
        file << std::to_string(si.depth);
        file << ")";
        break;
      case StackItemType::Lemmata:
        file << "lemmata(";
        file << std::to_string(si.this_action.Lindex);
        file << ", ";
        file << std::to_string(si.this_action.index_in_lemmata);
        file << ")";
        break;
      default:
        cerr << "Something is really wrong..." << endl;
        break;
    }
    if (i < s)
      file << ", ";
    file << std::endl;
    i++;
  }
  file << "])." << std::endl;
  file.close();
}
//---------------------------------------------------------------------
void ProofPrinter::show_Prolog() {
  cout << "proof_stack([" << std::endl;
  size_t s = p->size() - 1;
  size_t i = 0;
  for (const StackItem& si : *p) {
    switch (si.item_type) {
      case StackItemType::Start:
        cout<< "start(";
        cout << std::to_string(si.this_action.C_2);
        cout << ")";
        break;
      case StackItemType::Axiom:
        cout << "axiom()";
        break;
      case StackItemType::Reduction:
        cout << "reduction(";
        cout << std::to_string(si.this_action.Lindex);
        cout << ", ";
        cout << std::to_string(si.this_action.index_in_path);
        cout << ")";
        break;
      case StackItemType::LeftBranch:
        cout << "left_branch(";
        cout << std::to_string(si.this_action.Lindex);
        cout << ", ";
        cout << std::to_string(si.this_action.C_2);
        cout << ", ";
        cout << std::to_string(si.this_action.Lprime);
        cout << ", ";
        cout << std::to_string(si.depth);
        cout << ")";
        break;
      case StackItemType::RightBranch:
        cout << "right_branch(";
        cout << std::to_string(si.depth);
        cout << ")";
        break;
      case StackItemType::Lemmata:
        cout << "lemmata(";
        cout << std::to_string(si.this_action.Lindex);
        cout << ", ";
        cout << std::to_string(si.this_action.index_in_lemmata);
        cout << ")";
        break;
      default:
        cerr << "Something is really wrong..." << endl;
        break;
    }
    if (i < s)
      cout << ", ";
    cout << std::endl;
    i++;
  }
  cout << "])." << std::endl;
}
//---------------------------------------------------------------------
void ProofPrinter::show_tptp() {
  cout << "cnf(proof-stack, plain, " << std::endl;
  cout << "proof_stack(" << std::endl;
  size_t s = p->size() - 1;
  size_t i = 0;
  for (const StackItem& si : *p) {
    switch (si.item_type) {
      case StackItemType::Start:
        cout<< "start(";
        cout << std::to_string(si.this_action.C_2);
        cout << ")";
        break;
      case StackItemType::Axiom:
        cout << "axiom()";
        break;
      case StackItemType::Reduction:
        cout << "reduction(";
        cout << std::to_string(si.this_action.Lindex);
        cout << ", ";
        cout << std::to_string(si.this_action.index_in_path);
        cout << ")";
        break;
      case StackItemType::LeftBranch:
        cout << "left_branch(";
        cout << std::to_string(si.this_action.Lindex);
        cout << ", ";
        cout << std::to_string(si.this_action.C_2);
        cout << ", ";
        cout << std::to_string(si.this_action.Lprime);
        cout << ", ";
        cout << std::to_string(si.depth);
        cout << ")";
        break;
      case StackItemType::RightBranch:
        cout << "right_branch(";
        cout << std::to_string(si.depth);
        cout << ")";
        break;
      case StackItemType::Lemmata:
        cout << "lemmata(";
        cout << std::to_string(si.this_action.Lindex);
        cout << ", ";
        cout << std::to_string(si.this_action.index_in_lemmata);
        cout << ")";
        break;
      default:
        cerr << "Something is really wrong..." << endl;
        break;
    }
    if (i < s)
      cout << ", ";
    cout << std::endl;
    i++;
  }
  cout << "))." << std::endl;
}
//---------------------------------------------------------------------
  vector<pair<string, vector<size_t>>> ProofPrinter::make_internal() const {
  vector<pair<string, vector<size_t>>> out;

  size_t s = p->size() - 1;
  size_t i = 0;
  pair<string, vector<size_t>> next_out;
  for (const StackItem& si : *p) {
    next_out.second.clear();
    switch (si.item_type) {
      case StackItemType::Start:
        next_out.first = "start";
        next_out.second.push_back(si.this_action.C_2);
        out.push_back(next_out);
        break;
      case StackItemType::Axiom:
        next_out.first = "axiom";
        out.push_back(next_out);
        break;
      case StackItemType::Reduction:
        next_out.first = "reduction";
        next_out.second.push_back(si.this_action.Lindex);
        next_out.second.push_back(si.this_action.index_in_path);
        out.push_back(next_out);
        break;
      case StackItemType::LeftBranch:
        next_out.first = "left_branch";
        next_out.second.push_back(si.this_action.Lindex);
        next_out.second.push_back(si.this_action.C_2);
        next_out.second.push_back(si.this_action.Lprime);
        next_out.second.push_back(si.depth);
        out.push_back(next_out);
        break;
      case StackItemType::RightBranch:
        next_out.first = "right_branch";
        next_out.second.push_back(si.depth);
        out.push_back(next_out);
        break;
      case StackItemType::Lemmata:
        next_out.first = "lemmata";
        next_out.second.push_back(si.this_action.Lindex);
        next_out.second.push_back(si.this_action.index_in_lemmata);
        out.push_back(next_out);
        break;
      default:
        cerr << "Something is really wrong..." << endl;
        break;
    }
  }
  return out;
}