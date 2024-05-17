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

#ifndef LEMMATA_HPP
#define LEMMATA_HPP

#include <iostream>
#include <vector>

#include "Clause.hpp"
#include "InferenceItem.hpp"

using std::vector;
using std::ostream;
using std::endl;
using std::cout;

/**
* \brief Representation of the lemma list. 
*
* This is mostly straightforward is it is just a vector of 
* Literals.
*
* However it does have two critical methods: find_all_lemmata and 
* find_initial_lemmata. You should probably read the documentation 
* for these. 
*/
class Lemmata {
private:
  /**
  * \brief Lemmata list as appearing in the connection calculus. 
  */
  vector<Literal> ls;
  size_t len;
public:
  /**
  * \brief You should not need any more complicated constructor.
  */
  Lemmata() : ls(), len(0) {}
  /**
  * \brief Self-explanatory.
  *
  * @param l Reference to Literal to add 
  */
  void push_back(const Literal&);
  /**
  * \brief Self-explanatory.
  */
  void clear() { ls.clear(); len = 0; }
  /**
  * \brief Find all lemmata that are applicable, given a Clause.
  *
  * The connection calculus allows this, but there is a 
  * question of how you implement it. I suspect, but am 
  * not 100% certain, that leanCop only looks at the 
  * first Literal in the Clause, whereas this looks at 
  * all Literals in the Clause. For the (suspected) 
  * leanCop behavious use find_initial_lemmata.
  *
  * In Connect++ the parameter params::all_lemmata controls 
  * this and is false by default.
  *
  * @param inf Reference to a vector of InferenceItem
  * @param c Reference to a Clause
  */
  void find_all_lemmata(vector<InferenceItem>&, Clause&);
  /**
  * \brief Find all lemmata that are applicable, but only for 
  * the initial Literal in a Clause.
  *
  * See also the documentation for find_all_lemmata.
  *
  * @param inf Reference to a vector of InferenceItem
  * @param c Reference to a Clause
  */
  void find_initial_lemmata(vector<InferenceItem>&, Clause&);
  /**
  * \brief Convert to a string.
  *
  * @param subbed Implement substitutions if true.
  */
  string to_string(bool = false) const;
  /**
  * Convert to a LaTeX representation.
  *
 * @param subbed Implement substitutions if true.
  */
  string make_LaTeX(bool = false) const;

  friend ostream& operator<<(ostream&, const Lemmata&);
};

#endif
