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

#ifndef SUBSTITUTIONSTACK_HPP
#define SUBSTITUTIONSTACK_HPP

#include<iostream>

#include "Substitution.hpp"

/**
* \brief As you build a proof you make substitutions that 
*        apply to the entire proof: if you backtrack during 
*        the search you need to remove the relevant substitutions. 
*
* This class implements a stack that takes a Substitution
* applying possibly to multiple variables, and applies it while 
* keeping track of backtracking information so that backtracking 
* while removing substitutions is a single method call.
*/
class SubstitutionStack {
private:
  /**
  *\brief Stack of pointers to Variables that have been 
  *       substituted.
  */
  vector<Variable*> stack;
  /**
  * \brief Indexes on the stack that can be backtracked to. 
  *       
  * When you backtrack you undo every substitution back to the 
  * most recent index.
  */
  vector<size_t> backtrack_points;
  /**
  * \brief Self-explanatory.
  */
  size_t next_index;
public:
  /**
  * \brief If you need a different initialization, you're 
  *        probably doing something wrong.
  */
  SubstitutionStack() : stack(), backtrack_points(), next_index(0) {}
  /**
  * \brief As usual, you really don't want to be messing with 
  *        this kind of thing, so let the compiler find 
  *        your errors.
  */
  SubstitutionStack(const SubstitutionStack&) = delete;
  SubstitutionStack& operator=(const SubstitutionStack&) = delete;
  /**
  * \brief Take all the substitutions provided and add the 
  *        corresponding variables to the stack. 
  *
  * Also save the starting point as a backtrack point.
  *
  * @param sub Reference to Substitution that has been applied.
  */
  void push_all(Substitution&);
  /**
  * \brief Remove variables from the stack, and remove 
  *        substitutions as you go, as far back as the 
  *        most recent backtrack point.
  */
  void backtrack();
  /**
  * \brief Reset everything. 
  */
  void clear() { stack.clear(); backtrack_points.clear(); next_index = 0; }

  friend ostream& operator<<(ostream&, const SubstitutionStack&);
};

#endif