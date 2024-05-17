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

#ifndef STACKITEM_HPP
#define STACKITEM_HPP

#include<iostream>

#include "SimplePath.hpp"
#include "Lemmata.hpp"

using std::ostream;

/**
* \brief Enumeration for the different kinds of stack item.
*
* You need to be able to identify them in this way to correctly 
* control backtracking.
*/
enum class StackItemType {
  Start, Axiom, Reduction, LeftBranch, RightBranch, Lemmata
};

ostream& operator<<(ostream&, const StackItemType&);

/**
* \brief Stack items: each contains its own stack of possible next 
*        inferences.
*/
struct StackItem {
  /**
  * \brief What type of StackItem is this?
  */
  StackItemType item_type;
  /**
  * \brief Each node in the proof tree is a tuple of clause, 
  *        matrix, path, lemmata: this is the clause.
  */
  Clause c;
  /**
  * \brief Each node in the proof tree is a tuple of clause, 
  *        matrix, path, lemmata: this is the path.
  */
  SimplePath p;
  /**
  * \brief Each node in the proof tree is a tuple of clause, 
  *        matrix, path, lemmata: this is the lemmata.
  */
  Lemmata l;
  /**
  * \brief Some nodes in the proof tree have an associated 
  *        substitution.
  */
  Substitution sub;
  /**
  * \brief Actions available to try.
  *
  * These are all the actions that can be used to extend the proof 
  * further from this point onward. They are tried in order. 
  * Reordering here is an obvious approach to making a heuristic, and 
  * deletion corresponds to restriction of backtracking. 
  */
  vector<InferenceItem> actions;
  /**
  * \brief How deep in the proof tree are we?
  */
  uint32_t depth;
  /**
  * \brief Action that got you to this clause, path etc.
  */
  InferenceItem this_action;
  /**
  * \brief Pointer that allows a right branch to know 
  * where to delete alternatives for restricted backtracking.
  *
  * DO NOT try to do this by storing a pointer to the StackItem. 
  * As the vector can have its storage reallocated in the 
  * background, you end up with all manner of segfaultyness.
  */
  size_t bt_restriction_index;
  //----------------------------------------------------------------------
  // Many constructors - mostly you're just using StackItems as 
  // storage and there isn't much to do with the contents.
  //----------------------------------------------------------------------
  StackItem() = delete;
  StackItem(StackItemType sit)
  : item_type(sit)
  , c()
  , p()
  , l()
  , sub()
  , actions()
  , depth(0)
  , this_action()
  , bt_restriction_index(0)
  {};
  StackItem(StackItemType sit, const Clause& _c, const SimplePath& _p)
  : item_type(sit)
  , c(_c)
  , p(_p)
  , l()
  , sub()
  , actions()
  , depth(0)
  , this_action()
  , bt_restriction_index(0)
  {};
  StackItem(StackItemType sit, const Clause& _c, const SimplePath& _p, const Lemmata& _l)
  : item_type(sit)
  , c(_c)
  , p(_p)
  , l(_l)
  , sub()
  , actions()
  , depth(0)
  , this_action()
  , bt_restriction_index(0)
  {};
  StackItem(StackItemType sit, const Clause& _c, const SimplePath& _p, uint32_t _d)
  : item_type(sit)
  , c(_c)
  , p(_p)
  , l()
  , sub()
  , actions()
  , depth(_d)
  , this_action()
  , bt_restriction_index(0)
  {};
  StackItem(StackItemType sit,
    const Clause& _c,
    const SimplePath& _p,
    const Lemmata& _l,
    uint32_t _d)
  : item_type(sit)
  , c(_c)
  , p(_p)
  , l(_l)
  , sub()
  , actions()
  , depth(_d)
  , this_action()
  , bt_restriction_index(0)
  {};
  StackItem(StackItemType sit, const Clause& _c, const SimplePath& _p,
            const Substitution& _sub , uint32_t _d)
  : item_type(sit)
  , c(_c)
  , p(_p)
  , l()
  , sub(_sub)
  , actions()
  , depth(_d)
  , this_action()
  , bt_restriction_index(0)
  {};
  StackItem(StackItemType sit, const Clause& _c, const SimplePath& _p, const Lemmata& _l,
            const Substitution& _sub , uint32_t _d)
  : item_type(sit)
  , c(_c)
  , p(_p)
  , l(_l)
  , sub(_sub)
  , actions()
  , depth(_d)
  , this_action()
  , bt_restriction_index(0)
  {};
  /**
  * \brief Adjust the collection of actions to limit backtracking.
  *
  * Of course, you might want to modify how this works if you 
  * want to do something more sophisticated. At present you 
  * have either the leanCop style, or the most aggressive style 
  * possible.
  */
  void restrict_backtrack();
  /**
  * \brief Make a string representation.
  */
  string to_string_unsubbed() const;
  /**
  * \brief Delete all the remaining possible actions.
  *
  * Possibly the most aggressive backtracking restriction heuristic 
  * available.
  */
  void clear() { actions.clear(); }
  /**
  * \brief Basic set method.
  */
  inline void set_this_action(const InferenceItem& inf_i) {
    this_action = inf_i;
  }
  /**
  * \brief Basic set method.
  */
  inline void set_bt_restriction_index(size_t i) {
    bt_restriction_index = i;
  }
};

ostream& operator<<(ostream&, const StackItem&);

#endif
