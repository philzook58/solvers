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

#ifndef INFERENCEITEM_HPP
#define INFERENCEITEM_HPP

#include <iostream>

#include "Literal.hpp"
#include "Substitution.hpp"

using std::ostream;
using std::endl;

/**
* \brief Enumeration of the possible inferences.
*/
enum class InferenceItemType { 
          None, 
          Start, 
          Reduction, 
          Extension, 
          Axiom, 
          Lemma 
};

ostream& operator<<(ostream&, const InferenceItemType&);

/**
* \brief Full representation of inferences, beyond just the name.
*
* The nomenclature here deliberately mimics that used in many 
* of the publications describing the method, in an attempt to 
* maintain readability.
*
* As these are mostly used just to store information as the stack 
* representing the proof is built, the methods are mostly 
* just constructors.
*/
struct InferenceItem {
  /**
  *\brief What kind of inference is this?
  */
  InferenceItemType T;
  /**
  * \brief The Literal that is used to make the inference.
  */
  Literal L;
  /**
  * \brief The index of the literal within the clause being used.
  */
  LitNum Lindex;
  /**
  * \brief For extensions, the number of the clause for 
  *        which a fresh copy is being made.
  */
  ClauseNum C_2;
  /**
  * \brief The index of the literal in C_2 being used.
  */
  LitNum Lprime;
  /**
  * \brief A copy of the substitution that makes the rule 
  *        applicable.
  */
  Substitution sigma;
  /**
  * \brief The index in the path of the literal being usedd.
  */
  size_t index_in_path;
  /**
  * \brief For certification, you want to know which element of the lemmata 
  *        list was used when the Lemma rule was employed.
  */
  size_t index_in_lemmata;

  /**
  * \brief Constructor - probably unused.
  */
  InferenceItem();
  /**
  * \brief Constructor - probably unused.
  */
  InferenceItem(InferenceItemType);
  /**
  * \brief Constructor - probably unused.
  */
  InferenceItem(InferenceItemType, ClauseNum);
  /**
  * \brief Constructor - probably unused.
  */
  InferenceItem(InferenceItemType, const Literal&, LitNum);
  /**
  * \brief Constructor for lemmata. 
  *
  * The last parameter is for index_in_lemmata.
  */
  InferenceItem(InferenceItemType, const Literal&, LitNum, size_t);
  /**
  * \brief Constructor for extensions. 
  */
  InferenceItem(InferenceItemType, const Literal&, LitNum, 
      ClauseNum, LitNum, const Substitution&);
  /**
  * \brief Constructor for reductions.
  */
  InferenceItem(InferenceItemType, const Literal&, LitNum, 
      ClauseNum, LitNum, const Substitution&, size_t);
};

ostream& operator<<(ostream&, const InferenceItem&);

#endif
