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

#include "InferenceItem.hpp"

//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const InferenceItemType& inf) {
  switch (inf) {
    case InferenceItemType::Start:
      out << "Start inference";
      break;
    case InferenceItemType::Reduction:
      out << "Reduction inference";
      break;
    case InferenceItemType::Extension:
      out << "Extension inference";
      break;
    case InferenceItemType::Axiom:
      out << "Axiom inference";
      break;
    case InferenceItemType::Lemma:
      out << "Lemma inference";
      break;
    default:
      break;
  }
  return out;
}
//----------------------------------------------------------------------
InferenceItem::InferenceItem()
: T(InferenceItemType::None)
, L()
, Lindex(0)
, C_2(0)
, Lprime(0)
, sigma()
, index_in_path(0)
, index_in_lemmata(0)
{}
//----------------------------------------------------------------------
InferenceItem::InferenceItem(
  InferenceItemType _T)
: T(_T)
, L()
, Lindex(0)
, C_2(0)
, Lprime(0)
, sigma()
, index_in_path(0)
, index_in_lemmata(0)
{}
//----------------------------------------------------------------------
InferenceItem::InferenceItem
(InferenceItemType _T, 
ClauseNum _C_2)
: T(_T)
, L()
, Lindex(0)
, C_2(_C_2)
, Lprime(0)
, sigma()
, index_in_path(0)
, index_in_lemmata(0)
{}
//----------------------------------------------------------------------
InferenceItem::InferenceItem(
  InferenceItemType _T, 
  const Literal& _L, 
  LitNum _Lindex)
: T(_T)
, L(_L)
, Lindex(_Lindex)
, C_2(0)
, Lprime(0)
, sigma()
, index_in_path(0)
, index_in_lemmata(0)
{}
//----------------------------------------------------------------------
InferenceItem::InferenceItem(
  InferenceItemType _T, 
  const Literal& _L, 
  LitNum _Lindex,
  size_t _index_in_lemmata)
: T(_T)
, L(_L)
, Lindex(_Lindex)
, C_2(0)
, Lprime(0)
, sigma()
, index_in_path(0)
, index_in_lemmata(_index_in_lemmata)
{}
//----------------------------------------------------------------------
InferenceItem::InferenceItem(
  InferenceItemType _T, 
  const Literal& _L, 
  LitNum _Lindex,
  ClauseNum _C_2, 
  LitNum _LPrime, 
  const Substitution& _sigma)
: T(_T)
, L(_L)
, Lindex(_Lindex)
, C_2(_C_2)
, Lprime(_LPrime)
, sigma(_sigma)
, index_in_path(0)
, index_in_lemmata(0)
{}
//----------------------------------------------------------------------
InferenceItem::InferenceItem(
  InferenceItemType _T, 
  const Literal& _L, 
  LitNum _Lindex,
  ClauseNum _C_2, 
  LitNum _LPrime, 
  const Substitution& _sigma, 
  size_t _index_in_path)
: T(_T)
, L(_L)
, Lindex(_Lindex)
, C_2(_C_2)
, Lprime(_LPrime)
, sigma(_sigma)
, index_in_path(_index_in_path)
, index_in_lemmata(0)
{}
//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const InferenceItem& si) {
    out << "Inference Item: ";
    switch (si.T) {
      case InferenceItemType::Start:
        out << "Start: clause number = "
            << to_string(si.C_2);
        break;
      case InferenceItemType::Reduction:
        out << "Reduction: L = " << si.L << " index = "
            << to_string(si.Lindex);
        out << " Substitution: " << si.sigma;
        break;
      case InferenceItemType::Extension:
        out << "Extension: L = " << si.L << " C_2 = "
            << to_string(si.C_2)
            << " L' = " << to_string(si.Lprime);
        out << " Substitution: " << si.sigma;
        break;
      case InferenceItemType::Axiom:
        out << "Axiom";
        break;
      case InferenceItemType::Lemma:
        out << "Lemma: L = " << si.L << " index = "
            << to_string(si.Lindex);
        break;
      default:
        break;
    };
    return out;
}
