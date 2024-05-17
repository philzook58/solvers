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

#ifndef PROVEROUTCOME_HPP
#define PROVEROUTCOME_HPP

#include<iostream>
#include<string>

using std::ostream;
using std::string;

/** 
* \brief A bunch of straightforward enumerations, typically for 
*        indicating outcomes.
*/

/**
* \brief OptionsExhausted is not the same as False
*        because the search may not be complete.
*/
enum class ProverResult {
  Valid,
  OptionsExhausted,
  TimeOut,
  Error
};
/**
* \brief StartClauseStatus is used to track how proof 
*        attempts on individual start clauses have turned out. 
*
* This is needed because what you then do with them depends 
* on whether or not the search parameters are
* complete. NoStart marks potential start clauses that are 
* never used.
*/
enum class StartClauseStatus {
  Start,
  NoStart,
  False
};
/**
* \brief ProverOutcome contains options for the ultimate 
* result of running a prover on a problem.
*/
enum class ProverOutcome {
  Valid,
  False,
  PathLenLimit,
  Error,
  TimeOut
};

string outcome_to_string(const ProverOutcome&);

ostream& operator<<(ostream&, const ProverOutcome&);

#endif
