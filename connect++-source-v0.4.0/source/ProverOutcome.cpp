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

#include "ProverOutcome.hpp"
//----------------------------------------------------------------------
string outcome_to_string(const ProverOutcome& po) {
  string result;
  switch (po) {
      case ProverOutcome::Valid:
          result = "Valid";
          break;
      case ProverOutcome::False:
          result = "False";
          break;
      case ProverOutcome::PathLenLimit:
          result = "Path length limit reached";
          break;
      case ProverOutcome::Error:
          result = "Error";
          break;
      case ProverOutcome::TimeOut:
          result = "Timeout";
          break;
      default:
          break;
  }
  return result;
}

//----------------------------------------------------------------------
ostream& operator<<(ostream& out, const ProverOutcome& po) {
    out << outcome_to_string(po);
    return out;
}
