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

#ifndef INTERVAL_HPP
#define INTERVAL_HPP

/**
* \brief Simple class to help you count intervals.
*
* There is a count and a limit. Each tick increases the 
* count, and returns true plus resets the count when you 
* reach the limit. (Otherwise returns false.)
*/
class Interval {
private:
  size_t count;
  size_t limit;
public:
  Interval() = delete;

  /**
  * Parameter sets the limit.
  */
  Interval(size_t l) : count(0), limit(0) {
    if (l >= 0)
      limit = l;
  }

  /**
  * Advance the count by one and indicate/reset when you reach the
  * limit.
  */
  bool tick() {
    count++;
    if (count > limit) {
      count = 0;
      return true;
    }
    return false;
  }
};

#endif