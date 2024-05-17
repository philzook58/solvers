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

#ifndef REORDER_HPP
#define REORDER_HPP

#include<iostream>

using std::vector;
using std::cout;
using std::endl;

/**
* \brief Some Templates for reordering things. 
*
* These may not look like the most obvious ways of reordering. 
* The point is to have a deterministic re-ordering algorithm 
* equivalent to the one used by leanCoP2.0. Reorder clauses 
* but not literals within them.
*/
/**
* \brief Probably unused -- mainly for debugging.
*/
template<class T>
void show_vector(vector<T> v) {
  cout << "( ";
  for (T e : v)
   cout << e << " ";
  cout << ")" << endl;
}
/**
* \brief Used by deterministic_reorder(). Does what the name 
*        says.
*/
template<class T>
vector<T> three_way_merge(vector<T> v1,
                     vector<T> v2,
                     vector<T> v3) {
  if (v1.size() == 0) {
    return v3;
  }
  else {
    T v1_head = v1.front();
    v1.erase(v1.begin());
    T v2_head = v2.front();
    v2.erase(v2.begin());
    T v3_head = v3.front();
    v3.erase(v3.begin());
    vector<T> prefix {v1_head, v2_head, v3_head};
    vector<T> tail = three_way_merge(v1, v2, v3);
    prefix.insert(prefix.end(), tail.begin(), tail.end());
    return prefix;
  }
}
/**
* \brief Deterministic re-ordering algorithm equivalent 
*        to the one used by leanCoP2.0. 
*
* Reorders clauses but not literals within them.
*/
template<class T>
vector<T> deterministic_reorder_once(vector<T> v) {
  size_t s = v.size();
  size_t s2 = s / 3;
  vector<T> v1 = v;
  v1.erase(v1.begin() + s2, v1.end());
  vector<T> v2 = v;
  v2.erase(v2.begin(), v2.begin() + s2);
  v2.erase(v2.end() - s2, v2.end());
  vector<T> v3 = v;
  v3.erase(v3.begin(), v3.end() - s2);
  return three_way_merge<T>(v3, v1, v2);
}
/**
* \brief Er, well, does exactly what it says!
*/
template<class T>
vector<T> deterministic_reorder_n_times(vector<T> v, size_t n) {
  for (size_t i = 0; i < n; i++)
    v = deterministic_reorder_once(v);
  return v;
}

#endif