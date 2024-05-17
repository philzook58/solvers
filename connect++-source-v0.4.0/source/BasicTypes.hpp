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

#ifndef BASICTYPES_HPP
#define BASICTYPES_HPP

/*
* Self-explanatory. Comment these out unless you're actually 
* debugging.
*/
//#define DEBUGOUTPUT
//#define DEBUGMESSAGES
/*
* Some compilers appear not to play nicely with proper 
* hash consing of terms. Delete this to switch it off.
*/
#define HASHCONSTERMS

#include <cstdint>

/*
* Everything that's identified using an integer is represented 
* as a 32 bit unsigned integer. Might as well know exactly what 
* we're dealing with.
*/
using ID = uint32_t;
using Arity = uint32_t;
using LitNum = uint32_t;
using ClauseNum = uint32_t;

#endif
