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

#include "PathUtilities.hpp"

namespace path_utilities {
  /**
  * \brief Add an arbitrary number to the end of a filename.
  *
  * We make use of path objects as much as possible. This 
  * extracts the filename from the path, adds a number - 
  * probably a count - before the extension, and inserts the 
  * modified filename back in the path.
  *
  * @param input_path The path to modify
  * @param count The number to add
  */
  fs::path insert_count_in_path(fs::path input_path, uint32_t count) {
    if (input_path.has_filename()) {
      fs::path stem = input_path.stem();
      fs::path extension = input_path.extension();
      fs::path count_as_path(std::to_string(count));
      stem += count_as_path;
      stem += extension;
      input_path.replace_filename(stem);
    }
    return input_path;
  }
}