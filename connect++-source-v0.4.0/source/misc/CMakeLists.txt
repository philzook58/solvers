#----------------------------------------------------------------------------
# Copyright © 2023-24 Sean Holden. All rights reserved.
#
# This file is part of Connect++.
#
# Connect++ is free software: you can redistribute it and/or modify it 
# under the terms of the GNU General Public License as published by the 
# Free Software Foundation, either version 3 of the License, or (at your 
# option) any later version.
#
# Connect++ is distributed in the hope that it will be useful, but WITHOUT 
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for 
# more details.
#
# You should have received a copy of the GNU General Public License along 
# with Connect++. If not, see <https://www.gnu.org/licenses/>. 
#----------------------------------------------------------------------------

# Add misc library for Connect++

add_library(misc_lib OBJECT 
    Exceptions.cpp
    ProofPrinter.cpp
    ProofChecker.cpp
)

target_compile_options(misc_lib PRIVATE -Ofast)

target_include_directories(misc_lib PRIVATE
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/utilities
    ${PROJECT_SOURCE_DIR}/terms
    ${PROJECT_SOURCE_DIR}/literal
    ${PROJECT_SOURCE_DIR}/substitution
    ${Boost_INCLUDE_DIRS}
)

