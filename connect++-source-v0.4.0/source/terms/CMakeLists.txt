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

# Add terms library for Connect++

add_library(terms_lib OBJECT 
    Function.cpp
    FunctionIndex.cpp
    Term.cpp
    TermIndex.cpp
    Variable.cpp
    VariableIndex.cpp
)

target_compile_options(terms_lib PRIVATE -Ofast)

target_include_directories(terms_lib PRIVATE
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/utilities
    ${Boost_INCLUDE_DIRS}
)
