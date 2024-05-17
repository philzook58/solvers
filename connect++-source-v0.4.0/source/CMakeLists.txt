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
#
# Primary CMakeLists.txt file for Connect++
#
# If you have Boost installed in a non-standard place and 
# cmake can't find it, use:
#
# cmake ../source -D BOOST_INCLUDEDIR=/where/is/include -D BOOST_LIBRARYDIR=/where/is/lib
#
# If cmake can't find the SWI Prolog executable use:
#
# cmake ../source -D swipl_PATH=/where/is/swipl

# If this is ON, then do static linking.
# To enable, use: 
#
# cmake ../source -D STATIC_LINK=ON
set(STATIC_LINK OFF CACHE BOOL "When ON, perform static linking.")

# If this is ON, search for SWI Prolog and build check_proof.
# To disable, use: 
#
# cmake ../source -D INCLUDE_PROLOG=OFF
set(INCLUDE_PROLOG ON CACHE BOOL "When ON, build the Prolog application 'check_proof'.")

# Standard, basic information.
cmake_minimum_required(VERSION 3.22.1)
project(connect++ VERSION 0.4.0 LANGUAGES CXX)

# We need at least C++ 17.
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED True)

# Sort out the header file for incorporating the version.
configure_file(connect++-version.hpp.in 
               connect++-version.hpp)

# We need to find the BOOST includes and libraries.
set(Boost_USE_RELEASE_LIBS ON)
set(Boost USE_DEBUG_LIBS OFF)
set(Boost_USE_MULTITHREADED ON)
set(Boost_USE_STATIC_LIBS ON)
find_package(Boost 
             1.66.0 
             REQUIRED 
             COMPONENTS program_options
)
if (Boost_FOUND)
    message(STATUS "Found the BOOST libraries. Woohoo!")
    message(STATUS ${Boost_INCLUDE_DIRS})
    message(STATUS ${Boost_LIBRARY_DIRS})
endif()

# Main executable.
add_executable(connect++ 
    connect++.cpp
    Clause.cpp
    FOF.cpp
    InferenceItem.cpp
    Lemmata.cpp
    Matrix.cpp
    Parameters.cpp
    ProverOutcome.cpp
    Schedule.cpp
    SimplePath.cpp
    StackItem.cpp
    StackProver.cpp
    TPTPParser.cpp
)
target_compile_options(connect++ PRIVATE -Ofast)

# Add the subdirectories.
add_subdirectory(terms)
add_subdirectory(literal)
add_subdirectory(substitution)
add_subdirectory(misc)
add_subdirectory(utilities)

# Add the libraries.
add_library(terms
    $<TARGET_OBJECTS:terms_lib>
)
add_library(literal
    $<TARGET_OBJECTS:literal_lib>
)
add_library(substitution
    $<TARGET_OBJECTS:substitution_lib>
)
add_library(misc
    $<TARGET_OBJECTS:misc_lib>
)
add_library(utilities 
    $<TARGET_OBJECTS:utilities_lib>
)

# Make it fast!
target_compile_options(terms PRIVATE -Ofast)
target_compile_options(literal PRIVATE -Ofast)
target_compile_options(substitution PRIVATE -Ofast)
target_compile_options(misc PRIVATE -Ofast)
target_compile_options(utilities PRIVATE -Ofast)

# Add the includes.
target_include_directories(connect++ PRIVATE 
    ${PROJECT_SOURCE_DIR}
    ${PROJECT_BINARY_DIR}
    ${Boost_INCLUDE_DIRS}
    ${PROJECT_SOURCE_DIR}/terms
    ${PROJECT_SOURCE_DIR}/literal
    ${PROJECT_SOURCE_DIR}/substitution
    ${PROJECT_SOURCE_DIR}/misc
    ${PROJECT_SOURCE_DIR}/utilities
)

# Add the link information.
target_link_libraries(connect++ PRIVATE 
    ${Boost_LIBRARY_DIRS}/libboost_program_options.a 
    terms
    literal
    substitution
    misc
    utilities
)

# Optional static linking.
if(STATIC_LINK)
    message(STATUS "Compiler is: " ${CMAKE_CXX_COMPILER_ID})
    if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
        target_link_options(connect++ PRIVATE
            -static 
            -static-libstdc++ 
            -static-libgcc
        )
        message(STATUS "Static linking for g++.")
    else()
        message(STATUS "No static linking - supported for g++ only.")
    endif()
endif()

# If needed, search for SWI Prolog and configure check_proof.
if (INCLUDE_PROLOG)
    message(STATUS "Searching for SWI Prolog...")
    find_program(swipl_PATH
                    NAMES swipl
                    PATHS   /usr/bin/ 
                            /opt/homebrew/bin/ 
                    REQUIRED
    )
    if (swipl_PATH)
        message(STATUS "Found swipl. Woohoo!")
        message(STATUS ${swipl_PATH})
        configure_file(prolog/check_proof.in
                       check_proof
                       FILE_PERMISSIONS OWNER_WRITE
                                        OWNER_READ
                                        OWNER_EXECUTE
                                        GROUP_READ
                                        WORLD_READ
        )
    endif()
endif()