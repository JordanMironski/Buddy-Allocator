# CMakeList.txt : CMake project for quickSort, include source and define
# project specific logic here.
#
cmake_minimum_required (VERSION 3.20)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)
project ("buddy")

# Add source to this project's executable.
add_executable (buddy "oallocre.cpp")

# TODO: Add tests and install targets if needed.