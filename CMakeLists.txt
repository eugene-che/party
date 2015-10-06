cmake_minimum_required(VERSION 2.8)
project(party C CXX)

# set(CMAKE_C_COMPILER "/usr/bin/gcc")
# set(CMAKE_CXX_COMPILER "/usr/bin/g++")

# set(CMAKE_C_COMPILER "/usr/bin/clang")
# set(CMAKE_CXX_COMPILER "/usr/bin/clang++")
# set(CMAKE_TOOLCHAIN_PREFIX "llvm-")

set(CMAKE_BUILD_TYPE Release)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall")

include_directories(${PROJECT_SOURCE_DIR})
include_directories(${PROJECT_BINARY_DIR})


find_package(Boost COMPONENTS system filesystem unit_test_framework REQUIRED)
add_definitions(-DBOOST_TEST_DYN_LINK)
  
set(UNIT_TEST_LIBS
  ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
  ${Boost_FILESYSTEM_LIBRARY}
  ${Boost_SYSTEM_LIBRARY}
)

enable_testing()
add_executable(utest utest.cpp party.hpp)
target_link_libraries(utest ${UNIT_TEST_LIBS})
add_test(utest utest)