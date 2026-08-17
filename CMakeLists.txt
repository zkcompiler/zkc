cmake_minimum_required(VERSION 3.20.0)
project(zkc VERSION 0 LANGUAGES CXX C)

set(CMAKE_CXX_STANDARD 17 CACHE STRING "C++ standard (LLVM minimum)")
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(MLIR REQUIRED CONFIG)
message(STATUS "Using MLIRConfig.cmake in: ${MLIR_DIR}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# The floor, not a pin. PIR's dependency edges are the builtin `token` type,
# which MLIR gained in 23; nothing else here constrains the toolchain, and the
# artifact identity is computed over zkc's own canonical encoding rather than
# anything MLIR emits. Stated as an explicit comparison because MLIRConfig's
# version file admits only an exact major.minor, so passing 23 to
# find_package would reject 23.1 rather than accept it.
#
# The absent case is refused rather than skipped: CMake compares an undefined
# variable as an empty string, which is not LESS than 23, so the version test
# alone would pass silently on a package that reports no version.
if(NOT DEFINED LLVM_VERSION_MAJOR)
  message(FATAL_ERROR
    "the MLIR package reports no version; zkc requires 23 or newer and does "
    "not assume an unreported version satisfies that")
endif()
if(LLVM_VERSION_MAJOR LESS 23)
  message(FATAL_ERROR
    "zkc requires LLVM/MLIR 23 or newer; found ${LLVM_PACKAGE_VERSION}")
endif()

set(LLVM_RUNTIME_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/bin)
set(LLVM_LIBRARY_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/lib)
set(MLIR_BINARY_DIR ${CMAKE_BINARY_DIR})

list(APPEND CMAKE_MODULE_PATH "${MLIR_CMAKE_DIR}")
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(TableGen)
include(AddLLVM)
include(AddMLIR)
include(HandleLLVMOptions)

include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${MLIR_INCLUDE_DIRS})
include_directories(${PROJECT_SOURCE_DIR}/include)
include_directories(${PROJECT_BINARY_DIR}/include)
link_directories(${LLVM_BUILD_LIBRARY_DIR})
add_definitions(${LLVM_DEFINITIONS})

add_subdirectory(include/zkc/Dialect/Oir)
add_subdirectory(include/zkc/Dialect/Pir)
add_subdirectory(lib)
add_subdirectory(tools)
add_subdirectory(unittests)
add_subdirectory(test)
