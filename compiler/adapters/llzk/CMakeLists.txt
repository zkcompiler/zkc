cmake_minimum_required(VERSION 3.24)
project(ZkcLLZKAdapter LANGUAGES C CXX)

# Standalone by design: never add_subdirectory this into the LLVM 23 compiler.
if(NOT PROJECT_IS_TOP_LEVEL)
  message(FATAL_ERROR "Configure the LLZK adapter as a separate project")
endif()
# Match LLZK's minimum version without rejecting compatible patch releases.
find_package(LLVM 20.1.8 REQUIRED CONFIG)
find_package(MLIR REQUIRED CONFIG)
if(NOT LLVM_VERSION_MAJOR EQUAL 20)
  message(FATAL_ERROR "The LLZK adapter requires its separate LLVM/MLIR 20 toolchain")
endif()
find_package(LLZK REQUIRED CONFIG)
set(ZKC_LLZK_REVISION "unverified" CACHE STRING
  "Declared LLZK source revision; the verified build helper supplies this value")
add_library(zkc-llzk-admission STATIC Adapter.cpp)
target_compile_features(zkc-llzk-admission PUBLIC cxx_std_20)
target_compile_options(zkc-llzk-admission PRIVATE -Wall -Wextra -Wpedantic)
target_compile_definitions(zkc-llzk-admission PRIVATE
  ZKC_LLZK_REVISION="${ZKC_LLZK_REVISION}")
target_include_directories(zkc-llzk-admission SYSTEM PUBLIC ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
target_include_directories(zkc-llzk-admission PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/../../include)
target_link_libraries(zkc-llzk-admission PUBLIC
  LLZK::LLZKDialectRegistration LLZK::LLZKTransforms
  LLZK::R1CSDialectRegistration LLZK::R1CSTransforms LLZK::R1CSTarget
  MLIRParser MLIRTransforms MLIRIR LLVMSupport)
add_executable(zkc-llzk main.cpp)
target_link_libraries(zkc-llzk PRIVATE zkc-llzk-admission)
include(CTest)
if(BUILD_TESTING)
  find_package(Python3 REQUIRED COMPONENTS Interpreter)
  add_test(NAME llzk-adapter COMMAND ${Python3_EXECUTABLE}
    ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_adapter.py $<TARGET_FILE:zkc-llzk>)
  add_executable(zkc-llzk-guard-test tests/guard.cpp)
  target_link_libraries(zkc-llzk-guard-test PRIVATE zkc-llzk-admission)
  add_test(NAME llzk-final-guard COMMAND zkc-llzk-guard-test)
endif()
