cmake_minimum_required(VERSION 3.24)
project(ZkcLLZKAdapter LANGUAGES C CXX)

# Standalone by design: process isolation is independent of the LLVM version.
if(NOT PROJECT_IS_TOP_LEVEL)
  message(FATAL_ERROR "Configure the LLZK adapter as a separate project")
endif()
find_package(LLVM 23.1.3 EXACT REQUIRED CONFIG)
find_package(MLIR 23.1.3 EXACT REQUIRED CONFIG)
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
  add_test(NAME llzk-build-custody COMMAND ${Python3_EXECUTABLE}
    ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_build.py)
  add_test(NAME llzk-adapter COMMAND ${Python3_EXECUTABLE}
    ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_adapter.py $<TARGET_FILE:zkc-llzk>)
  add_executable(zkc-llzk-guard-test tests/guard.cpp)
  target_link_libraries(zkc-llzk-guard-test PRIVATE zkc-llzk-admission)
  add_test(NAME llzk-final-guard COMMAND zkc-llzk-guard-test)
  set(ZKC_NATIVE_COMPILER "" CACHE FILEPATH "Native compiler for relation integration checks")
  if(ZKC_NATIVE_COMPILER)
    add_test(NAME llzk-native-relation COMMAND ${Python3_EXECUTABLE}
      ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_native.py $<TARGET_FILE:zkc-llzk>
      ${ZKC_NATIVE_COMPILER})
  endif()
endif()
