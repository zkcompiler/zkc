# A focused build of the production source/syntax implementation with the
# same data generation and installed SDK configuration. No MLIR.
cmake_minimum_required(VERSION 3.21)
project(ZkcNamesTests VERSION 0.0.0 LANGUAGES C CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
get_filename_component(zkc_compiler "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
find_package(LLVM REQUIRED CONFIG)
if(NOT LLVM_VERSION_MAJOR EQUAL 23)
  message(FATAL_ERROR "The Names tests require LLVM 23")
endif()
include("${zkc_compiler}/cmake/Unicode.cmake")
add_library(ZkcSource "${zkc_compiler}/lib/Source/Names.cpp"
  "${zkc_compiler}/lib/Source/Source.cpp")
set_target_properties(ZkcSource PROPERTIES EXPORT_NAME Source
  INSTALL_RPATH_USE_LINK_PATH TRUE)
add_dependencies(ZkcSource ZkcSourceNameDataGen)
target_include_directories(ZkcSource PUBLIC
  "$<BUILD_INTERFACE:${zkc_compiler}/include>" "$<INSTALL_INTERFACE:include>")
target_include_directories(ZkcSource SYSTEM PUBLIC "$<BUILD_INTERFACE:${LLVM_INCLUDE_DIRS}>")
target_include_directories(ZkcSource PRIVATE "${CMAKE_CURRENT_BINARY_DIR}/generated")
target_link_libraries(ZkcSource PRIVATE utf8proc::utf8proc)
# Reuse the SDK's real Support discovery route for LLVM headers and libraries.
add_library(ZkcSupport INTERFACE)
set_target_properties(ZkcSupport PROPERTIES EXPORT_NAME Support)
if(LLVM_LINK_LLVM_DYLIB)
  target_link_libraries(ZkcSupport INTERFACE LLVM)
else()
  target_link_libraries(ZkcSupport INTERFACE LLVMSupport)
endif()
target_link_libraries(ZkcSource PUBLIC ZkcSupport)
target_compile_options(ZkcSource PRIVATE -Wall -Wextra -Werror)
include("${zkc_compiler}/cmake/InstallSDK.cmake")
add_library(ZkcSyntax
  "${zkc_compiler}/lib/Syntax/Syntax.cpp"
  "${zkc_compiler}/lib/Syntax/Lexer.cpp"
  "${zkc_compiler}/lib/Syntax/Parser.cpp"
  "${zkc_compiler}/lib/Syntax/Format.cpp")
set_target_properties(ZkcSyntax PROPERTIES EXPORT_NAME Syntax
  INSTALL_RPATH_USE_LINK_PATH TRUE)
target_link_libraries(ZkcSyntax PUBLIC ZkcSource)
target_compile_options(ZkcSyntax PRIVATE -Wall -Wextra -Werror)
zkc_install_sdk(COMPONENTS ZkcSupport ZkcSource ZkcSyntax)
install(FILES "${zkc_compiler}/include/zkc/Language/Names.h" DESTINATION include/zkc/Language)
install(DIRECTORY "${zkc_compiler}/include/zkc/Source" "${zkc_compiler}/include/zkc/Syntax" DESTINATION include/zkc)
add_executable(zkc-language_names-test ../language_names.cpp)
target_link_libraries(zkc-language_names-test PRIVATE ZkcSource utf8proc::utf8proc)
target_compile_options(zkc-language_names-test PRIVATE -Wall -Wextra -Werror)
target_compile_definitions(zkc-language_names-test PRIVATE
  ZKC_UNICODE_DATA="${ZKC_UNICODE_SOURCE_DIR}/17.0.0")
enable_testing()
add_test(NAME language-names COMMAND zkc-language_names-test)
add_test(NAME unicode-generation
  COMMAND "${Python3_EXECUTABLE}" "${zkc_compiler}/test/unicode_generation.py")
set_tests_properties(unicode-generation PROPERTIES ENVIRONMENT
  "PYTHONPATH=${zkc_compiler}/test/support:${zkc_compiler}/../common/tests/support")

add_executable(zkc-source_syntax-test ../source_syntax.cpp)
target_link_libraries(zkc-source_syntax-test PRIVATE ZkcSyntax)
target_compile_definitions(zkc-source_syntax-test PRIVATE
  ZKC_SYNTAX_FIXTURES="${zkc_compiler}/test/fixtures/syntax")
add_test(NAME source-syntax COMMAND zkc-source_syntax-test)
