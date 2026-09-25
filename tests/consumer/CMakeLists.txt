cmake_minimum_required(VERSION 3.20)
project(ZkcConsumer LANGUAGES C CXX)
find_package(ZkcCompiler REQUIRED CONFIG)
add_executable(consumer main.cpp)
target_link_libraries(consumer PRIVATE Zkc::Compiler)

enable_testing()
add_test(NAME compiler-consumer COMMAND consumer)
foreach(component Support Contracts Relation Protocol IR)
  string(TOLOWER ${component} name)
  add_executable(${name}-consumer ${name}.cpp)
  target_link_libraries(${name}-consumer PRIVATE Zkc::${component})
  target_compile_options(${name}-consumer PRIVATE -Wall -Wextra -Werror)
  add_test(NAME ${name}-consumer COMMAND ${name}-consumer)
endforeach()

# Build the real extension using only the installed package. This also checks
# that public TableGen includes survive component and aggregate changes.
set(ZKC_SERVICE_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/../../compiler/examples/service"
  CACHE PATH "Standalone service extension source directory")
add_subdirectory("${ZKC_SERVICE_SOURCE}" service)
add_test(NAME service-compiler-consumer COMMAND zkc-service-compile --help)
add_test(NAME service-optimizer-consumer COMMAND zkc-service-opt --help)
