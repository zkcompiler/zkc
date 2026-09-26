cmake_minimum_required(VERSION 3.21)
project(ZkcCompiler VERSION 0.1 LANGUAGES C CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
option(ZKC_ENABLE_ASSERTIONS "Keep project assertions in optimized development builds" OFF)
option(ZKC_ENABLE_SANITIZERS "Instrument project C++ code with ASan and UBSan" OFF)
if(ZKC_ENABLE_ASSERTIONS)
  add_compile_options(-UNDEBUG)
endif()
if(ZKC_ENABLE_SANITIZERS)
  if(NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(FATAL_ERROR "The sanitizer configuration requires Clang")
  endif()
  add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer
    -fno-sanitize-recover=all)
  add_link_options(-fsanitize=address,undefined -fno-sanitize-recover=all)
endif()
find_package(MLIR REQUIRED CONFIG)
# Some distributions export a tool name instead of an absolute TableGen path.
# Ninja needs an actual file for the generated headers' dependency edge.
if(NOT IS_ABSOLUTE "${MLIR_TABLEGEN_EXE}")
  find_program(ZKC_MLIR_TABLEGEN_EXE NAMES mlir-tblgen
    HINTS "${MLIR_TOOLS_DIR}" "${LLVM_TOOLS_BINARY_DIR}" REQUIRED)
  set(MLIR_TABLEGEN_EXE "${ZKC_MLIR_TABLEGEN_EXE}")
endif()
# MLIR's C++ interfaces change between major releases, so the major release is
# what a native build requires. The Nix lock selects the tested upstream patch;
# other native 23 builds report their difference with this baseline.
set(ZKC_TESTED_LLVM_VERSION "23.1.0")
if(NOT LLVM_VERSION_MAJOR EQUAL 23)
  message(FATAL_ERROR
    "zkc requires LLVM/MLIR 23; found ${LLVM_PACKAGE_VERSION}")
endif()
if(NOT LLVM_PACKAGE_VERSION VERSION_EQUAL ZKC_TESTED_LLVM_VERSION)
  message(WARNING
    "LLVM/MLIR ${LLVM_PACKAGE_VERSION} differs from the tested "
    "${ZKC_TESTED_LLVM_VERSION}; record the version with any evidence.")
endif()
list(APPEND CMAKE_MODULE_PATH "${MLIR_CMAKE_DIR}" "${LLVM_CMAKE_DIR}")
include(TableGen)
include(AddLLVM)
include(AddMLIR)
include(cmake/GenerateIR.cmake)
include(cmake/Components.cmake)
add_executable(zkc-compile tools/zkc-compile.cpp)
target_link_libraries(zkc-compile PRIVATE ZkcDriver)
target_compile_options(zkc-compile PRIVATE -Wall -Wextra -Werror)
add_executable(zkc-source-bench tools/zkc-source-bench.cpp)
target_link_libraries(zkc-source-bench PRIVATE ZkcCompilerCore)
target_compile_options(zkc-source-bench PRIVATE -Wall -Wextra -Werror)
target_compile_definitions(zkc-source-bench PRIVATE
  ZKC_BENCH_VERSION="${PROJECT_VERSION}"
  ZKC_BENCH_BUILD_TYPE="${CMAKE_BUILD_TYPE}")
add_executable(zkc-opt tools/zkc-opt.cpp)
foreach(tool zkc-compile zkc-opt)
  target_compile_definitions(${tool} PRIVATE ZKC_VERSION="${PROJECT_VERSION}")
endforeach()
target_link_libraries(zkc-opt PRIVATE ZkcCompilerCore MLIRMlirOptMain)
target_compile_options(zkc-opt PRIVATE -Wall -Wextra -Werror)

include(CMakePackageConfigHelpers)
# Keep installed tools usable with the selected external LLVM/MLIR package.
set_target_properties(zkc-compile zkc-opt PROPERTIES
  INSTALL_RPATH_USE_LINK_PATH TRUE INSTALL_RPATH "$ORIGIN/../lib")
install(TARGETS ${zkc_components} ZkcCompiler zkc-compile zkc-opt
  EXPORT ZkcCompilerTargets
  ARCHIVE DESTINATION lib LIBRARY DESTINATION lib RUNTIME DESTINATION bin)
install(DIRECTORY include/zkc DESTINATION include FILES_MATCHING PATTERN "*.h" PATTERN "*.td")
# Install current generated declarations only. A reused build tree can contain
# obsolete output paths after TableGen inputs move.
foreach(header ${zkc_generated_headers})
  get_filename_component(directory "${header}" DIRECTORY)
  install(FILES "${CMAKE_CURRENT_BINARY_DIR}/${header}" DESTINATION "${directory}")
endforeach()
install(EXPORT ZkcCompilerTargets NAMESPACE Zkc:: DESTINATION lib/cmake/ZkcCompiler)
configure_package_config_file(cmake/ZkcCompilerConfig.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/ZkcCompilerConfig.cmake"
  INSTALL_DESTINATION lib/cmake/ZkcCompiler)
write_basic_package_version_file("${CMAKE_CURRENT_BINARY_DIR}/ZkcCompilerConfigVersion.cmake"
  COMPATIBILITY ExactVersion)
install(FILES "${CMAKE_CURRENT_BINARY_DIR}/ZkcCompilerConfig.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/ZkcCompilerConfigVersion.cmake"
  DESTINATION lib/cmake/ZkcCompiler)
include(CTest)
if(BUILD_TESTING)
  add_subdirectory(examples/service)
  add_subdirectory(test)
endif()
