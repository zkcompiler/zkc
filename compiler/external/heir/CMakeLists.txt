cmake_minimum_required(VERSION 3.24)
project(ZkcHeirArithmetic VERSION 0.0.0 LANGUAGES C CXX)
find_package(Python3 REQUIRED COMPONENTS Interpreter)
find_package(LLVM 23.1.3 EXACT REQUIRED CONFIG)
find_package(MLIR 23.1.3 EXACT REQUIRED CONFIG)
if(NOT LLVM_PACKAGE_VERSION VERSION_EQUAL "23.1.3")
  message(FATAL_ERROR "HEIR arithmetic is qualified against LLVM/MLIR 23.1.3")
endif()
find_package(ortools 9.15.6755 EXACT CONFIG REQUIRED)
set(ZKC_HEIR_SOURCE_DIR "" CACHE PATH "Verified, patched HEIR source from build.py")
if(NOT EXISTS "${ZKC_HEIR_SOURCE_DIR}/lib/Dialect/Polynomial/IR/PolynomialOps.td")
  message(FATAL_ERROR "Run build.py with the archive selected in pins.json")
endif()
if(NOT EXISTS "${MLIR_TABLEGEN_EXE}")
  message(FATAL_ERROR "MLIR_TABLEGEN_EXE must name the selected mlir-tblgen")
endif()

# Upstream Bazel uses repository-relative include paths. Provide those aliases
# locally without changing LLVM headers or installing global include symlinks.
foreach(owner llvm mlir)
  string(TOUPPER "${owner}" upper)
  foreach(directory IN LISTS ${upper}_INCLUDE_DIRS)
    if(EXISTS "${directory}/${owner}")
      file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/include-shims/${owner}/include")
      file(CREATE_LINK "${directory}/${owner}"
        "${CMAKE_CURRENT_BINARY_DIR}/include-shims/${owner}/include/${owner}" SYMBOLIC)
      break()
    endif()
  endforeach()
endforeach()

# Some OR-Tools binary packages expose the host /usr/include through their
# compression imports. A sysroot compiler must keep its own system headers.
if(CMAKE_CXX_COMPILER MATCHES "^/nix/store/")
  foreach(target ZLIB::ZLIB BZip2::BZip2)
    if(TARGET ${target})
      get_target_property(paths ${target} INTERFACE_INCLUDE_DIRECTORIES)
      if(paths)
        list(REMOVE_ITEM paths "/usr/include")
        set_property(TARGET ${target} PROPERTY INTERFACE_INCLUDE_DIRECTORIES "${paths}")
      endif()
    endif()
  endforeach()
endif()

file(GLOB_RECURSE td_dependencies CONFIGURE_DEPENDS "${ZKC_HEIR_SOURCE_DIR}/lib/*.td")
set(tablegen_includes)
foreach(directory IN LISTS LLVM_INCLUDE_DIRS MLIR_INCLUDE_DIRS)
  list(APPEND tablegen_includes -I "${directory}")
endforeach()
function(heir_tablegen input output generator)
  get_filename_component(directory "${output}" DIRECTORY)
  get_filename_component(input_directory "${input}" DIRECTORY)
  set(destination "${CMAKE_CURRENT_BINARY_DIR}/generated/${output}")
  add_custom_command(OUTPUT "${destination}"
    COMMAND ${CMAKE_COMMAND} -E make_directory "${CMAKE_CURRENT_BINARY_DIR}/generated/${directory}"
    COMMAND "${MLIR_TABLEGEN_EXE}" "-${generator}" ${ARGN}
      -I "${ZKC_HEIR_SOURCE_DIR}" -I "${ZKC_HEIR_SOURCE_DIR}/${input_directory}"
      ${tablegen_includes}
      "${ZKC_HEIR_SOURCE_DIR}/${input}" -o "${destination}"
    DEPENDS ${td_dependencies} "${MLIR_TABLEGEN_EXE}" VERBATIM)
  set_property(GLOBAL APPEND PROPERTY zkc_heir_generated "${destination}")
endfunction()
foreach(dialect ModArith Polynomial RNS Secret LWE TfheRust)
  set(kinds Dialect:dialect Attributes:attrdef Types:typedef Ops:op Enums:enum TypeInterfaces:type-interface)
  if(dialect STREQUAL "Secret")
    set(kinds Dialect:dialect Attributes:attrdef)
  elseif(dialect STREQUAL "LWE")
    set(kinds Dialect:dialect)
  elseif(dialect STREQUAL "TfheRust")
    set(kinds Dialect:dialect Types:typedef)
  endif()
  set(base "lib/Dialect/${dialect}/IR/${dialect}")
  foreach(pair IN LISTS kinds)
    string(REPLACE ":" ";" parts "${pair}")
    list(GET parts 0 suffix)
    list(GET parts 1 generator)
    if(EXISTS "${ZKC_HEIR_SOURCE_DIR}/${base}${suffix}.td")
      heir_tablegen("${base}${suffix}.td" "${base}${suffix}.h.inc" "gen-${generator}-decls")
      heir_tablegen("${base}${suffix}.td" "${base}${suffix}.cpp.inc" "gen-${generator}-defs")
    endif()
  endforeach()
  if(EXISTS "${ZKC_HEIR_SOURCE_DIR}/${base}Canonicalization.td")
    heir_tablegen("${base}Canonicalization.td" "${base}Canonicalization.cpp.inc" gen-rewriters)
  endif()
endforeach()
foreach(kind Attr Op Type)
  string(TOLOWER "${kind}" lower)
  heir_tablegen(lib/Dialect/HEIRInterfaces.td "lib/Dialect/HEIR${kind}Interfaces.h.inc" "gen-${lower}-interface-decls")
  heir_tablegen(lib/Dialect/HEIRInterfaces.td "lib/Dialect/HEIR${kind}Interfaces.cpp.inc" "gen-${lower}-interface-defs")
endforeach()
foreach(dialect Polynomial ModArith)
  if(dialect STREQUAL "Polynomial")
    set(name PolynomialToModArith)
  else()
    set(name ModArithToArith)
  endif()
  set(base "lib/Dialect/${dialect}/Conversions/${name}/${name}")
  heir_tablegen("${base}.td" "${base}.h.inc" gen-pass-decls)
  if(dialect STREQUAL "ModArith")
    heir_tablegen("${base}.td" "${base}.cpp.inc" gen-rewriters)
  endif()
endforeach()
foreach(dialect Polynomial RNS)
  heir_tablegen("lib/Dialect/${dialect}/Transforms/Passes.td"
    "lib/Dialect/${dialect}/Transforms/Passes.h.inc" gen-pass-decls "-name=${dialect}")
endforeach()
get_property(generated GLOBAL PROPERTY zkc_heir_generated)
add_custom_target(ZkcHeirTableGen DEPENDS ${generated})

# Selected arithmetic sources only. Encryption schemes are not linked.
file(GLOB dialect_sources CONFIGURE_DEPENDS
  "${ZKC_HEIR_SOURCE_DIR}/lib/Dialect/ModArith/IR/*.cpp"
  "${ZKC_HEIR_SOURCE_DIR}/lib/Dialect/Polynomial/IR/*.cpp"
  "${ZKC_HEIR_SOURCE_DIR}/lib/Dialect/RNS/IR/*.cpp")
set(sources lib/Dialect/HEIRInterfaces.cpp lib/Utils/APIntUtils.cpp
  lib/Utils/MathUtils.cpp lib/Utils/Polynomial/Polynomial.cpp
  lib/Utils/Polynomial/RNSPolynomial.cpp lib/Utils/Polynomial/NTT.cpp
  lib/Utils/ConversionUtils.cpp lib/Utils/Utils.cpp
  lib/Dialect/Polynomial/Conversions/PolynomialToModArith/PolynomialToModArith.cpp
  lib/Dialect/ModArith/Conversions/ModArithToArith/ModArithToArith.cpp
  lib/Dialect/Polynomial/Transforms/PolyMulToNTT.cpp
  lib/Dialect/Polynomial/Transforms/NTTSolver.cpp
  lib/Dialect/Polynomial/Transforms/AttachNTTRoots.cpp
  lib/Dialect/RNS/Transforms/LowerConvertBasis.cpp)
list(TRANSFORM sources PREPEND "${ZKC_HEIR_SOURCE_DIR}/")
add_library(ZkcHeirArithmetic STATIC ${sources} ${dialect_sources})
add_dependencies(ZkcHeirArithmetic ZkcHeirTableGen)
target_compile_features(ZkcHeirArithmetic PUBLIC cxx_std_20)
target_include_directories(ZkcHeirArithmetic SYSTEM PUBLIC
  "$<BUILD_INTERFACE:${ZKC_HEIR_SOURCE_DIR}>"
  "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/generated>"
  "$<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include-shims>"
  "$<INSTALL_INTERFACE:include/zkc-heir>")
foreach(directory IN LISTS LLVM_INCLUDE_DIRS MLIR_INCLUDE_DIRS)
  target_include_directories(ZkcHeirArithmetic SYSTEM PUBLIC "$<BUILD_INTERFACE:${directory}>")
endforeach()
target_link_libraries(ZkcHeirArithmetic PUBLIC MLIR LLVM absl::int128 ortools::ortools)
add_executable(zkc-heir-opt main.cpp)
target_link_libraries(zkc-heir-opt PRIVATE ZkcHeirArithmetic)
add_library(ZkcHeirAdmission STATIC Admission.cpp Placement.cpp)
target_include_directories(ZkcHeirAdmission PUBLIC
  "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>" "$<INSTALL_INTERFACE:include>")
target_link_libraries(ZkcHeirAdmission PUBLIC ZkcHeirArithmetic)
target_compile_options(ZkcHeirAdmission PRIVATE -Wall -Wextra -Werror)
add_executable(zkc-heir-check check.cpp)
target_link_libraries(zkc-heir-check PRIVATE ZkcHeirAdmission)
add_executable(zkc-heir-place place.cpp)
target_link_libraries(zkc-heir-place PRIVATE ZkcHeirAdmission)
option(ZKC_HEIR_ENABLE_SANITIZERS "Instrument zkc arithmetic readers and drivers" OFF)
if(ZKC_HEIR_ENABLE_SANITIZERS)
  # Static library consumers must link the instrumentation runtimes too.
  target_link_options(ZkcHeirAdmission INTERFACE -fsanitize=address,undefined)
  foreach(target ZkcHeirAdmission zkc-heir-check zkc-heir-place)
    target_compile_options(${target} PRIVATE -fsanitize=address,undefined
      -fno-omit-frame-pointer -fno-sanitize-recover=all)
    target_link_options(${target} PRIVATE -fsanitize=address,undefined)
  endforeach()
endif()
include(CTest)
if(BUILD_TESTING)
  find_package(Python3 REQUIRED COMPONENTS Interpreter)
  find_program(ZKC_HEIR_MLIR_OPT mlir-opt HINTS "${MLIR_INSTALL_PREFIX}/bin" REQUIRED)
  find_program(ZKC_HEIR_MLIR_RUNNER mlir-runner HINTS "${MLIR_INSTALL_PREFIX}/bin" REQUIRED)
  find_library(ZKC_HEIR_RUNNER_UTILS mlir_c_runner_utils HINTS "${MLIR_INSTALL_PREFIX}/lib" REQUIRED)
  add_test(NAME heir-installed-consumer COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_CURRENT_SOURCE_DIR}/tests/sdk.py"
    --build "${CMAKE_CURRENT_BINARY_DIR}" --work "${CMAKE_CURRENT_BINARY_DIR}/sdk-tests"
    --llvm-dir "${LLVM_DIR}" --mlir-dir "${MLIR_DIR}" --ortools-dir "${ortools_DIR}"
    --cc "${CMAKE_C_COMPILER}" --cxx "${CMAKE_CXX_COMPILER}")
  add_test(NAME heir-arithmetic COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_CURRENT_SOURCE_DIR}/tests/arithmetic.py"
    --optimizer $<TARGET_FILE:zkc-heir-opt> --checker $<TARGET_FILE:zkc-heir-check>
    --placement $<TARGET_FILE:zkc-heir-place>
    --mlir-opt "${ZKC_HEIR_MLIR_OPT}" --runner "${ZKC_HEIR_MLIR_RUNNER}"
    --runner-utils "${ZKC_HEIR_RUNNER_UTILS}"
    --work "${CMAKE_CURRENT_BINARY_DIR}/test-output")
endif()

include(CMakePackageConfigHelpers)
file(READ "${CMAKE_CURRENT_SOURCE_DIR}/pins.json" pins)
string(JSON HEIR_REVISION GET "${pins}" heir revision)
string(JSON HEIR_PATCH_SHA256 GET "${pins}" patches 0 sha256)
set_target_properties(ZkcHeirArithmetic PROPERTIES EXPORT_NAME Arithmetic)
set_target_properties(ZkcHeirAdmission PROPERTIES EXPORT_NAME Admission)
install(TARGETS ZkcHeirArithmetic ZkcHeirAdmission EXPORT ZkcHeirArithmeticTargets
  ARCHIVE DESTINATION lib)
install(EXPORT ZkcHeirArithmeticTargets NAMESPACE ZkcHeir::
  DESTINATION lib/cmake/ZkcHeirArithmetic)
configure_package_config_file(ZkcHeirArithmeticConfig.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/ZkcHeirArithmeticConfig.cmake"
  INSTALL_DESTINATION lib/cmake/ZkcHeirArithmetic)
write_basic_package_version_file("${CMAKE_CURRENT_BINARY_DIR}/ZkcHeirArithmeticConfigVersion.cmake"
  COMPATIBILITY ExactVersion)
install(FILES "${CMAKE_CURRENT_BINARY_DIR}/ZkcHeirArithmeticConfig.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/ZkcHeirArithmeticConfigVersion.cmake"
  DESTINATION lib/cmake/ZkcHeirArithmetic)
install(FILES Admission.h Arithmetic.h DESTINATION include/zkc/heir)
install(FILES pins.json DESTINATION share/zkc-heir)
install(FILES "${ZKC_HEIR_SOURCE_DIR}/LICENSE" DESTINATION share/licenses/zkc-heir)
install(CODE "
  execute_process(COMMAND \"${Python3_EXECUTABLE}\"
    \"${CMAKE_CURRENT_SOURCE_DIR}/install_headers.py\"
    --source \"${ZKC_HEIR_SOURCE_DIR}\"
    --generated \"${CMAKE_CURRENT_BINARY_DIR}/generated\"
    --output \"\$ENV{DESTDIR}\${CMAKE_INSTALL_PREFIX}/include/zkc-heir\"
    COMMAND_ERROR_IS_FATAL ANY)")
