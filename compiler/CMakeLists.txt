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
add_library(ZkcCompiler
  lib/Claims/Trace.cpp
  lib/Claims/Codec.cpp
  lib/Claims/Check.cpp
  lib/Claims/IR.cpp
  lib/Claims/Driver.cpp
  lib/Dialect/ClaimDialect.cpp
  lib/Analysis/Obligations.cpp
  lib/Analysis/OracleAccess.cpp
  lib/Analysis/PolynomialDomains.cpp
  lib/Compiler/Driver.cpp
  lib/Compiler/Generic.cpp
  lib/Compiler/Inspection.cpp
  lib/Compiler/Instantiation.cpp
  lib/Compiler/Library.cpp
  lib/Compiler/Pipelines.cpp
  lib/Compiler/Physical.cpp
  lib/Compiler/Requirements.cpp
  lib/Compiler/SourceLocations.cpp
  lib/Compiler/TableLibrary.cpp
  lib/Conversion/PIRToPlan.cpp
  lib/Conversion/PlanToPhysical.cpp
  lib/Dialect/AlgebraDialect.cpp
  lib/Dialect/LinearContraction.cpp
  lib/Dialect/Kernels.cpp
  lib/Dialect/Operations.cpp
  lib/Dialect/PCSDialect.cpp
  lib/Dialect/OracleDialect.cpp
  lib/Dialect/RelationDialect.cpp
  lib/Dialect/PIRDialect.cpp
  lib/Dialect/PlanDialect.cpp
  lib/Dialect/PolynomialDialect.cpp
  lib/Dialect/Protocol.cpp
  lib/Frontend/Compile.cpp
  lib/Frontend/Dependencies.cpp
  lib/Frontend/Diagnostic.cpp
  lib/Frontend/Input.cpp
  lib/Frontend/Project.cpp
  lib/Frontend/Capture.cpp
  lib/Frontend/Resolution/Project.cpp
  lib/Frontend/Resolution/Names.cpp
  lib/Frontend/Resolution/Environment.cpp
  lib/Frontend/Instantiation/Select.cpp
  lib/Frontend/Library/Body.cpp
  lib/Frontend/Library/Conformance.cpp
  lib/Frontend/Library/Identity.cpp
  lib/Frontend/Library/Interface.cpp
  lib/Frontend/Library/Link.cpp
  lib/Frontend/Library/Representation.cpp
  lib/Frontend/Library/Static.cpp
  lib/Frontend/Library/Types.cpp
  lib/Frontend/Library/World.cpp
  lib/Frontend/Lowering/Admission.cpp
  lib/Frontend/Lowering/Library.cpp
  lib/Frontend/Lowering/PIR.cpp
  lib/Frontend/Model/Module.cpp
  lib/Frontend/Semantics/Aggregates.cpp
  lib/Frontend/Semantics/Body.cpp
  lib/Frontend/Semantics/Captures.cpp
  lib/Frontend/Semantics/Check.cpp
  lib/Frontend/Semantics/Libraries.cpp
  lib/Frontend/Semantics/Local.cpp
  lib/Frontend/Semantics/Protocols.cpp
  lib/Frontend/Static/Naturals.cpp
  lib/Frontend/Syntax/Format.cpp
  lib/Frontend/Syntax/Lexer.cpp
  lib/Frontend/Syntax/Parser.cpp
  lib/Frontend/Tooling/Analysis.cpp
  lib/Frontend/Tooling/Calls.cpp
  lib/Frontend/Tooling/Inspection.cpp
  lib/Frontend/Tooling/Libraries.cpp
  lib/Frontend/Tooling/Lints.cpp
  lib/Frontend/Tooling/Printer.cpp
  lib/Frontend/Tooling/Syntax.cpp
  lib/Protocol/Algorithms.cpp
  lib/Protocol/Admission.cpp
  lib/Protocol/BindingIR.cpp
  lib/Protocol/BindingPhysical.cpp
  lib/Protocol/Variant.cpp
  lib/Protocol/Bindings.cpp
  lib/Protocol/Construction.cpp
  lib/Protocol/Contracts.cpp
  lib/Protocol/ConstructionAvailability.cpp
  lib/Protocol/ConstructionEmission.cpp
  lib/Protocol/ConstructionResources.cpp
  lib/Protocol/Domains.cpp
  lib/Protocol/Export.cpp
  lib/Protocol/Import.cpp
  lib/Protocol/Library.cpp
  lib/Protocol/Physical.cpp
  lib/Protocol/PhysicalOptions.cpp
  lib/Protocol/Storage.cpp
  lib/Protocol/Projection.cpp
  lib/Protocol/Representations.cpp
  lib/Relation/Authoring.cpp
  lib/Relation/R1CS.cpp
  lib/Relation/R1CSBinary.cpp
  lib/Relation/IR.cpp
  lib/Relation/AIR.cpp
  lib/Relation/AIRPolynomial.cpp
  lib/Relation/AIRIR.cpp
  lib/Relation/AIRCommands.cpp
  lib/Relation/Lowering.cpp
  lib/Relation/Driver.cpp
  lib/Source/Decode.cpp
  lib/Source/Document.cpp
  lib/Source/Encode.cpp
  lib/Source/Execution.cpp
  lib/Source/Model.cpp
  lib/Source/Resolution.cpp
  lib/Source/Structure.cpp
  lib/Support/Input.cpp
  lib/Target/Json.cpp
  lib/Target/Source.cpp
  lib/Transforms/Passes.cpp
  lib/Transforms/LinearContraction.cpp
  lib/Transforms/TableSimplification.cpp
)
add_dependencies(ZkcCompiler ZkcIRGen)
target_compile_options(ZkcCompiler PRIVATE -Wall -Wextra -Werror)
target_link_libraries(ZkcCompiler PUBLIC MLIRIR MLIRParser MLIRPass MLIRTransforms
  MLIRTransformUtils MLIRControlFlowInterfaces MLIRSideEffectInterfaces MLIRInferTypeOpInterface MLIRFuncDialect)
add_executable(zkc-compile tools/zkc-compile.cpp)
target_link_libraries(zkc-compile PRIVATE ZkcCompiler)
target_compile_options(zkc-compile PRIVATE -Wall -Wextra -Werror)
add_executable(zkc-source-bench tools/zkc-source-bench.cpp)
target_link_libraries(zkc-source-bench PRIVATE ZkcCompiler)
target_compile_options(zkc-source-bench PRIVATE -Wall -Wextra -Werror)
target_compile_definitions(zkc-source-bench PRIVATE
  ZKC_BENCH_VERSION="${PROJECT_VERSION}"
  ZKC_BENCH_BUILD_TYPE="${CMAKE_BUILD_TYPE}")
add_executable(zkc-opt tools/zkc-opt.cpp)
foreach(tool zkc-compile zkc-opt)
  target_compile_definitions(${tool} PRIVATE ZKC_VERSION="${PROJECT_VERSION}")
endforeach()
target_link_libraries(zkc-opt PRIVATE ZkcCompiler MLIRMlirOptMain)
target_compile_options(zkc-opt PRIVATE -Wall -Wextra -Werror)

include(CMakePackageConfigHelpers)
set_target_properties(ZkcCompiler PROPERTIES EXPORT_NAME Compiler)
target_include_directories(ZkcCompiler PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>)
target_include_directories(ZkcCompiler SYSTEM PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>
  $<BUILD_INTERFACE:${LLVM_INCLUDE_DIRS}>
  $<BUILD_INTERFACE:${MLIR_INCLUDE_DIRS}>)
separate_arguments(zkc_llvm_definitions NATIVE_COMMAND "${LLVM_DEFINITIONS}")
target_compile_options(ZkcCompiler PUBLIC ${zkc_llvm_definitions})
target_compile_features(ZkcCompiler PUBLIC cxx_std_17)
# Keep installed tools usable with the selected external LLVM/MLIR package.
# Build-tree RPATHs are removed on install; a shared ZkcCompiler lives in lib.
set_target_properties(ZkcCompiler zkc-compile zkc-opt PROPERTIES
  INSTALL_RPATH_USE_LINK_PATH TRUE)
set_property(TARGET ZkcCompiler zkc-compile zkc-opt APPEND PROPERTY
  INSTALL_RPATH "$ORIGIN/../lib")
install(TARGETS ZkcCompiler zkc-compile zkc-opt EXPORT ZkcCompilerTargets
  ARCHIVE DESTINATION lib LIBRARY DESTINATION lib RUNTIME DESTINATION bin)
install(DIRECTORY include/zkc DESTINATION include FILES_MATCHING PATTERN "*.h" PATTERN "*.td")
install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include/zkc DESTINATION include
  FILES_MATCHING PATTERN "*.h.inc")
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
