# Contributions own their outputs. Begin a separate core generator inventory,
# so author CMake files do not need to restore MLIR's TABLEGEN_OUTPUT variable.
set(TABLEGEN_OUTPUT)
include(cmake/ContractDeclarations.cmake)
# TableGen needs source and dependency paths independently of C++ targets.
set(zkc_tablegen_includes ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/include ${ZKC_CONTRIBUTION_INCLUDES}
  ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
set(zkc_generated_headers
  include/zkc/Interfaces/SourceOpInterface.h.inc
  include/zkc/Interfaces/LinearContraction.h.inc
  include/zkc/Dialect/Operations.h.inc)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Interfaces)
set(LLVM_TARGET_DEFINITIONS include/zkc/Interfaces/SourceOpInterface.td)
mlir_tablegen(include/zkc/Interfaces/SourceOpInterface.h.inc -gen-op-interface-decls
    EXTRA_INCLUDES ${zkc_tablegen_includes})
mlir_tablegen(include/zkc/Interfaces/SourceOpInterface.cpp.inc -gen-op-interface-defs
    EXTRA_INCLUDES ${zkc_tablegen_includes})
set(LLVM_TARGET_DEFINITIONS include/zkc/Interfaces/LinearContraction.td)
mlir_tablegen(include/zkc/Interfaces/LinearContraction.h.inc -gen-op-interface-decls
    EXTRA_INCLUDES ${zkc_tablegen_includes})
mlir_tablegen(include/zkc/Interfaces/LinearContraction.cpp.inc -gen-op-interface-defs
    EXTRA_INCLUDES ${zkc_tablegen_includes})
set(LLVM_TARGET_DEFINITIONS include/zkc/Dialect/IR.td)
set(zkc_builtin_headers "// Generated private registration includes.\n")
set(zkc_builtin_classes "// Generated private registration classes.\n")
foreach(record IN LISTS zkc_builtin_dialects)
  string(REPLACE "|" ";" fields "${record}")
  list(GET fields 0 dialect)
  list(GET fields 1 owner)
  list(GET fields 2 types)
  string(APPEND zkc_builtin_headers
    "#include \"zkc/Dialect/${owner}/IR/${owner}Dialect.h\"\n")
  string(APPEND zkc_builtin_classes ", ::zkc::${owner}Dialect\n")
  file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/${owner}/IR)
  list(APPEND zkc_generated_headers
    include/zkc/Dialect/${owner}/IR/${dialect}Dialect.h.inc)
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Dialect.h.inc -gen-dialect-decls -dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Dialect.cpp.inc -gen-dialect-defs -dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
  if(types STREQUAL "types")
    list(APPEND zkc_generated_headers
      include/zkc/Dialect/${owner}/IR/${dialect}Types.h.inc)
    mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Types.h.inc -gen-typedef-decls -typedefs-dialect=${dialect}
      EXTRA_INCLUDES ${zkc_tablegen_includes})
    mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Types.cpp.inc -gen-typedef-defs -typedefs-dialect=${dialect}
      EXTRA_INCLUDES ${zkc_tablegen_includes})
  endif()
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Ops.cpp.inc -gen-op-defs
    # A bracketed dot survives the shell the generated command runs in, where
    # a backslash would not.
    "-op-include-regex=^${dialect}[.]" EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
file(CONFIGURE OUTPUT include/zkc/Dialect/BuiltinHeaders.h.inc
  CONTENT "${zkc_builtin_headers}" @ONLY)
file(CONFIGURE OUTPUT include/zkc/Dialect/BuiltinDialects.inc
  CONTENT "${zkc_builtin_classes}" @ONLY)
mlir_tablegen(include/zkc/Dialect/Operations.h.inc -gen-op-decls
  EXTRA_INCLUDES ${zkc_tablegen_includes})
include(cmake/ContractMappings.cmake)
set(LLVM_TARGET_DEFINITIONS
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/Installation.td)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/TypeAdapters)
foreach(record IN LISTS zkc_builtin_type_adapters)
  string(REPLACE "|" ";" fields "${record}")
  list(GET fields 0 owner)
  list(GET fields 1 file)
  tablegen(ZKC include/zkc/Dialect/TypeAdapters/${file}.inc
    -gen-type-bindings -type-binding-owner=${owner}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
foreach(owner IN LISTS ZKC_CONTRIBUTION_ADAPTER_OWNERS)
  tablegen(ZKC include/zkc/Dialect/TypeAdapters/${owner}.inc
    -gen-type-bindings -type-binding-owner=${owner}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
tablegen(ZKC include/zkc/Dialect/TypeAdapters/Installed.inc
  -gen-type-bindings EXTRA_INCLUDES ${zkc_tablegen_includes})
# Record only outputs declared by these TableGen invocations. Reused build
# trees may contain obsolete generated files, which are not valid dependencies.
set(zkc_ir_generated_files ${TABLEGEN_OUTPUT}
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/BuiltinHeaders.h.inc
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/BuiltinDialects.inc
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/ContributionHeaders.h.inc
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/ContributionDialects.inc)
list(REMOVE_DUPLICATES zkc_ir_generated_files)
list(JOIN zkc_ir_generated_files "\n" zkc_ir_generated_files)
file(GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/ir-generated-files.txt"
  CONTENT "${zkc_ir_generated_files}\n")
add_public_tablegen_target(ZkcIRGen)
