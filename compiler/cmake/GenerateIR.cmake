# TableGen needs source and dependency paths independently of C++ targets.
set(zkc_tablegen_includes ${CMAKE_CURRENT_SOURCE_DIR}/include
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
set(zkc_dialects pir algebra poly plan pcs oracle relation claim)
set(zkc_dialect_owners PIR Algebra Polynomial Plan PCS Oracle Relation Claim)
foreach(dialect owner IN ZIP_LISTS zkc_dialects zkc_dialect_owners)
  file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/${owner}/IR)
  list(APPEND zkc_generated_headers
    include/zkc/Dialect/${owner}/IR/${dialect}Dialect.h.inc)
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Dialect.h.inc -gen-dialect-decls -dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Dialect.cpp.inc -gen-dialect-defs -dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
foreach(dialect owner IN ZIP_LISTS zkc_dialects zkc_dialect_owners)
  if(dialect STREQUAL "relation")
    continue()
  endif()
  list(APPEND zkc_generated_headers
    include/zkc/Dialect/${owner}/IR/${dialect}Types.h.inc)
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Types.h.inc -gen-typedef-decls -typedefs-dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Types.cpp.inc -gen-typedef-defs -typedefs-dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
mlir_tablegen(include/zkc/Dialect/Operations.h.inc -gen-op-decls
  EXTRA_INCLUDES ${zkc_tablegen_includes})
foreach(dialect owner IN ZIP_LISTS zkc_dialects zkc_dialect_owners)
  mlir_tablegen(include/zkc/Dialect/${owner}/IR/${dialect}Ops.cpp.inc -gen-op-defs
    # A bracketed dot survives the shell the generated command runs in, where
    # a backslash would not.
    "-op-include-regex=^${dialect}[.]" EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
include(cmake/ContractMappings.cmake)
# Record only outputs declared by these TableGen invocations. Reused build
# trees may contain obsolete generated files, which are not valid dependencies.
set(zkc_ir_generated_files ${TABLEGEN_OUTPUT})
list(REMOVE_DUPLICATES zkc_ir_generated_files)
list(JOIN zkc_ir_generated_files "\n" zkc_ir_generated_files)
file(GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/ir-generated-files.txt"
  CONTENT "${zkc_ir_generated_files}\n")
add_public_tablegen_target(ZkcIRGen)
