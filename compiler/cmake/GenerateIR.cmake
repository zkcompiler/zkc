# TableGen needs source and dependency paths independently of C++ targets.
set(zkc_tablegen_includes ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
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
foreach(dialect pir algebra poly plan pcs oracle relation claim)
  mlir_tablegen(include/zkc/Dialect/${dialect}Dialect.h.inc -gen-dialect-decls -dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
  mlir_tablegen(include/zkc/Dialect/${dialect}Dialect.cpp.inc -gen-dialect-defs -dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
foreach(dialect pir algebra poly plan pcs oracle claim)
  mlir_tablegen(include/zkc/Dialect/${dialect}Types.h.inc -gen-typedef-decls -typedefs-dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
  mlir_tablegen(include/zkc/Dialect/${dialect}Types.cpp.inc -gen-typedef-defs -typedefs-dialect=${dialect}
    EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
mlir_tablegen(include/zkc/Dialect/Operations.h.inc -gen-op-decls
  EXTRA_INCLUDES ${zkc_tablegen_includes})
foreach(dialect pir algebra poly plan pcs oracle relation claim)
  mlir_tablegen(include/zkc/Dialect/${dialect}Ops.cpp.inc -gen-op-defs
    # A bracketed dot survives the shell the generated command runs in, where
    # a backslash would not.
    "-op-include-regex=^${dialect}[.]" EXTRA_INCLUDES ${zkc_tablegen_includes})
endforeach()
add_public_tablegen_target(ZkcIRGen)
