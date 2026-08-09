add_mlir_dialect(PirOps pir)

set(LLVM_TARGET_DEFINITIONS PirOps.td)
mlir_tablegen(PirOpsEnums.h.inc -gen-enum-decls)
mlir_tablegen(PirOpsEnums.cpp.inc -gen-enum-defs)
add_public_tablegen_target(ZkcPirEnumsIncGen)

set(LLVM_TARGET_DEFINITIONS PirInterfaces.td)
mlir_tablegen(PirInterfaces.h.inc -gen-op-interface-decls)
mlir_tablegen(PirInterfaces.cpp.inc -gen-op-interface-defs)
add_public_tablegen_target(ZkcPirInterfacesIncGen)

add_subdirectory(Transforms)

