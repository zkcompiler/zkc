set(LLVM_TARGET_DEFINITIONS
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/Installation.td)
tablegen(ZKC include/zkc/Dialect/ContractMappings.cpp.inc -gen-contract-mappings
  EXTRA_INCLUDES ${zkc_tablegen_includes})
