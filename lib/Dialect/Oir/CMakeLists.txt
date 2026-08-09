add_mlir_dialect_library(ZkcOir
  OirDialect.cpp
  OirOps.cpp
  OirTypes.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Dialect/Oir

  DEPENDS
  MLIROirOpsIncGen

  LINK_LIBS PUBLIC
  MLIRIR
  MLIRInferTypeOpInterface
)
