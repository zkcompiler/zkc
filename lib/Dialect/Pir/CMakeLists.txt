add_subdirectory(Transforms)

add_mlir_dialect_library(ZkcPir
  PirDialect.cpp
  PirOps.cpp
  PirTypes.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Dialect/Pir

  DEPENDS
  MLIRPirOpsIncGen
  ZkcPirEnumsIncGen
  ZkcPirInterfacesIncGen

  LINK_LIBS PUBLIC
  MLIRIR
  MLIRInferTypeOpInterface
  MLIRSideEffectInterfaces
)
