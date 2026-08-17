add_mlir_library(ZkcRelation
  AnchorProjection.cpp
  R1csHeader.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Relation

  LINK_COMPONENTS
  Support
)
