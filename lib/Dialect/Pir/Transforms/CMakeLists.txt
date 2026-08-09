add_mlir_library(ZkcPirTransforms
  PirBatchOpen.cpp
  PirLink.cpp
  PirProject.cpp
  PirSeal.cpp
  ProtocolArtifacts.cpp
  SpineEditor.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Dialect/Pir/Transforms

  DEPENDS
  ZkcPirPassIncGen

  LINK_LIBS PUBLIC
  MLIRIR
  MLIRPass
  MLIRTransformUtils
  ZkcArtifact
  ZkcEncoding
  ZkcOir
  ZkcPir
  ZkcRegistry
  ZkcSemantics
)

target_include_directories(ZkcPirTransforms PRIVATE
  ${PROJECT_SOURCE_DIR}/lib
)
