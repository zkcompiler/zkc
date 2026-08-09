# The canonical byte layer (JSON writer + domain) has no MLIR
# dependency: the registry library computes contract digests over it, so
# it stays Support-only.
add_mlir_library(ZkcEncodingCore
  CanonicalJson.cpp
  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Encoding

  LINK_COMPONENTS
  Support
)

add_mlir_library(ZkcEncoding
  CanonicalEncoder.cpp
  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Encoding

  LINK_LIBS PUBLIC
  MLIRIR
  ZkcEncodingCore
  ZkcOir
  ZkcPir
)
