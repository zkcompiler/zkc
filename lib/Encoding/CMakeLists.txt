# The canonical byte layer (JSON writer, unique-key parser, domain rule)
# has no MLIR dependency: the registry library computes contract digests
# over it, so it stays Support-only. The attribute conversion that does
# read MLIR lives in ZkcEncoding below, where the encoder is — the claim
# here is checked by the unit tests, which link this library alone.
add_mlir_library(ZkcEncodingCore
  CanonicalJson.cpp
  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Encoding

  LINK_COMPONENTS
  Support
)

add_mlir_library(ZkcEncoding
  AttributeJson.cpp
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
