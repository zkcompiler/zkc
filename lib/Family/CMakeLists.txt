# Family instance emission (the unjudged half of family generation):
# description parsing + deterministic contract/spine emitters. No MLIR
# dependency — the consumers (CLI, sweep) re-parse the emitted spine
# through the dialect themselves.
add_mlir_library(ZkcFamily
  FriFamily.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Family

  LINK_COMPONENTS
  Support

  LINK_LIBS PUBLIC
  ZkcEncodingCore
  ZkcRegistry
)
