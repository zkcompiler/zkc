add_mlir_library(ZkcArtifact
  Artifact.cpp
  SealedGuard.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Artifact

  LINK_LIBS PUBLIC
  MLIRBytecodeReader
  MLIRBytecodeWriter
  MLIRIR
  MLIRRewrite
  ZkcEncoding
  ZkcPir
  ZkcRegistry
  ZkcSemantics
)
# The producer string carries the tool version (see producerString());
# scoped to the one file that spells it rather than the directory.
set_source_files_properties(Artifact.cpp PROPERTIES
  COMPILE_DEFINITIONS ZKC_VERSION_STRING="${PROJECT_VERSION}")
