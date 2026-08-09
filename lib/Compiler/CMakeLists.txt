add_mlir_library(ZkcCompiler
  CompilerCore.cpp

  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Compiler

  LINK_COMPONENTS
  Support

  LINK_LIBS PUBLIC
  ZkcSoundness
)

add_mlir_library(ZkcCompilerPir
  PirCompilerProvider.cpp

  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Compiler

  LINK_COMPONENTS
  Support

  LINK_LIBS PUBLIC
  MLIRIR
  ZkcArtifact
  ZkcCompiler
  ZkcEncodingCore
  ZkcPir
  ZkcPirTransforms
  ZkcRegistry
  ZkcSemantics
  ZkcSoundnessPir
)

target_include_directories(ZkcCompilerPir PRIVATE
  ${PROJECT_SOURCE_DIR}/lib
)
