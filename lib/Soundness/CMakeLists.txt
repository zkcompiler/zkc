add_mlir_library(ZkcSoundness
  DerivationEncoding.cpp
  SealedSoundnessView.cpp
  Signature.cpp
  SignatureEncoding.cpp
  SignatureFile.cpp
  SoundnessCatalog.cpp
  SoundnessEvaluator.cpp
  SoundnessKernel.cpp
  SoundnessProjection.cpp
  SoundnessRuntime.cpp
  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Soundness

  LINK_COMPONENTS
  Support

  LINK_LIBS PUBLIC
  ZkcEncodingCore
  ZkcRegistry
  ZkcRelation
)

add_mlir_library(ZkcSoundnessPir
  PirSoundnessAdapter.cpp
  PARTIAL_SOURCES_INTENDED

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Soundness

  LINK_COMPONENTS
  Support

  LINK_LIBS PUBLIC
  MLIRIR
  ZkcArtifact
  ZkcEncoding
  ZkcPir
  ZkcRegistry
  ZkcSemantics
  ZkcSoundness
)

target_include_directories(ZkcSoundnessPir PRIVATE
  ${PROJECT_SOURCE_DIR}/lib
)
