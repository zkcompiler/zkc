add_mlir_library(ZkcRegistry
  ConstructionProfileRegistry.cpp
  ProtocolEnvironment.cpp
  ProtocolVocabulary.cpp
  Rational.cpp
  RegistryFile.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Registry

  LINK_COMPONENTS
  Support

  LINK_LIBS PUBLIC
  ZkcEncodingCore
)
