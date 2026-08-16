add_mlir_library(ZkcSemantics
  ConstructionGraph.cpp
  LinkEngine.cpp
  ProtocolFacts.cpp
  CheckLayout.cpp
  ReductionClosure.cpp
  SealBattery.cpp
  SealEngine.cpp
  TerminalClosure.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Semantics

  LINK_LIBS PUBLIC
  MLIRIR
  ZkcEncoding
  ZkcPir
  ZkcRegistry
)
