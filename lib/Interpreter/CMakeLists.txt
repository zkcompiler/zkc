add_mlir_library(ZkcInterpreter
  ExecutionProfile.cpp
  Interpreter.cpp
  Plonky3Profile.cpp
  ToyProfile.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Interpreter

  LINK_LIBS PUBLIC
  MLIRIR
  ZkcEncoding
  ZkcOir
)
