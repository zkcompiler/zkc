add_mlir_library(ZkcToolUtils
  ToolUtils.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Tools

  LINK_LIBS PUBLIC
  MLIRIR
  MLIRParser
)
