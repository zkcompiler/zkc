add_mlir_library(ZkcOirViews
  TranscriptSchedule.cpp

  ADDITIONAL_HEADER_DIRS
  ${PROJECT_SOURCE_DIR}/include/zkc/Dialect/Oir

  LINK_LIBS PUBLIC
  MLIRIR
  ZkcEncoding
  ZkcOir
)
