set(LIBS
  MLIRIR
  MLIRParser
  ZkcInterpreter
  ZkcPirTransforms
  ZkcRegistry
  ZkcEncoding
  ZkcOir
  ZkcPir
  ZkcToolUtils
)
add_llvm_executable(zkc-run zkc-run.cpp)
llvm_update_compile_flags(zkc-run)
target_link_libraries(zkc-run PRIVATE ${LIBS})
