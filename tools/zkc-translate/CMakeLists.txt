set(LIBS
  MLIRIR
  MLIRParser
  ZkcEncoding
  ZkcInterpreter
  ZkcOir
  ZkcOirViews
  ZkcPir
  ZkcToolUtils
)
add_llvm_executable(zkc-translate zkc-translate.cpp)
llvm_update_compile_flags(zkc-translate)
target_link_libraries(zkc-translate PRIVATE ${LIBS})
