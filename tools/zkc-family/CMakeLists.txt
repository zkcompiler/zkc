set(LIBS
  MLIRIR
  MLIRParser
  ZkcFamily
  ZkcPir
  ZkcRegistry
  ZkcToolUtils
)
add_llvm_executable(zkc-family zkc-family.cpp)
llvm_update_compile_flags(zkc-family)
target_link_libraries(zkc-family PRIVATE ${LIBS})
