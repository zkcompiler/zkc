set(LIBS
  MLIROptLib
  MLIRFuncDialect
  MLIRTransforms
  ZkcArtifact
  ZkcOir
  ZkcPir
  ZkcPirTransforms
  ZkcToolUtils
)
add_llvm_executable(zkc-opt zkc-opt.cpp)
llvm_update_compile_flags(zkc-opt)
target_link_libraries(zkc-opt PRIVATE ${LIBS})
mlir_check_all_link_libraries(zkc-opt)
