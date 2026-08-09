set(LIBS
  MLIRParser
  MLIRPass
  ZkcArtifact
  ZkcPir
  ZkcPirTransforms
  ZkcToolUtils
)
add_llvm_executable(zkc-seal zkc-seal.cpp)
llvm_update_compile_flags(zkc-seal)
target_link_libraries(zkc-seal PRIVATE ${LIBS})
