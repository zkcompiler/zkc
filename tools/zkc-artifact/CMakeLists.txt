set(LIBS
  ZkcArtifact
  ZkcToolUtils
)
add_llvm_executable(zkc-artifact zkc-artifact.cpp)
llvm_update_compile_flags(zkc-artifact)
target_link_libraries(zkc-artifact PRIVATE ${LIBS})
