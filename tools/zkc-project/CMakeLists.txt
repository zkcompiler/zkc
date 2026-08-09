set(LIBS
  ZkcArtifact
  ZkcPirTransforms
  ZkcRegistry
  ZkcToolUtils
)
add_llvm_executable(zkc-project zkc-project.cpp)
llvm_update_compile_flags(zkc-project)
target_link_libraries(zkc-project PRIVATE ${LIBS})
