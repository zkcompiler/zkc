set(LIBS
  ZkcArtifact
  ZkcEncodingCore
  ZkcRegistry
  ZkcRelation
  ZkcSoundness
  ZkcSoundnessPir
  ZkcToolUtils
)
add_llvm_executable(zkc-relation zkc-relation.cpp)
llvm_update_compile_flags(zkc-relation)
target_link_libraries(zkc-relation PRIVATE ${LIBS})
