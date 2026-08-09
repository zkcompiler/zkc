set(LIBS
  ZkcArtifact
  ZkcRegistry
  ZkcSoundness
  ZkcSoundnessPir
  ZkcToolUtils
)
add_llvm_executable(zkc-derive zkc-derive.cpp)
llvm_update_compile_flags(zkc-derive)
target_link_libraries(zkc-derive PRIVATE ${LIBS})
