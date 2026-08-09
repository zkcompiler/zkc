set(LIBS
  ZkcEncodingCore
  ZkcRegistry
  ZkcSoundness
  ZkcToolUtils
)
add_llvm_executable(zkc-registry-lint zkc-registry-lint.cpp)
llvm_update_compile_flags(zkc-registry-lint)
target_link_libraries(zkc-registry-lint PRIVATE ${LIBS})
