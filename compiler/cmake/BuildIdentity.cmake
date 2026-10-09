# Content identity for compiler-owned semantics. Configure dependencies ensure
# edits also update the identity during an incremental build; host paths and
# timestamps do not enter it. The actual LLVM/MLIR release is retained alongside
# this digest, independently of the repository's tested-version preference.
file(GLOB_RECURSE zkc_identity_inputs CONFIGURE_DEPENDS
  "${CMAKE_CURRENT_SOURCE_DIR}/include/*.h"
  "${CMAKE_CURRENT_SOURCE_DIR}/include/*.td"
  "${CMAKE_CURRENT_SOURCE_DIR}/include/*.def"
  "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.h"
  "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.td"
  "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.def"
  "${CMAKE_CURRENT_SOURCE_DIR}/lib/*.inc"
  "${CMAKE_CURRENT_SOURCE_DIR}/tools/*.h"
  "${CMAKE_CURRENT_SOURCE_DIR}/tools/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/*.cmake"
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/*.in")
list(APPEND zkc_identity_inputs "${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")
list(SORT zkc_identity_inputs)
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${zkc_identity_inputs})
set(zkc_identity_material "zkc.compiler-build\n")
foreach(input IN LISTS zkc_identity_inputs)
  file(RELATIVE_PATH name "${CMAKE_CURRENT_SOURCE_DIR}" "${input}")
  file(SHA256 "${input}" identity)
  string(APPEND zkc_identity_material "${name}:${identity}\n")
endforeach()
string(SHA256 zkc_build_identity "${zkc_identity_material}")
set_source_files_properties(lib/Compiler/Language.cpp PROPERTIES
  COMPILE_DEFINITIONS "ZKC_BUILD_ID=\"${zkc_build_identity}\";ZKC_LLVM_VERSION=\"${LLVM_PACKAGE_VERSION}\"")
