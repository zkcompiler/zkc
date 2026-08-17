# Unit tests for the pure cores: exact arithmetic, byte formats, and the
# parsers that read untrusted input. Everything else in this repository
# is judged end to end through a tool, which is right for judgments over
# whole artifacts and wrong for a total function over a rational — a
# property that holds for every input is not evidence a corpus can carry.
#
# Only functions with no MLIRContext belong here. That is not a
# limitation but the selection rule: those are the pieces whose
# correctness is a mathematical statement rather than a statement about
# a compiled artifact.
add_custom_target(ZkcUnitTests)
set_target_properties(ZkcUnitTests PROPERTIES FOLDER "zkc unit tests")

# Plain CMake rather than add_llvm_executable: these link one zkc
# library, gtest, and LLVMSupport, and none of the wrapper's plugin,
# export, or install handling applies to a test binary that never
# ships.
function(add_zkc_unittest name)
  add_executable(${name} ${ARGN})
  llvm_update_compile_flags(${name})
  target_include_directories(${name} SYSTEM PRIVATE
    ${LLVM_MAIN_SRC_DIR}/utils/unittest/googletest/include
    ${LLVM_MAIN_SRC_DIR}/third-party/unittest/googletest/include)
  target_link_libraries(${name} PRIVATE llvm_gtest llvm_gtest_main LLVMSupport)
  add_dependencies(ZkcUnitTests ${name})
  set_target_properties(${name} PROPERTIES FOLDER "zkc unit tests")
endfunction()

add_subdirectory(Encoding)
add_subdirectory(Registry)
add_subdirectory(Relation)
