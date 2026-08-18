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
#
# The harness is local (`ZkcTest.h`) rather than gtest, because a
# packaged LLVM ships no gtest and a gate that runs only where someone
# built LLVM from source is not a gate.
add_custom_target(ZkcUnitTests)
set_target_properties(ZkcUnitTests PROPERTIES FOLDER "zkc unit tests")

# Plain CMake rather than add_llvm_executable: these link one zkc
# library, the local harness, and LLVMSupport, and none of the
# wrapper's plugin, export, or install handling applies to a test
# binary that never ships.
function(add_zkc_unittest name)
  add_executable(${name} ${ARGN} ${CMAKE_CURRENT_FUNCTION_LIST_DIR}/ZkcTest.cpp)
  llvm_update_compile_flags(${name})
  target_include_directories(${name} PRIVATE
    ${CMAKE_CURRENT_FUNCTION_LIST_DIR})
  target_link_libraries(${name} PRIVATE LLVMSupport)
  add_dependencies(ZkcUnitTests ${name})
  set_target_properties(${name} PROPERTIES FOLDER "zkc unit tests")
endfunction()

add_subdirectory(Encoding)
add_subdirectory(Registry)
add_subdirectory(Relation)
add_subdirectory(Soundness)
