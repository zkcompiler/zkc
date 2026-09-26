# Included by GenerateIR.cmake before it records TABLEGEN_OUTPUT and declares
# ZkcIRGen. This is a build-only generator; it is not an installed SDK tool and
# does not add a runtime dependency to Contracts or IR.
add_executable(zkc-tblgen tools/zkc-tblgen.cpp)
target_include_directories(zkc-tblgen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
separate_arguments(zkc_tablegen_definitions NATIVE_COMMAND "${LLVM_DEFINITIONS}")
target_compile_options(zkc-tblgen PRIVATE ${zkc_tablegen_definitions}
  -Wall -Wextra -Werror)
target_link_libraries(zkc-tblgen PRIVATE LLVMTableGen LLVMSupport)
set(ZKC_TABLEGEN_EXE $<TARGET_FILE:zkc-tblgen>)
set(ZKC_TABLEGEN_TARGET zkc-tblgen)
set(LLVM_TARGET_DEFINITIONS include/zkc/Dialect/IR.td)
tablegen(ZKC include/zkc/Dialect/ContractMappings.cpp.inc
  EXTRA_INCLUDES ${zkc_tablegen_includes})
