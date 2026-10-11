# One build-only tool, with independent actions for neutral declarations and ODS.
add_executable(zkc-tblgen tools/zkc-tblgen.cpp tools/TableGen/Declarations.cpp
  tools/TableGen/Contributions.cpp tools/TableGen/TypeBindings.cpp
  tools/TableGen/Mathematical.cpp tools/TableGen/Recipes.cpp)
target_include_directories(zkc-tblgen SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
separate_arguments(zkc_tablegen_definitions NATIVE_COMMAND "${LLVM_DEFINITIONS}")
target_compile_options(zkc-tblgen PRIVATE ${zkc_tablegen_definitions}
  -Wall -Wextra -Werror)
target_link_libraries(zkc-tblgen PRIVATE LLVMTableGen LLVMSupport)
set(ZKC_TABLEGEN_EXE $<TARGET_FILE:zkc-tblgen>)
set(ZKC_TABLEGEN_TARGET zkc-tblgen)
# Do not inherit IR generation outputs or MLIR TableGen include paths.
set(zkc_saved_tablegen_output ${TABLEGEN_OUTPUT})
set(TABLEGEN_OUTPUT)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts)
set(LLVM_TARGET_DEFINITIONS
  ${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts/Installation.td)
tablegen(ZKC include/zkc/Contracts/Declarations.cpp.inc
  -gen-contract-declarations EXTRA_INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_BINARY_DIR}/include ${ZKC_CONTRIBUTION_INCLUDES})
tablegen(ZKC include/zkc/Contracts/Mathematical.inc
  -gen-mathematical-declarations EXTRA_INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_BINARY_DIR}/include ${ZKC_CONTRIBUTION_INCLUDES})
add_public_tablegen_target(ZkcContractDeclarationsGen)
install(FILES "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts/Mathematical.inc"
  DESTINATION include/zkc/Contracts)
set(TABLEGEN_OUTPUT)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/generated/Transforms)
set(LLVM_TARGET_DEFINITIONS
  ${CMAKE_CURRENT_SOURCE_DIR}/lib/Transforms/MathematicalRecipes.td)
tablegen(ZKC generated/Transforms/MathematicalRecipes.inc
  -gen-mathematical-recipes EXTRA_INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_BINARY_DIR}/include ${ZKC_CONTRIBUTION_INCLUDES})
add_public_tablegen_target(ZkcMathematicalRecipesGen)
set(TABLEGEN_OUTPUT ${zkc_saved_tablegen_output})
unset(zkc_saved_tablegen_output)
