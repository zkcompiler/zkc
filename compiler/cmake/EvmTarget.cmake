# The EVM target declaration is shared with the Rust SDK, the deployed runner
# and the harness. The configure step validates it and projects the compiler's
# tables; the installed zkc/Compiler/Evm.h includes the projection. The
# declaration stays outside the logical catalog: it describes the target ABI,
# tool configuration, fork mapping, deployment ceilings and revert classes.
find_package(Python3 REQUIRED COMPONENTS Interpreter)
set(zkc_evm_target_directory "${CMAKE_CURRENT_SOURCE_DIR}/../common/targets")
get_filename_component(zkc_evm_target_directory "${zkc_evm_target_directory}" ABSOLUTE)
set(zkc_evm_target_inputs
  "${zkc_evm_target_directory}/evm.json"
  "${zkc_evm_target_directory}/generate.py")
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${zkc_evm_target_inputs})
execute_process(COMMAND "${Python3_EXECUTABLE}" "${zkc_evm_target_directory}/generate.py"
  --source "${zkc_evm_target_directory}/evm.json"
  --output "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Target/Evm/Declaration.h.inc"
  RESULT_VARIABLE zkc_evm_target_result ERROR_VARIABLE zkc_evm_target_error)
if(NOT zkc_evm_target_result EQUAL 0)
  message(FATAL_ERROR "EVM target declaration projection failed: ${zkc_evm_target_error}")
endif()
list(APPEND zkc_generated_headers include/zkc/Target/Evm/Declaration.h.inc)

# The physical EVM dialect is target-owned and independent of the logical
# catalog's dialect generator.
set(TABLEGEN_OUTPUT)
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Dialect/Evm")
set(LLVM_TARGET_DEFINITIONS include/zkc/Dialect/Evm/Ops.td)
mlir_tablegen(include/zkc/Dialect/Evm/Ops.h.inc -gen-op-decls
  EXTRA_INCLUDES ${zkc_tablegen_includes})
mlir_tablegen(include/zkc/Dialect/Evm/Ops.cpp.inc -gen-op-defs
  EXTRA_INCLUDES ${zkc_tablegen_includes})
add_public_tablegen_target(ZkcEvmIRGen)
list(APPEND zkc_generated_headers include/zkc/Dialect/Evm/Ops.h.inc)
