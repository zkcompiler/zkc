# The authored neutral catalog is shared with Rust. This projection needs only
# the existing Python build tool; the compiler never invokes Cargo. The native
# TableGen backends independently validate the projected declarations. The
# declarations and their native installation form one catalog package: they
# are validated together, and the physical records get their own file.
find_package(Python3 REQUIRED COMPONENTS Interpreter)
set(zkc_catalog_directory "${CMAKE_CURRENT_SOURCE_DIR}/../common/catalog")
set(zkc_catalog_inputs
  "${zkc_catalog_directory}/declarations.json"
  "${zkc_catalog_directory}/installation.json"
  "${zkc_catalog_directory}/generate.py"
  "${zkc_catalog_directory}/tablegen.py"
  "${zkc_catalog_directory}/descriptor_schemes.py")
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${zkc_catalog_inputs})
execute_process(COMMAND "${Python3_EXECUTABLE}" "${zkc_catalog_directory}/generate.py"
  --source "${zkc_catalog_directory}/declarations.json"
  --installation "${zkc_catalog_directory}/installation.json"
  --output "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts"
  RESULT_VARIABLE zkc_catalog_result ERROR_VARIABLE zkc_catalog_error)
if(NOT zkc_catalog_result EQUAL 0)
  message(FATAL_ERROR "Shared catalog projection failed: ${zkc_catalog_error}")
endif()
install(FILES
  "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts/Catalog.td"
  "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts/Mathematical.td"
  "${CMAKE_CURRENT_BINARY_DIR}/include/zkc/Contracts/NativeInstallation.td"
  DESTINATION include/zkc/Contracts)
