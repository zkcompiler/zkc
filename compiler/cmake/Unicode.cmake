# Shared profile inputs are ordinary, hash-checked source dependencies. Neither
# configure nor generation downloads anything or consults host Unicode tables.
set(ZKC_UNICODE_SOURCE_DIR "${CMAKE_CURRENT_LIST_DIR}/../../common/unicode")
get_filename_component(ZKC_UNICODE_SOURCE_DIR "${ZKC_UNICODE_SOURCE_DIR}" ABSOLUTE)
file(READ "${ZKC_UNICODE_SOURCE_DIR}/manifest.json" zkc_unicode_manifest)
string(JSON ZKC_UTF8PROC_VERSION GET "${zkc_unicode_manifest}" normalizers cpp version)
if(TARGET utf8proc::utf8proc AND
    (NOT DEFINED utf8proc_VERSION OR
     NOT utf8proc_VERSION VERSION_EQUAL ZKC_UTF8PROC_VERSION))
  message(FATAL_ERROR "Loaded utf8proc does not match ${ZKC_UTF8PROC_VERSION}")
endif()
find_package(utf8proc ${ZKC_UTF8PROC_VERSION} EXACT REQUIRED CONFIG)
find_package(Python3 REQUIRED COMPONENTS Interpreter)
set(zkc_unicode_inputs
  "${ZKC_UNICODE_SOURCE_DIR}/manifest.json"
  "${ZKC_UNICODE_SOURCE_DIR}/generate.py"
  "${ZKC_UNICODE_SOURCE_DIR}/LICENSE.txt")
foreach(name DerivedCoreProperties PropList UnicodeData BidiBrackets NormalizationTest)
  list(APPEND zkc_unicode_inputs "${ZKC_UNICODE_SOURCE_DIR}/17.0.0/${name}.txt")
endforeach()
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${zkc_unicode_inputs})
set(zkc_unicode_header "${CMAKE_CURRENT_BINARY_DIR}/generated/SourceNameData.inc")
add_custom_command(OUTPUT "${zkc_unicode_header}"
  COMMAND "${Python3_EXECUTABLE}" "${ZKC_UNICODE_SOURCE_DIR}/generate.py"
    --data "${ZKC_UNICODE_SOURCE_DIR}" --output "${zkc_unicode_header}"
  DEPENDS ${zkc_unicode_inputs}
  VERBATIM)
add_custom_target(ZkcSourceNameDataGen DEPENDS "${zkc_unicode_header}")
