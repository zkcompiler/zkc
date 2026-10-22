option(ZKC_ENABLE_HEIR "Use the qualified HEIR package for quotient calculations" OFF)
target_sources(ZkcTransforms PRIVATE
  lib/Transforms/Kernel/Quotient.cpp
  lib/Transforms/Kernel/QuotientVerification.cpp)
file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/heir-dependency.txt" "${ZKC_ENABLE_HEIR}\n")
if(ZKC_ENABLE_HEIR)
  find_package(ZkcHeirArithmetic 0.0.0 EXACT REQUIRED CONFIG)
  file(READ "${CMAKE_CURRENT_SOURCE_DIR}/external/heir/pins.json" pins)
  string(JSON ZKC_HEIR_REVISION GET "${pins}" heir revision)
  string(JSON ZKC_HEIR_PATCH_SHA256 GET "${pins}" patches 0 sha256)
  if(NOT ZkcHeirArithmetic_HEIR_REVISION STREQUAL ZKC_HEIR_REVISION OR
      NOT ZkcHeirArithmetic_PATCH_SHA256 STREQUAL ZKC_HEIR_PATCH_SHA256)
    message(FATAL_ERROR "The installed HEIR package does not match external/heir/pins.json")
  endif()
  target_compile_definitions(ZkcTransforms PRIVATE ZKC_ENABLE_HEIR=1)
  target_link_libraries(ZkcTransforms PRIVATE ZkcHeir::Admission)
endif()
