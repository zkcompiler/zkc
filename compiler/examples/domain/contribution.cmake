# Included at compiler configure time. Native generation stays ordinary MLIR.
set(envelope_include "${CMAKE_CURRENT_LIST_DIR}/include")
set(envelope_generated "${CMAKE_CURRENT_BINARY_DIR}/contributions/envelope")
file(MAKE_DIRECTORY "${envelope_generated}/envelope")
set(envelope_includes "${envelope_include}" "${CMAKE_CURRENT_SOURCE_DIR}/include"
  ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
set(LLVM_TARGET_DEFINITIONS "${envelope_include}/envelope/Native.td")
set(TABLEGEN_OUTPUT)
foreach(kind decls defs)
  if(kind STREQUAL "decls")
    set(suffix h)
  else()
    set(suffix cpp)
  endif()
  mlir_tablegen(contributions/envelope/envelope/EnvelopeDialect.${suffix}.inc
    -gen-dialect-${kind} -dialect=envelope EXTRA_INCLUDES ${envelope_includes})
  mlir_tablegen(contributions/envelope/envelope/EnvelopeTypes.${suffix}.inc
    -gen-typedef-${kind} -typedefs-dialect=envelope EXTRA_INCLUDES ${envelope_includes})
  mlir_tablegen(contributions/envelope/envelope/EnvelopeOps.${suffix}.inc
    -gen-op-${kind} "-op-include-regex=^envelope[.]" EXTRA_INCLUDES ${envelope_includes})
endforeach()
add_public_tablegen_target(EnvelopeGen)
zkc_add_contribution(NAME envelope DEPENDS base
  DECLARATIONS "include/envelope/Declarations.td"
  BINDINGS "include/envelope/Native.td"
  IR_SOURCES "lib/Envelope.cpp" "lib/Adapters.cpp"
  TRANSFORM_SOURCES "lib/Specialization.cpp"
  TRANSFORM_HEADERS "include/envelope/Specialization.h"
  INCLUDE_DIRECTORIES "${envelope_include}" "${envelope_generated}"
  PUBLIC_HEADERS
    "${envelope_generated}/envelope/EnvelopeDialect.h.inc"
    "${envelope_generated}/envelope/EnvelopeTypes.h.inc"
    "${envelope_generated}/envelope/EnvelopeOps.h.inc"
  GENERATED_SOURCES
    "${envelope_generated}/envelope/EnvelopeDialect.cpp.inc"
    "${envelope_generated}/envelope/EnvelopeTypes.cpp.inc"
    "${envelope_generated}/envelope/EnvelopeOps.cpp.inc"
  HEADERS "envelope/Envelope.h"
  DIALECT_CLASSES "::envelope::EnvelopeDialect"
  ADAPTER_OWNERS EnvelopeAdapters GENERATION_TARGETS EnvelopeGen)
