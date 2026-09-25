# Each translation unit has one owner. ZkcCompiler is an interface aggregate;
# it never recompiles component sources.
separate_arguments(zkc_llvm_definitions NATIVE_COMMAND "${LLVM_DEFINITIONS}")
function(add_zkc_component name)
  add_library(Zkc${name} ${ARGN})
  add_library(Zkc::${name} ALIAS Zkc${name})
  set_target_properties(Zkc${name} PROPERTIES EXPORT_NAME ${name}
    INSTALL_RPATH_USE_LINK_PATH TRUE INSTALL_RPATH "$ORIGIN")
  target_compile_options(Zkc${name} PRIVATE -Wall -Wextra -Werror)
  if(CMAKE_SYSTEM_NAME STREQUAL "Linux" AND NOT ZKC_ENABLE_SANITIZERS)
    # Sanitized shared libraries leave runtime hooks for the final executable.
    # Ordinary shared libraries resolve symbols through their declared links.
    target_link_options(Zkc${name} PRIVATE "LINKER:-z,defs")
  endif()
  target_compile_options(Zkc${name} PUBLIC ${zkc_llvm_definitions})
  target_compile_features(Zkc${name} PUBLIC cxx_std_17)
  target_include_directories(Zkc${name} PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>)
  target_include_directories(Zkc${name} SYSTEM PUBLIC
    $<BUILD_INTERFACE:${LLVM_INCLUDE_DIRS}>)
endfunction()

add_zkc_component(Support
  lib/Support/Input.cpp
  lib/Support/Json.cpp
)
add_zkc_component(Contracts
  lib/Contracts/Generic.cpp
  lib/Contracts/Requirements.cpp
  lib/Contracts/Variant.cpp
  lib/Contracts/Bindings.cpp
  lib/Contracts/Operations.cpp
  lib/Contracts/Domains.cpp
  lib/Contracts/Kernels.cpp
  lib/Contracts/Representations.cpp
)
add_zkc_component(Relation
  lib/Relation/R1CS.cpp
  lib/Relation/R1CSBinary.cpp
  lib/Relation/AIR.cpp
  lib/Relation/AIRPolynomial.cpp
  lib/Relation/Matrices.cpp
)
add_zkc_component(Protocol
  lib/Analysis/Obligations.cpp
  lib/Analysis/OracleAccess.cpp
  lib/Analysis/PolynomialDomains.cpp
  lib/Protocol/Instantiation.cpp
  lib/Protocol/Admission.cpp
  lib/Protocol/PhysicalOptions.cpp
  lib/Source/Relations.cpp
  lib/Source/RelationLowering.cpp
  lib/Source/Decode.cpp
  lib/Source/Document.cpp
  lib/Source/Encode.cpp
  lib/Source/Execution.cpp
  lib/Source/Model.cpp
  lib/Source/Resolution.cpp
  lib/Source/Structure.cpp
  lib/Source/Snapshot.cpp
)
add_zkc_component(IR
  lib/Dialect/Diagnostics.cpp
  lib/Dialect/Algebra/IR/AlgebraDialect.cpp
  lib/Dialect/Bindings.cpp
  lib/Dialect/Claim/IR/ClaimDialect.cpp
  lib/Dialect/Kernels.cpp
  lib/Dialect/LinearContraction.cpp
  lib/Dialect/Operations.cpp
  lib/Dialect/Oracle/IR/OracleDialect.cpp
  lib/Dialect/PCS/IR/PCSDialect.cpp
  lib/Dialect/PIR/IR/PIRDialect.cpp
  lib/Dialect/PIR/IR/Protocol.cpp
  lib/Dialect/Plan/IR/Physical.cpp
  lib/Dialect/Plan/IR/PlanDialect.cpp
  lib/Dialect/Polynomial/IR/PolynomialDialect.cpp
  lib/Dialect/Registry.cpp
  lib/Dialect/Relation/IR/RelationDialect.cpp
  lib/Dialect/TableLibrary.cpp
  lib/Interfaces/SourceLibrary.cpp
  lib/Translation/AIR.cpp
  lib/Translation/ProtocolExport.cpp
  lib/Translation/ProtocolImport.cpp
  lib/Translation/R1CS.cpp
  lib/Translation/Table.cpp
)
add_zkc_component(Frontend
  lib/Frontend/Analysis.cpp
  lib/Frontend/Compile.cpp
  lib/Frontend/Diagnostic.cpp
  lib/Frontend/Input.cpp
  lib/Frontend/Instantiation/Construction.cpp
  lib/Frontend/Instantiation/Select.cpp
  lib/Frontend/Library/Body.cpp
  lib/Frontend/Library/Conformance.cpp
  lib/Frontend/Library/Identity.cpp
  lib/Frontend/Library/Interface.cpp
  lib/Frontend/Library/Link.cpp
  lib/Frontend/Library/Representation.cpp
  lib/Frontend/Library/Static.cpp
  lib/Frontend/Library/Types.cpp
  lib/Frontend/Library/World.cpp
  lib/Frontend/Lowering/Admission.cpp
  lib/Frontend/Lowering/Library.cpp
  lib/Frontend/Lowering/LibrarySource.cpp
  lib/Frontend/Lowering/PIR.cpp
  lib/Frontend/Model/Module.cpp
  lib/Frontend/Project.cpp
  lib/Frontend/Resolution/Environment.cpp
  lib/Frontend/Resolution/Names.cpp
  lib/Frontend/Resolution/Project.cpp
  lib/Frontend/Semantics/Aggregates.cpp
  lib/Frontend/Semantics/Analysis.cpp
  lib/Frontend/Semantics/Body.cpp
  lib/Frontend/Semantics/Check.cpp
  lib/Frontend/Semantics/Libraries.cpp
  lib/Frontend/Semantics/LibraryEntries.cpp
  lib/Frontend/Semantics/Local.cpp
  lib/Frontend/Semantics/Protocols.cpp
  lib/Frontend/Semantics/Provenance.cpp
  lib/Frontend/Static/Naturals.cpp
  lib/Frontend/Syntax/Captures.cpp
  lib/Frontend/Syntax/Format.cpp
  lib/Frontend/Syntax/Lexer.cpp
  lib/Frontend/Syntax/Parser.cpp
  lib/Frontend/Tooling/Analysis.cpp
  lib/Frontend/Tooling/Calls.cpp
  lib/Frontend/Tooling/Inspection.cpp
  lib/Frontend/Tooling/Libraries.cpp
  lib/Frontend/Tooling/Lints.cpp
  lib/Frontend/Tooling/Printer.cpp
  lib/Frontend/Tooling/Syntax.cpp
)
add_zkc_component(FrontendLoading
  lib/Frontend/Loading/Capture.cpp
  lib/Frontend/Loading/Relations.cpp
)
add_zkc_component(CompilerCore
  lib/Claims/Trace.cpp
  lib/Claims/Codec.cpp
  lib/Claims/Check.cpp
  lib/Claims/IR.cpp
  lib/Claims/Driver.cpp
  lib/Compiler/Driver.cpp
  lib/Compiler/Inspection.cpp
  lib/Compiler/Pipelines.cpp
  lib/Compiler/SourceLocations.cpp
  lib/Conversion/PIRToPlan.cpp
  lib/Conversion/PlanToPhysical.cpp
  lib/Protocol/Algorithms.cpp
  lib/Protocol/BindingPhysical.cpp
  lib/Protocol/Construction.cpp
  lib/Protocol/ConstructionAvailability.cpp
  lib/Protocol/ConstructionEmission.cpp
  lib/Protocol/ConstructionResources.cpp
  lib/Protocol/Physical.cpp
  lib/Protocol/Storage.cpp
  lib/Protocol/Projection.cpp
  lib/Relation/AIRCommands.cpp
  lib/Relation/Driver.cpp
  lib/Transforms/Passes.cpp
  lib/Transforms/LinearContraction.cpp
  lib/Transforms/TableSimplification.cpp
  lib/Dialect/Relation/Transforms/Deduplicate.cpp
)
# Match the external package's LLVM linkage. Mixing its shared LLVM with a
# second static Support copy duplicates process-global LLVM state.
if(LLVM_LINK_LLVM_DYLIB)
  target_link_libraries(ZkcSupport PUBLIC LLVM)
else()
  target_link_libraries(ZkcSupport PUBLIC LLVMSupport)
endif()
target_link_libraries(ZkcContracts PUBLIC ZkcSupport)
target_link_libraries(ZkcRelation PUBLIC ZkcContracts)
target_link_libraries(ZkcProtocol PUBLIC ZkcRelation)
# IR translation and mandatory verification are a coordinated lower library.
add_dependencies(ZkcIR ZkcIRGen)
target_include_directories(ZkcIR SYSTEM PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>
  $<BUILD_INTERFACE:${MLIR_INCLUDE_DIRS}>)
target_link_libraries(ZkcIR PUBLIC ZkcProtocol
  MLIRIR MLIRControlFlowInterfaces MLIRSideEffectInterfaces
  MLIRInferTypeOpInterface MLIRFuncDialect)
target_link_libraries(ZkcFrontend PUBLIC ZkcProtocol)
target_link_libraries(ZkcFrontendLoading PUBLIC ZkcFrontend)
# Passes and application workflows separate in the next phase.
target_link_libraries(ZkcCompilerCore PUBLIC ZkcIR ZkcFrontendLoading
  MLIRParser MLIRPass MLIRTransforms MLIRTransformUtils)
add_library(ZkcCompiler INTERFACE)
add_library(Zkc::Compiler ALIAS ZkcCompiler)
set_target_properties(ZkcCompiler PROPERTIES EXPORT_NAME Compiler)
target_link_libraries(ZkcCompiler INTERFACE ZkcCompilerCore)
# TableGen consumers query the aggregate's include root directly.
target_include_directories(ZkcCompiler INTERFACE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>)
set(zkc_components ZkcSupport ZkcContracts ZkcRelation ZkcProtocol ZkcIR ZkcFrontend ZkcFrontendLoading ZkcCompilerCore)

# Record actual target properties for the fast dependency-boundary test.
set(zkc_component_manifest "")
foreach(component ${zkc_components} ZkcCompiler)
  string(APPEND zkc_component_manifest
    "${component}|$<TARGET_PROPERTY:${component},LINK_LIBRARIES>|$<TARGET_PROPERTY:${component},INTERFACE_LINK_LIBRARIES>|$<TARGET_PROPERTY:${component},SOURCES>\n")
endforeach()
file(GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/component-dependencies.txt"
  CONTENT "${zkc_component_manifest}")
