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
  lib/Support/Refusal.cpp
  lib/Support/Json.cpp
  lib/Support/LogicalTree.cpp
)
add_zkc_component(Contracts
  lib/Contracts/Declarations.cpp
  lib/Contracts/Generic.cpp
  lib/Contracts/Requirements.cpp
  lib/Contracts/Variant.cpp
  lib/Contracts/Bindings.cpp
  lib/Contracts/Types.cpp
  lib/Contracts/TypeRepresentations.cpp
  lib/Contracts/Implementations.cpp
  lib/Contracts/Operations.cpp
  lib/Contracts/Mathematical.cpp
  lib/Contracts/Domains.cpp
  lib/Contracts/Kernels.cpp
  lib/Contracts/NativePolicy.cpp
  lib/Contracts/NativeOrigin.cpp
  lib/Contracts/Representations.cpp
)
add_zkc_component(Language
  lib/Language/Types.cpp
  lib/Language/Assets.cpp
  lib/Language/Layout.cpp
  lib/Language/Natural.cpp
  lib/Language/Project.cpp
  lib/Language/Syntax.cpp
  lib/Language/Check.cpp
  lib/Language/TypeCheck.cpp
  lib/Language/Signatures.cpp
  lib/Language/Specifications.cpp
  lib/Language/Entries.cpp
  lib/Language/Capabilities.cpp
  lib/Language/Permissions.cpp
  lib/Language/Conformance.cpp
  lib/Language/BodyCheck.cpp
  lib/Language/Expressions.cpp
  lib/Language/Calls.cpp
  lib/Language/Builtins.cpp
  lib/Language/Kernels.cpp
  lib/Language/Intrinsics.cpp
  lib/Language/Applications.cpp
  lib/Language/Repetition.cpp
  lib/Language/Completion.cpp
  lib/Language/Control.cpp
  lib/Language/Specialize.cpp
)
target_link_libraries(ZkcLanguage PUBLIC ZkcContracts)
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
  lib/Protocol/Construction.cpp
  lib/Protocol/ConstructionAvailability.cpp
  lib/Protocol/ConstructionEmission.cpp
  lib/Protocol/ConstructionResources.cpp
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
add_zkc_component(Claims
  lib/Claims/Trace.cpp
  lib/Claims/Codec.cpp
  lib/Claims/Check.cpp
)
add_zkc_component(IR
  lib/Dialect/Diagnostics.cpp
  lib/Dialect/Table/IR/TableDialect.cpp
  lib/Dialect/Crypto/IR/CryptoDialect.cpp
  lib/Dialect/Local/IR/LocalDialect.cpp
  lib/Dialect/Local/IR/Functions.cpp
  lib/Dialect/Local/IR/Control.cpp
  lib/Dialect/Data/IR/DataDialect.cpp
  lib/Dialect/Algebra/IR/AlgebraDialect.cpp
  lib/Dialect/Algebra/IR/Mathematical.cpp
  lib/Dialect/Bindings.cpp
  lib/Dialect/Claim/IR/ClaimDialect.cpp
  lib/Dialect/Kernels.cpp
  lib/Dialect/MathematicalInterfaces.cpp
  lib/Dialect/LinearContraction.cpp
  lib/Dialect/Algebra/IR/Types.cpp
  lib/Dialect/Polynomial/IR/Types.cpp
  lib/Dialect/Polynomial/IR/Mathematical.cpp
  lib/Dialect/Polynomial/IR/Recipes.cpp
  lib/Dialect/Table/IR/Operations.cpp
  lib/Dialect/SourceInterfaces.cpp
  lib/Dialect/Oracle/IR/OracleDialect.cpp
  lib/Dialect/PCS/IR/PCSDialect.cpp
  lib/Dialect/Protocol/IR/ProtocolDialect.cpp
  lib/Dialect/Protocol/IR/Attributes.cpp
  lib/Dialect/Protocol/Semantics.cpp
  lib/Dialect/Protocol/NativePolicy.cpp
  lib/Dialect/Protocol/IR/Protocol.cpp
  lib/Dialect/Protocol/IR/Mathematical.cpp
  lib/Dialect/Protocol/IR/ResourceOrigins.cpp
  lib/Dialect/Protocol/IR/Applications.cpp
  lib/Dialect/Protocol/IR/Projection.cpp
  lib/Dialect/Table/IR/Physical.cpp
  lib/Dialect/Table/IR/Program.cpp
  lib/Dialect/Protocol/Execution.cpp
  lib/Dialect/Relation/IR/AIR.cpp
  lib/Dialect/Relation/IR/R1CS.cpp
  lib/Dialect/Plan/IR/PlanDialect.cpp
  lib/Dialect/Polynomial/IR/PolynomialDialect.cpp
  lib/Dialect/Registry.cpp
  lib/Dialect/Relation/IR/RelationDialect.cpp
  lib/Dialect/Relation/IR/Declarations.cpp
  lib/Dialect/Relation/IR/Formula.cpp
  lib/Dialect/TableLibrary.cpp
  lib/Dialect/TypeAdapters/Algebra.cpp
  lib/Dialect/TypeAdapters/Commitment.cpp
  lib/Dialect/TypeAdapters/Core.cpp
  lib/Dialect/TypeAdapters/Curve.cpp
  lib/Dialect/TypeAdapters/Polynomial.cpp
  lib/Dialect/TypeAdapters/Registry.cpp
  lib/Dialect/TypeAdapters/Installed.cpp
  lib/Dialect/TypeAdapters/Resources.cpp
  lib/Interfaces/SourceLibrary.cpp
)
add_zkc_component(Translation
  lib/Translation/Language/Emission.cpp
  lib/Translation/Language/Comparison.cpp
  lib/Translation/AIR.cpp
  lib/Translation/ProtocolExport.cpp
  lib/Translation/ProgramVerification.cpp
  lib/Translation/ProtocolImport.cpp
  lib/Translation/R1CS.cpp
  lib/Translation/R1CSSumcheck.cpp
  lib/Translation/Table.cpp
)
add_zkc_component(ClaimTranslation
  lib/ClaimTranslation/Claims.cpp
)
add_zkc_component(Frontend
  lib/Frontend/Analysis.cpp
  lib/Frontend/Carrier/Reader.cpp
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
  lib/Frontend/Resolution/Selectors.cpp
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
  lib/Frontend/Tooling/Dependencies.cpp
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
  lib/Frontend/Loading/Document.cpp
)
add_zkc_component(Transforms
  lib/Conversion/PIRToPlan.cpp
  lib/Conversion/PlanToPhysical.cpp
  lib/Conversion/Bindings.cpp
  lib/Conversion/PhysicalVerification.cpp
  lib/Conversion/Participants.cpp
  lib/Transforms/Algorithms.cpp
  lib/Transforms/AlgorithmVerification.cpp
  lib/Transforms/Participants.cpp
  lib/Transforms/Mathematical.cpp
  lib/Transforms/ProtocolApplications.cpp
  lib/Transforms/MathLowering.cpp
  lib/Transforms/MathRealizations.cpp
  lib/Transforms/PolynomialRecipes.cpp
  lib/Transforms/PolynomialRecipeVerification.cpp
  lib/Transforms/PolynomialLowering.cpp
  lib/Transforms/PolynomialFixing.cpp
  lib/Transforms/MathematicalValues.cpp
  lib/Transforms/PolynomialValues.cpp
  lib/Transforms/MathematicalCorrespondence.cpp
  lib/Transforms/MathematicalPreservation.cpp
  lib/Transforms/MathLoweringVerification.cpp
  lib/Transforms/Storage.cpp
  lib/Transforms/LinearContraction.cpp
  lib/Transforms/TableSimplification.cpp
  lib/Dialect/Relation/Transforms/Deduplicate.cpp
  lib/Target/Selection.cpp
  lib/Target/Catalog.cpp
  lib/Target/PhysicalPlan.cpp
)
add_zkc_component(CompilerCore
  lib/Compiler/Language.cpp
  lib/Compiler/LanguagePackage.cpp
  lib/Compiler/LanguageInterface.cpp
  lib/Compiler/LanguageInterfaceReader.cpp
  lib/Compiler/LanguageInterfaceWriter.cpp
  lib/Compiler/LanguageInterfaceComparison.cpp
  lib/Compiler/LanguageInspection.cpp
  lib/Compiler/Algorithms.cpp
  lib/Compiler/Compilation.cpp
  lib/Compiler/ArtifactJson.cpp
  lib/Compiler/RunVerification.cpp
  lib/Compiler/Run.cpp
  lib/Compiler/PolynomialReduction.cpp
  lib/Compiler/PublicCoin.cpp
  lib/Compiler/NativeDeployment.cpp
  lib/Compiler/NativeProof.cpp
  lib/Compiler/NativeProofVerification.cpp
  lib/Compiler/Claims.cpp
  lib/Compiler/Construction.cpp
  lib/Compiler/Inspection.cpp
  lib/Compiler/Passes.cpp
  lib/Compiler/Pipelines.cpp
  lib/Compiler/Source.cpp
  lib/Compiler/SourceLocations.cpp
)
add_zkc_component(Driver
  lib/Driver/Language.cpp
  lib/Driver/Compiler.cpp
  lib/Driver/Claims.cpp
  lib/Driver/Relations.cpp
  lib/Driver/AIR.cpp
  lib/Driver/Inspection.cpp
)
# Match the external package's LLVM linkage. Mixing its shared LLVM with a
# second static Support copy duplicates process-global LLVM state.
if(LLVM_LINK_LLVM_DYLIB)
  target_link_libraries(ZkcSupport PUBLIC LLVM)
else()
  target_link_libraries(ZkcSupport PUBLIC LLVMSupport)
endif()
add_dependencies(ZkcContracts ZkcContractDeclarationsGen)
target_include_directories(ZkcContracts PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/include)
target_link_libraries(ZkcContracts PUBLIC ZkcSupport)
target_link_libraries(ZkcRelation PUBLIC ZkcContracts)
target_link_libraries(ZkcLanguage PUBLIC ZkcRelation)
target_link_libraries(ZkcProtocol PUBLIC ZkcRelation)
# IR owns mandatory profile validation; carrier adapters depend on that owner.
add_dependencies(ZkcIR ZkcIRGen)
target_include_directories(ZkcIR SYSTEM PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>
  $<BUILD_INTERFACE:${MLIR_INCLUDE_DIRS}>)
target_link_libraries(ZkcClaims PUBLIC ZkcProtocol)
target_link_libraries(ZkcIR PUBLIC ZkcProtocol)
target_link_libraries(ZkcTranslation PUBLIC ZkcIR ZkcLanguage)
target_link_libraries(ZkcClaimTranslation PUBLIC ZkcClaims ZkcIR)
# Follow MLIR's package linkage too: embedding static MLIR archives alongside
# its dylib duplicates MLIR definitions and process-global state.
mlir_target_link_libraries(ZkcIR PUBLIC
  MLIRIR MLIRControlFlowInterfaces MLIRSideEffectInterfaces
  MLIRInferTypeOpInterface MLIRFunctionInterfaces MLIRCallInterfaces
  MLIRFuncDialect MLIRArithDialect MLIRTensorDialect)
target_link_libraries(ZkcFrontend PUBLIC ZkcProtocol)
target_link_libraries(ZkcFrontendLoading PUBLIC ZkcFrontend)
target_link_libraries(ZkcTransforms PUBLIC ZkcIR)
mlir_target_link_libraries(ZkcTransforms PUBLIC
  MLIRPass MLIRTransforms MLIRTransformUtils)
target_link_libraries(ZkcCompilerCore PUBLIC ZkcTransforms ZkcTranslation ZkcFrontend ZkcClaimTranslation)
target_link_libraries(ZkcDriver PUBLIC ZkcCompilerCore ZkcFrontendLoading)
mlir_target_link_libraries(ZkcCompilerCore PUBLIC MLIRParser)
mlir_target_link_libraries(ZkcDriver PUBLIC MLIRParser)
add_library(ZkcCompiler INTERFACE)
add_library(Zkc::Compiler ALIAS ZkcCompiler)
set_target_properties(ZkcCompiler PROPERTIES EXPORT_NAME Compiler)
target_link_libraries(ZkcCompiler INTERFACE ZkcCompilerCore ZkcDriver)
# TableGen consumers query the aggregate's include root directly.
target_include_directories(ZkcCompiler INTERFACE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>)
set(zkc_components ZkcSupport ZkcContracts ZkcLanguage ZkcRelation ZkcProtocol ZkcClaims ZkcIR ZkcTranslation ZkcClaimTranslation ZkcFrontend ZkcFrontendLoading ZkcTransforms ZkcCompilerCore ZkcDriver)

# Record actual target properties for the fast dependency-boundary test.
set(zkc_component_manifest "")
foreach(component ${zkc_components} ZkcCompiler)
  string(APPEND zkc_component_manifest
    "${component}|$<TARGET_PROPERTY:${component},LINK_LIBRARIES>|$<TARGET_PROPERTY:${component},INTERFACE_LINK_LIBRARIES>|$<TARGET_PROPERTY:${component},SOURCES>\n")
endforeach()
file(GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/component-dependencies.txt"
  CONTENT "${zkc_component_manifest}")

# Contributions are selected before generation and linked into one installation.
if(ZKC_CONTRIBUTION_SOURCES)
  target_sources(ZkcIR PRIVATE ${ZKC_CONTRIBUTION_SOURCES})
endif()


if(ZKC_CONTRIBUTION_INCLUDES)
  foreach(directory IN LISTS ZKC_CONTRIBUTION_INCLUDES)
    target_include_directories(ZkcIR PUBLIC $<BUILD_INTERFACE:${directory}>)
  endforeach()
endif()
if(ZKC_CONTRIBUTION_TRANSFORM_SOURCES)
  target_sources(ZkcTransforms PRIVATE ${ZKC_CONTRIBUTION_TRANSFORM_SOURCES})
endif()
if(ZKC_CONTRIBUTION_GENERATION_TARGETS)
  add_dependencies(ZkcIR ${ZKC_CONTRIBUTION_GENERATION_TARGETS})
  add_dependencies(ZkcTransforms ${ZKC_CONTRIBUTION_GENERATION_TARGETS})
endif()
# Install exactly the admitted public inventory; generated headers are known
# before they exist, and later unregistered outputs cannot enter via a glob.
foreach(header installed_path IN ZIP_LISTS ZKC_CONTRIBUTION_PUBLIC_HEADER_FILES ZKC_CONTRIBUTION_PUBLIC_HEADER_PATHS)
  get_filename_component(directory "${installed_path}" DIRECTORY)
  get_filename_component(basename "${installed_path}" NAME)
  install(FILES "${header}" DESTINATION "include/${directory}" RENAME "${basename}")
endforeach()

# Forward references and aliases now resolve against every core component.
zkc_link_contribution_libraries()

include(${CMAKE_CURRENT_LIST_DIR}/BuildIdentity.cmake)
