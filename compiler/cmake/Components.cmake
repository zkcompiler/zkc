# Each translation unit has one owner. Compiler owns compilation; Driver owns
# CLI parsing and input loading.
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
  lib/Contracts/MathematicalFacts.cpp
  lib/Contracts/FiniteCardinality.cpp
  lib/Contracts/RingExpression.cpp
  lib/Contracts/RingSharing.cpp
  lib/Contracts/Numerical.cpp
  lib/Contracts/Domains.cpp
  lib/Contracts/OperationShapes.cpp
  lib/Contracts/NativePolicy.cpp
  lib/Contracts/SourceTerms.cpp
  lib/Contracts/NativeOrigin.cpp
  lib/Contracts/Representations.cpp
)
file(READ "${CMAKE_CURRENT_SOURCE_DIR}/lib/Language/Prelude.zkc" zkc_prelude_source)
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
  "${CMAKE_CURRENT_SOURCE_DIR}/lib/Language/Prelude.zkc")
configure_file(lib/Language/Prelude.inc.in generated/Prelude.inc @ONLY)
include(${CMAKE_CURRENT_LIST_DIR}/Unicode.cmake)
add_zkc_component(Language
  lib/Language/Names.cpp
  lib/Language/Diagnostics.cpp
  lib/Language/Inspection.cpp
  lib/Language/NotationInspection.cpp
  lib/Language/NotationRecords.cpp
  lib/Language/SourceTerms.cpp
  lib/Language/Types.cpp
  lib/Language/Assets.cpp
  lib/Language/AssetProperties.cpp
  lib/Language/AssetClosure.cpp
  lib/Language/Layout.cpp
  lib/Language/Natural.cpp
  lib/Language/Project.cpp
  lib/Language/Syntax.cpp
  lib/Language/Arguments.cpp
  lib/Language/Elaboration.cpp
  lib/Language/Booleans.cpp
  lib/Language/Check.cpp
  lib/Language/Imports.cpp
  lib/Language/Notation.cpp
  lib/Language/Operators.cpp
  lib/Language/Semantics.cpp
  lib/Language/KernelSignatures.cpp
  lib/Language/BindingWitness.cpp
  lib/Language/Primitives.cpp
  lib/Language/IntrinsicSignatures.cpp
  lib/Language/SemanticContracts.cpp
  lib/Language/TypeCheck.cpp
  lib/Language/Signatures.cpp
  lib/Language/Specifications.cpp
  lib/Language/SourceClaims.cpp
  lib/Language/RelationABI.cpp
  lib/Language/Entries.cpp
  lib/Language/Constructions.cpp
  lib/Language/ConstructionCodecs.cpp
  lib/Language/EntrySetups.cpp
  lib/Language/Capabilities.cpp
  lib/Language/Permissions.cpp
  lib/Language/Admission.cpp
  lib/Language/Conformance.cpp
  lib/Language/Resolution.cpp
  lib/Language/ResourceUsage.cpp
  lib/Language/UsagePlan.cpp
  lib/Language/UsageRequirements.cpp
  lib/Language/UsageInference.cpp
  lib/Language/Bindings.cpp
  lib/Language/Effects.cpp
  lib/Language/BodySummary.cpp
  lib/Language/BodyMapping.cpp
  lib/Language/ScopedSpecialization.cpp
  lib/Language/ScopedWitness.cpp
  lib/Language/SignatureWitness.cpp
  lib/Language/ScopedValues.cpp
  lib/Language/Scoped.cpp
  lib/Language/FiniteDomains.cpp
  lib/Language/FiniteDefinitions.cpp
  lib/Language/FiniteContracts.cpp
  lib/Language/HelperResults.cpp
  lib/Language/MathematicalFacts.cpp
  lib/Language/FiniteFormation.cpp
  lib/Language/DataRequirements.cpp
  lib/Language/FiniteDomainArguments.cpp
  lib/Language/DomainClosure.cpp
  lib/Language/DomainWitness.cpp
  lib/Language/ValueOrigins.cpp
  lib/Language/ClosureInputs.cpp
  lib/Language/FreePlaces.cpp
  lib/Language/Regions.cpp
  lib/Language/BodyCheck.cpp
  lib/Language/Placement.cpp
  lib/Language/BodyPlacement.cpp
  lib/Language/Expressions.cpp
  lib/Language/TypeInference.cpp
  lib/Language/CallableConstraints.cpp
  lib/Language/OperatorInference.cpp
  lib/Language/ExpressionInference.cpp
  lib/Language/CallResolution.cpp
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
target_link_libraries(ZkcLanguage PRIVATE utf8proc::utf8proc)
target_link_libraries(ZkcContracts PRIVATE utf8proc::utf8proc)
add_dependencies(ZkcLanguage ZkcSourceNameDataGen)
add_zkc_component(Relation
  lib/Relation/R1CS.cpp
  lib/Relation/R1CSBinary.cpp
  lib/Relation/AIR.cpp
  lib/Relation/AIRPolynomial.cpp
  lib/Relation/Bundle.cpp
  lib/Relation/BundleData.cpp
  lib/Relation/BundleStaged.cpp
  lib/Relation/BundleTable.cpp
  lib/Relation/BundlePolynomial.cpp
  lib/Relation/Matrices.cpp
)
add_zkc_component(Program
  lib/Program/Model.cpp
  lib/Program/Decode.cpp
  lib/Program/Encode.cpp
  lib/Program/Structure.cpp
  lib/Program/Admission.cpp
)
add_zkc_component(IR
  lib/Dialect/Collection.cpp
  lib/Dialect/Diagnostics.cpp
  lib/Dialect/Crypto/IR/CryptoDialect.cpp
  lib/Dialect/Local/IR/LocalDialect.cpp
  lib/Dialect/Exec/IR/ExecDialect.cpp
  lib/Dialect/Runtime/IR/RuntimeDialect.cpp
  lib/Dialect/Local/IR/Functions.cpp
  lib/Dialect/Local/IR/Control.cpp
  lib/Dialect/Kernel/IR/KernelDialect.cpp
  lib/Dialect/Kernel/IR/Kernel.cpp
  lib/Dialect/Data/IR/DataDialect.cpp
  lib/Dialect/Data/IR/Logical.cpp
  lib/Dialect/Data/IR/Domains.cpp
  lib/Analysis/NativeTypes.cpp
  lib/Analysis/TotalClosure.cpp
  lib/Analysis/ComputationUnit.cpp
  lib/Analysis/Finite.cpp
  lib/Analysis/Computation.cpp
  lib/Analysis/ComputationMeaning.cpp
  lib/Analysis/MathematicalFacts.cpp
  lib/Dialect/Algebra/IR/AlgebraDialect.cpp
  lib/Dialect/Algebra/IR/Mathematical.cpp
  lib/Dialect/Algebra/IR/Maps.cpp
  lib/Dialect/Algebra/RingExpression.cpp
  lib/Dialect/Bindings.cpp
  lib/Dialect/BoundOperations.cpp
  lib/Dialect/MathematicalInterfaces.cpp
  lib/Dialect/PreparationCallable.cpp
  lib/Dialect/LinearContraction.cpp
  lib/Dialect/Algebra/IR/Types.cpp
  lib/Dialect/Polynomial/IR/Types.cpp
  lib/Dialect/Polynomial/IR/Mathematical.cpp
  lib/Dialect/Polynomial/IR/Recipes.cpp
  lib/Dialect/Commitment/IR/CommitmentDialect.cpp
  lib/Dialect/Protocol/IR/ProtocolDialect.cpp
  lib/Dialect/Protocol/IR/Attributes.cpp
  lib/Dialect/MathematicalSemantics.cpp
  lib/Dialect/Protocol/NativePolicy.cpp
  lib/Dialect/Protocol/IR/Protocol.cpp
  lib/Dialect/Protocol/IR/Mathematical.cpp
  lib/Dialect/Protocol/IR/Origins.cpp
  lib/Dialect/Protocol/IR/Contracts.cpp
  lib/Dialect/Protocol/IR/ResourceOrigins.cpp
  lib/Dialect/Protocol/IR/Applications.cpp
  lib/Dialect/Protocol/IR/Construction.cpp
  lib/Dialect/Protocol/IR/ConstructionResolution.cpp
  lib/Dialect/Protocol/IR/Projection.cpp
  lib/Dialect/Protocol/Execution.cpp
  lib/Dialect/Relation/IR/AIR.cpp
  lib/Dialect/Relation/IR/R1CS.cpp
  lib/Dialect/Plan/IR/PlanDialect.cpp
  lib/Dialect/Polynomial/IR/PolynomialDialect.cpp
  lib/Dialect/Registry.cpp
  lib/Dialect/Relation/IR/RelationDialect.cpp
  lib/Dialect/Relation/IR/Declarations.cpp
  lib/Dialect/Relation/IR/Formula.cpp
  lib/Dialect/TypeAdapters/Algebra.cpp
  lib/Dialect/TypeAdapters/Commitment.cpp
  lib/Dialect/TypeAdapters/Core.cpp
  lib/Dialect/TypeAdapters/Runtime.cpp
  lib/Dialect/TypeAdapters/Curve.cpp
  lib/Dialect/TypeAdapters/Polynomial.cpp
  lib/Dialect/TypeAdapters/Registry.cpp
  lib/Dialect/TypeAdapters/Installed.cpp
  lib/Dialect/TypeAdapters/Resources.cpp
)
add_zkc_component(Translation
  lib/Translation/Entry.cpp
  lib/Translation/Language/Emission.cpp
  lib/Translation/Language/DataPreconditions.cpp
  lib/Translation/Language/FiniteEmission.cpp
  lib/Translation/Language/FiniteComparison.cpp
  lib/Translation/Language/Comparison.cpp
  lib/Translation/AIR.cpp
  lib/Translation/ProtocolExport.cpp
  lib/Translation/ProgramVerification.cpp
  lib/Translation/R1CS.cpp
  lib/Translation/R1CSSumcheck.cpp
)
add_zkc_component(Transforms
  lib/Conversion/Bindings.cpp
  lib/Conversion/PhysicalVerification.cpp
  lib/Conversion/Storage.cpp
  lib/Conversion/Participants.cpp
  lib/Transforms/Algorithms.cpp
  lib/Transforms/AlgorithmVerification.cpp
  lib/Transforms/Mathematical.cpp
  lib/Transforms/MathematicalTrace.cpp
  lib/Transforms/ProtocolApplications.cpp
  lib/Transforms/MathLowering.cpp
  lib/Transforms/MathRealizations.cpp
  lib/Transforms/Kernel/Formation.cpp
  lib/Transforms/Kernel/Closure.cpp
  lib/Transforms/Kernel/Readback.cpp
  lib/Transforms/Kernel/Lowering.cpp
  lib/Transforms/Kernel/Verification.cpp
  lib/Transforms/Kernel/Schedule.cpp
  lib/Transforms/Kernel/Recipes.cpp
  lib/Transforms/Kernel/RecipeVerification.cpp
  lib/Transforms/Kernel/Frontier.cpp
  lib/Transforms/Kernel/FrontierVerification.cpp
  lib/Transforms/Kernel/NormalizationVerification.cpp
  lib/Transforms/HelperNormalization.cpp
  lib/Transforms/HelperNormalizationVerification.cpp
  lib/Transforms/CollectFold.cpp
  lib/Transforms/FiniteRealizations.cpp
  lib/Transforms/FiniteVerification.cpp
  lib/Transforms/RealizationEmission.cpp
  lib/Transforms/CollectionRealization.cpp
  lib/Transforms/ComputationEquations.cpp
  lib/Transforms/ComputationSelection.cpp
  lib/Transforms/NumericalSelection.cpp
  lib/Transforms/NumericalLowering.cpp
  lib/Transforms/MathematicalRecipes.cpp
  lib/Transforms/LaneRealization.cpp
  lib/Transforms/MathematicalComparison.cpp
  lib/Transforms/NestedContractions.cpp
  lib/Transforms/NestedContractionVerification.cpp
  lib/Transforms/MapRealizations.cpp
  lib/Transforms/StructuredComputation.cpp
  lib/Transforms/VectorReductions.cpp
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
  lib/Dialect/Relation/Transforms/Deduplicate.cpp
  lib/Target/Selection.cpp
  lib/Target/Catalog.cpp
  lib/Target/PhysicalPlan.cpp
  lib/Target/StorageSchedule.cpp
)
add_zkc_component(Compiler
  lib/Compiler/Host.cpp
  lib/Compiler/AssetSharing.cpp
  lib/Compiler/Language.cpp
  lib/Compiler/LanguagePackage.cpp
  lib/Compiler/LanguageInterface.cpp
  lib/Compiler/LanguageInterfaceReader.cpp
  lib/Compiler/LanguageInterfaceWriter.cpp
  lib/Compiler/LanguageInterfaceComparison.cpp
  lib/Compiler/LanguageInspection.cpp
  lib/Compiler/Observation.cpp
  lib/Compiler/SourceClaims.cpp
  lib/Compiler/Compilation.cpp
  lib/Compiler/CommonSource.cpp
  lib/Compiler/StructuredSource.cpp
  lib/Compiler/ArtifactJson.cpp
  lib/Compiler/RunVerification.cpp
  lib/Compiler/Run.cpp
  lib/Compiler/PolynomialReduction.cpp
  lib/Compiler/PublicCoin.cpp
  lib/Compiler/NativeDeployment.cpp
  lib/Compiler/NativeCodec.cpp
  lib/Compiler/NativeCodecVerification.cpp
  lib/Compiler/NativeProof.cpp
  lib/Compiler/NativeProofVerification.cpp
  lib/Compiler/Passes.cpp
  lib/Compiler/Pipelines.cpp
  lib/Compiler/NativeCompilation.cpp
)
add_zkc_component(Driver
  lib/Driver/Language.cpp
  lib/Driver/Assets.cpp
  lib/Driver/Compiler.cpp
  lib/Driver/Relations.cpp
  lib/Driver/AIR.cpp
)
# Match the external package's LLVM linkage. Mixing its shared LLVM with a
# second static Support copy duplicates process-global LLVM state.
if(LLVM_LINK_LLVM_DYLIB)
  target_link_libraries(ZkcSupport PUBLIC LLVM)
else()
  target_link_libraries(ZkcSupport PUBLIC LLVMSupport)
endif()
add_dependencies(ZkcTransforms ZkcMathematicalRecipesGen)
target_include_directories(ZkcTransforms PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/generated/Transforms)
add_dependencies(ZkcContracts ZkcContractDeclarationsGen)
target_include_directories(ZkcContracts PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>)
target_link_libraries(ZkcContracts PUBLIC ZkcSupport)
target_link_libraries(ZkcRelation PUBLIC ZkcContracts)
target_link_libraries(ZkcLanguage PUBLIC ZkcRelation)
# IR owns mandatory profile validation; carrier adapters depend on that owner.
add_dependencies(ZkcIR ZkcIRGen)
target_include_directories(ZkcIR SYSTEM PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/include>
  $<BUILD_INTERFACE:${MLIR_INCLUDE_DIRS}>)
target_link_libraries(ZkcProgram PUBLIC ZkcContracts)
target_link_libraries(ZkcIR PUBLIC ZkcProgram ZkcRelation)
target_link_libraries(ZkcTranslation PUBLIC ZkcIR ZkcLanguage)
# Follow MLIR's package linkage too: embedding static MLIR archives alongside
# its dylib duplicates MLIR definitions and process-global state.
mlir_target_link_libraries(ZkcIR PUBLIC
  MLIRIR MLIRControlFlowInterfaces MLIRSideEffectInterfaces
  MLIRInferTypeOpInterface MLIRFunctionInterfaces MLIRCallInterfaces
  MLIRFuncDialect MLIRArithDialect MLIRSCFDialect MLIRControlFlowDialect
  MLIRLinalgDialect MLIRTensorDialect)
target_link_libraries(ZkcTransforms PUBLIC ZkcIR)
mlir_target_link_libraries(ZkcTransforms PUBLIC
  MLIRPass MLIRTransforms MLIRTransformUtils MLIRSCFDialect MLIRLinalgTransforms)
target_link_libraries(ZkcCompiler PUBLIC ZkcTransforms ZkcTranslation)
target_link_libraries(ZkcDriver PUBLIC ZkcCompiler)
mlir_target_link_libraries(ZkcCompiler PUBLIC MLIRParser)
mlir_target_link_libraries(ZkcDriver PUBLIC MLIRParser)
set(zkc_components ZkcSupport ZkcContracts ZkcLanguage ZkcRelation ZkcProgram ZkcIR ZkcTranslation ZkcTransforms ZkcCompiler ZkcDriver)

# Record actual target properties for the fast dependency-boundary test.
set(zkc_component_manifest "")
foreach(component ${zkc_components})
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

target_include_directories(ZkcLanguage PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/generated)
