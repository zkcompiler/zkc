# Native API tests and tool-level integration checks are built and named here.
#
# A test name is optional. Without one the file is built but registers no test,
# which is for an executable a Python test here drives as a tool.
function(add_zkc_test name component)
  add_executable(zkc-${name}-test ${name}.cpp)
  target_link_libraries(zkc-${name}-test PRIVATE Zkc${component})
  target_compile_options(zkc-${name}-test PRIVATE -Wall -Wextra -Werror)
  if(ARGC GREATER 2)
    add_test(NAME ${ARGV2} COMMAND zkc-${name}-test)
    set_tests_properties(${ARGV2} PROPERTIES LABELS native)
  endif()
endfunction()

# Source fixtures use the same dependency closure as CLI consumers.
find_package(Python3 REQUIRED COMPONENTS Interpreter)
file(GLOB_RECURSE source_project_manifests CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/../libraries/*/zkc.toml")
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
  ${source_project_manifests}
  "${CMAKE_CURRENT_SOURCE_DIR}/support/source_project.py"
  "${PROJECT_SOURCE_DIR}/../common/tests/support/project.py")
function(zkc_source_project target manifest)
  set(output "${CMAKE_CURRENT_BINARY_DIR}/${target}-sources.json")
  execute_process(COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_CURRENT_SOURCE_DIR}/support/source_project.py" "${manifest}" "${output}"
    COMMAND_ERROR_IS_FATAL ANY)
  set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${manifest}")
  target_compile_definitions(${target} PRIVATE ZKC_SOURCE_PROJECT="${output}")
endfunction()

add_zkc_test(structured_associations Compiler structured-associations)
target_compile_definitions(zkc-structured_associations-test PRIVATE
  ZKC_ASSOCIATION_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")

add_zkc_test(computation_unit IR computation-unit)
mlir_target_link_libraries(zkc-computation_unit-test PRIVATE MLIRParser)

add_zkc_test(execution_finite IR execution-finite)
mlir_target_link_libraries(zkc-execution_finite-test PRIVATE MLIRParser)
add_zkc_test(execution_computation IR execution-computation)
mlir_target_link_libraries(zkc-execution_computation-test PRIVATE MLIRParser)

add_zkc_test(runtime_scopes IR runtime-scopes)
target_compile_definitions(zkc-runtime_scopes-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-runtime_scopes-test PRIVATE MLIRParser)

add_zkc_test(execution_comparison IR execution-comparison)
target_compile_definitions(zkc-execution_comparison-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-execution_comparison-test PRIVATE MLIRParser)

add_zkc_test(scoped_control_schedule IR scoped-control-schedule)
target_compile_definitions(zkc-scoped_control_schedule-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-scoped_control_schedule-test PRIVATE MLIRParser MLIRSCFDialect)
add_zkc_test(execution_control_cursor IR execution-control-cursor)
target_compile_definitions(zkc-execution_control_cursor-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-execution_control_cursor-test PRIVATE MLIRParser)

add_zkc_test(source_emission_budget Translation source-emission-budget)
add_zkc_test(source_finite_execution Translation source-finite-execution)
add_zkc_test(source_scoped_execution Translation source-scoped-execution)
target_link_libraries(zkc-source_scoped_execution-test PRIVATE ZkcTransforms)
mlir_target_link_libraries(zkc-source_scoped_execution-test PRIVATE MLIRParser)
mlir_target_link_libraries(zkc-source_emission_budget-test PRIVATE MLIRParser)

add_zkc_test(execution_emission Translation execution-emission)
target_compile_definitions(zkc-execution_emission-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-execution_emission-test PRIVATE MLIRParser)

add_zkc_test(source_execution IR source-execution)
target_compile_definitions(zkc-source_execution-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-source_execution-test PRIVATE MLIRParser)

add_zkc_test(execution_reader IR execution-reader)
target_compile_definitions(zkc-execution_reader-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-execution_reader-test PRIVATE MLIRParser)

add_zkc_test(structured_computation Transforms structured-computation)
mlir_target_link_libraries(zkc-structured_computation-test PRIVATE MLIRParser)

add_zkc_test(quotient_calculations Compiler quotient-calculations)
mlir_target_link_libraries(zkc-quotient_calculations-test PRIVATE MLIRParser)

add_zkc_test(total_closure IR total-closure)
target_compile_definitions(zkc-total_closure-test PRIVATE
  ZKC_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-total_closure-test PRIVATE MLIRParser)

add_zkc_test(mathematical_facts Contracts mathematical-facts)
add_zkc_test(common_reference Translation)
mlir_target_link_libraries(zkc-common_reference-test PRIVATE MLIRParser)
add_zkc_test(structured_reference IR)
mlir_target_link_libraries(zkc-structured_reference-test PRIVATE MLIRParser)
add_zkc_test(finite_cardinality Contracts finite-cardinality)
add_zkc_test(mathematical_fact_analysis IR mathematical-fact-analysis)
mlir_target_link_libraries(zkc-mathematical_fact_analysis-test PRIVATE
  MLIRParser MLIRPass)
add_zkc_test(language_mathematical_facts Language language-mathematical-facts)
add_zkc_test(language_usage_plan Language language-usage-plan)
add_zkc_test(language_compositional_forwarding Compiler language-compositional-forwarding)
mlir_target_link_libraries(zkc-language_compositional_forwarding-test PRIVATE MLIRParser)
add_zkc_test(language_finite_occurrence Compiler language-finite-occurrence)
mlir_target_link_libraries(zkc-language_finite_occurrence-test PRIVATE MLIRParser)
add_zkc_test(language_finite_cardinality Language language-finite-cardinality)
add_zkc_test(mathematical_fact_lifetime IR mathematical-fact-lifetime)
mlir_target_link_libraries(zkc-mathematical_fact_lifetime-test PRIVATE
  MLIRParser MLIRPass)

add_zkc_test(finite_direct_emission Transforms finite-direct-emission)
target_compile_definitions(zkc-finite_direct_emission-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-finite_direct_emission-test PRIVATE MLIRParser)

add_zkc_test(finite_abi IR finite-abi)
mlir_target_link_libraries(zkc-finite_abi-test PRIVATE MLIRParser)

add_zkc_test(finite_callback_selection Transforms finite-callback-selection)
mlir_target_link_libraries(zkc-finite_callback_selection-test PRIVATE MLIRParser)
add_zkc_test(scoped_collection_sum Transforms scoped-collection-sum)
mlir_target_link_libraries(zkc-scoped_collection_sum-test PRIVATE MLIRParser)
add_zkc_test(finite_preparation Transforms finite-preparation)
mlir_target_link_libraries(zkc-finite_preparation-test PRIVATE MLIRParser)

add_zkc_test(computation_analysis IR computation-analysis)
target_compile_definitions(zkc-computation_analysis-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-computation_analysis-test PRIVATE MLIRParser)

add_zkc_test(computation_equations Transforms computation-equations)
target_compile_definitions(zkc-computation_equations-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-computation_equations-test PRIVATE MLIRParser)

add_zkc_test(computation_outcomes Transforms computation-outcomes)
target_compile_definitions(zkc-computation_outcomes-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-computation_outcomes-test PRIVATE MLIRParser)

add_zkc_test(mathematical_recipes Transforms mathematical-recipes)
target_compile_definitions(zkc-mathematical_recipes-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-mathematical_recipes-test PRIVATE MLIRParser)

add_zkc_test(realization_emission Transforms realization-emission)
mlir_target_link_libraries(zkc-realization_emission-test PRIVATE MLIRParser)

add_zkc_test(pass_dependencies Transforms pass-dependencies)
mlir_target_link_libraries(zkc-pass_dependencies-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(bounded_access_verification Transforms bounded-access-verification)
mlir_target_link_libraries(zkc-bounded_access_verification-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(mathematical_stages Transforms mathematical-stages)
target_compile_definitions(zkc-mathematical_stages-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical"
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-mathematical_stages-test PRIVATE MLIRParser)

add_zkc_test(mathematical_decisions Transforms mathematical-decisions)
target_compile_definitions(zkc-mathematical_decisions-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical"
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-mathematical_decisions-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(finite_computation Transforms finite-computation)
target_compile_definitions(zkc-finite_computation-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-finite_computation-test PRIVATE MLIRParser)

add_zkc_test(domain_admission Transforms domain-admission)
target_compile_definitions(zkc-domain_admission-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-domain_admission-test PRIVATE
  MLIRParser MLIRTransforms)

add_zkc_test(math_realization Transforms)
add_test(NAME math-realization COMMAND zkc-math_realization-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical/helper-realization.mlir")
set_tests_properties(math-realization PROPERTIES LABELS native)
mlir_target_link_libraries(zkc-math_realization-test PRIVATE MLIRParser)
add_zkc_test(helper_normalization Transforms helper-normalization)
target_compile_definitions(zkc-helper_normalization-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical"
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-helper_normalization-test PRIVATE MLIRParser)
add_zkc_test(vector_reductions Transforms vector-reductions)
target_compile_definitions(zkc-vector_reductions-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical")
mlir_target_link_libraries(zkc-vector_reductions-test PRIVATE MLIRParser)
add_zkc_test(numerical_expressions Transforms)
add_test(NAME numerical-expressions COMMAND zkc-numerical_expressions-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/structured-source/map-declarations.mlir")
set_tests_properties(numerical-expressions PROPERTIES LABELS native)
mlir_target_link_libraries(zkc-numerical_expressions-test PRIVATE MLIRParser)
add_zkc_test(map_realization Transforms)
add_test(NAME map-realization COMMAND zkc-map_realization-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/structured-source/map-declarations.mlir")
set_tests_properties(map-realization PROPERTIES LABELS native)
mlir_target_link_libraries(zkc-map_realization-test PRIVATE MLIRParser)
add_zkc_test(late_maps Transforms late-maps)
mlir_target_link_libraries(zkc-late_maps-test PRIVATE MLIRParser)
add_zkc_test(language_package Compiler language-package)
add_zkc_test(asset_sharing Compiler asset-sharing)
add_zkc_test(language_interface Compiler language-interface)
add_zkc_test(language_assets Language language-assets)
add_zkc_test(language_expression_assets Language language-expression-assets)
zkc_source_project(zkc-language_expression_assets-test
  "${PROJECT_SOURCE_DIR}/../examples/projects/sumcheck/product/zkc.toml")
target_compile_definitions(zkc-language_expression_assets-test PRIVATE
  ZKC_EXPRESSION_SUMCHECK_PROJECT="${PROJECT_SOURCE_DIR}/../examples/projects/sumcheck/product")
add_zkc_test(language_asset_ir Compiler language-asset-ir)
mlir_target_link_libraries(zkc-language_asset_ir-test PRIVATE MLIRParser)
add_zkc_test(language_specifications Language language-specifications)
add_zkc_test(language_bundle_relations Compiler language-bundle-relations)
add_zkc_test(language_entries Language language-entries)
add_zkc_test(language_sites Compiler language-sites)
add_zkc_test(language_constructions Compiler language-constructions)
add_zkc_test(language_modules Compiler language-modules)
add_zkc_test(construction_applications Compiler construction-applications)
mlir_target_link_libraries(zkc-language_constructions-test PRIVATE MLIRParser)
mlir_target_link_libraries(zkc-language_sites-test PRIVATE MLIRParser)
add_zkc_test(language_entry_ir Compiler)
mlir_target_link_libraries(zkc-language_entry_ir-test PRIVATE MLIRParser)
add_test(NAME language-entry-ir COMMAND zkc-language_entry_ir-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/language/schnorr.zkc")
set_tests_properties(language-entry-ir PROPERTIES LABELS native)
add_zkc_test(language_specification_ir Compiler language-specification-ir)
mlir_target_link_libraries(zkc-language_specification_ir-test PRIVATE MLIRParser)
add_zkc_test(language_natural Language language-natural)
add_zkc_test(language_names Language language-names)
target_link_libraries(zkc-language_names-test PRIVATE utf8proc::utf8proc)
target_compile_definitions(zkc-language_names-test PRIVATE
  ZKC_UNICODE_DATA="${ZKC_UNICODE_SOURCE_DIR}/17.0.0")
add_test(NAME unicode-sdk
  COMMAND "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/support/unicode_sdk.py"
    --output "${CMAKE_CURRENT_BINARY_DIR}/unicode-sdk"
    --llvm-dir "${LLVM_DIR}" --utf8proc-dir "${utf8proc_DIR}"
    --c-compiler "${CMAKE_C_COMPILER}" --cxx-compiler "${CMAKE_CXX_COMPILER}")
set_tests_properties(unicode-sdk PROPERTIES LABELS native)
add_zkc_test(language_power Compiler language-power)
add_zkc_test(language_polynomial Compiler)
mlir_target_link_libraries(zkc-language_polynomial-test PRIVATE MLIRParser)
add_test(NAME language-polynomial COMMAND zkc-language_polynomial-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/language/polynomial.zkc")
set_tests_properties(language-polynomial PROPERTIES LABELS native)
add_zkc_test(group_identity Compiler group-identity)
mlir_target_link_libraries(zkc-group_identity-test PRIVATE MLIRParser)
add_zkc_test(language_boolean Compiler language-boolean)
add_zkc_test(language_map Compiler language-map)
mlir_target_link_libraries(zkc-language_map-test PRIVATE MLIRParser)
add_zkc_test(language_scoped Language language-scoped)
add_zkc_test(language_effect_algebra Language language-effect-algebra)
add_zkc_test(language_effect_boundaries Language language-effect-boundaries)
add_zkc_test(language_finite_domains Language language-finite-domains)
add_zkc_test(language_callback_origins Language language-callback-origins)
add_zkc_test(language_scoped_ir Compiler language-scoped-ir)
mlir_target_link_libraries(zkc-language_scoped_ir-test PRIVATE MLIRParser)
zkc_source_project(zkc-language_scoped_ir-test
  "${PROJECT_SOURCE_DIR}/../common/tests/fixtures/projects/scoped-computations/zkc.toml")
add_zkc_test(language_reductions Language language-reductions)
add_zkc_test(language_reduction_ir Compiler language-reduction-ir)
mlir_target_link_libraries(zkc-language_reduction_ir-test PRIVATE MLIRParser)
mlir_target_link_libraries(zkc-language_boolean-test PRIVATE MLIRParser)
add_zkc_test(language_capabilities Compiler language-capabilities)
add_zkc_test(language_inference Compiler language-inference)
add_zkc_test(operator_inference Language operator-inference)
add_zkc_test(library_operators Compiler library-operators)
add_zkc_test(language_notation Language language-notation)
add_zkc_test(language_notation_inspection Language language-notation-inspection)
add_zkc_test(language_api_inspection Language language-api-inspection)
add_zkc_test(language_written_source Language language-written-source)
add_zkc_test(source_bindings Language source-bindings)
zkc_source_project(zkc-source_bindings-test
  "${PROJECT_SOURCE_DIR}/../examples/projects/fri/zkc.toml")
add_zkc_test(notation_semantics Language notation-semantics)
add_zkc_test(language_arguments Compiler language-arguments)
add_zkc_test(language_logic Compiler language-logic)
add_zkc_test(language_presentation Language language-presentation)
add_zkc_test(language_lexical Compiler language-lexical)
add_zkc_test(language_usage Compiler language-usage)
add_zkc_test(language_admission Compiler language-admission)
add_zkc_test(language_placement Compiler language-placement)
add_zkc_test(language_types Compiler language-types)
mlir_target_link_libraries(zkc-language_types-test PRIVATE MLIRParser)
add_zkc_test(language_sequence Compiler language-sequence)
mlir_target_link_libraries(zkc-language_sequence-test PRIVATE MLIRParser)
add_zkc_test(language Compiler language-api)
mlir_target_link_libraries(zkc-language-test PRIVATE MLIRParser)
target_compile_definitions(zkc-language-test PRIVATE
  ZKC_LANGUAGE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/language")
add_zkc_test(run Compiler run-api)
add_zkc_test(run_preservation Compiler run-preservation)
mlir_target_link_libraries(zkc-run_preservation-test PRIVATE MLIRParser)
add_zkc_test(public_coin Compiler public-coin-api)
mlir_target_link_libraries(zkc-public_coin-test PRIVATE MLIRParser)
add_zkc_test(json Support json-carrier)
add_zkc_test(requirements Contracts)
add_zkc_test(generic Contracts generic-signatures)
add_zkc_test(numerical_contracts Program numerical-contracts)
add_zkc_test(ring_expression Contracts ring-expression)
add_zkc_test(ring_expression_ir IR ring-expression-ir)
add_zkc_test(ring_sharing Contracts ring-sharing)
add_zkc_test(ring_conformance Contracts)
add_zkc_test(relation_bundle_conformance Relation)
add_zkc_test(contract_declarations Contracts contract-declarations)
add_zkc_test(native_origin Contracts native-origin)
add_zkc_test(native_preservation Compiler)
mlir_target_link_libraries(zkc-native_preservation-test PRIVATE MLIRParser)
add_test(NAME native-preservation COMMAND zkc-native_preservation-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical/schnorr-services.mlir")
add_zkc_test(native_proof Compiler)
mlir_target_link_libraries(zkc-native_proof-test PRIVATE MLIRParser)
add_test(NAME native-proof-construction COMMAND zkc-native_proof-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical/schnorr-services.mlir")
add_zkc_test(native_proof_selection Compiler)
mlir_target_link_libraries(zkc-native_proof_selection-test PRIVATE MLIRParser)
add_test(NAME native-proof-selection COMMAND zkc-native_proof_selection-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical")
add_zkc_test(structural_types Contracts structural-types)
add_zkc_test(implementation_policy Transforms implementation-policy)
add_zkc_test(type_adapters IR type-adapters)
add_zkc_test(collection_types IR collection-types)
mlir_target_link_libraries(zkc-collection_types-test PRIVATE MLIRParser)
add_zkc_test(type_adapter_ambiguity Contracts type-adapter-ambiguity)
target_sources(zkc-type_adapter_ambiguity-test PRIVATE
  "${PROJECT_SOURCE_DIR}/lib/Dialect/TypeAdapters/Registry.cpp")
target_include_directories(zkc-type_adapter_ambiguity-test SYSTEM PRIVATE ${MLIR_INCLUDE_DIRS})
mlir_target_link_libraries(zkc-type_adapter_ambiguity-test PRIVATE MLIRIR)
add_zkc_test(contract_inventory Contracts)
add_zkc_test(contract_conformance Contracts)
add_test(NAME contract-declarations-generation
  COMMAND ${CMAKE_COMMAND}
    "-DZKC_TABLEGEN=$<TARGET_FILE:zkc-tblgen>"
    "-DZKC_DECLARATION_INCLUDE=${PROJECT_SOURCE_DIR}/include"
    "-DZKC_DECLARATION_FIXTURES=${CMAKE_CURRENT_SOURCE_DIR}/fixtures/contract_declarations"
    "-DZKC_DECLARATION_TEST_DIRECTORY=${CMAKE_CURRENT_BINARY_DIR}/contract-declarations-generation"
    -P "${CMAKE_CURRENT_SOURCE_DIR}/contract_declarations_generation.cmake")
set_tests_properties(contract-declarations-generation PROPERTIES LABELS native)
add_zkc_test(bindings IR operation-bindings)
add_zkc_test(contract_mappings Translation operation-contract-mappings)
add_test(NAME contract-mapping-generation
  COMMAND ${CMAKE_COMMAND}
    "-DZKC_TABLEGEN=$<TARGET_FILE:zkc-tblgen>"
    "-DZKC_TABLEGEN_INCLUDES=${zkc_tablegen_includes}"
    "-DZKC_MAPPING_TEST_DIRECTORY=${CMAKE_CURRENT_BINARY_DIR}/contract-mapping-generation"
    -P "${CMAKE_CURRENT_SOURCE_DIR}/contract_mapping_generation.cmake")
set_tests_properties(contract-mapping-generation PROPERTIES LABELS native)
add_zkc_test(relation Relation relation-model)
add_zkc_test(air Relation air-model)
add_zkc_test(air_ring_expression Relation air-ring-expression)
add_zkc_test(air_polynomial Relation air-polynomial-model)
add_zkc_test(relation_bundle Relation relation-bundle)
# Also driven with the Rust ring provider by common/tests/protocol/test_clean_air_conformance.py.
add_zkc_test(clean_air_conformance Relation)
add_test(NAME clean-air-conformance COMMAND zkc-clean_air_conformance-test
  "${PROJECT_SOURCE_DIR}/../common/tests/fixtures/clean/air-control.json")
set_tests_properties(clean-air-conformance PROPERTIES LABELS native)
add_zkc_test(operation_contracts Contracts operation-contracts)
target_compile_definitions(zkc-operation_contracts-test PRIVATE
  ZKC_HISTORY_FIXTURE="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/contracts/history.txt")
add_zkc_test(linear_interfaces Transforms linear-interfaces)
add_zkc_test(target_decisions Transforms target-decisions)
target_link_libraries(zkc-target_decisions-test PRIVATE ZkcTranslation)
add_zkc_test(domains IR nominal-domains)
add_zkc_test(plonky3_fields Contracts plonky3-fields)
add_zkc_test(relation_declarations IR relation-declarations)
mlir_target_link_libraries(zkc-relation_declarations-test PRIVATE MLIRParser)
add_zkc_test(native_policy Transforms native-local-policy)
mlir_target_link_libraries(zkc-native_policy-test PRIVATE MLIRParser)
target_compile_definitions(zkc-native_policy-test PRIVATE
  ZKC_MIXED_FIXTURE="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical/local-execution.mlir")
add_zkc_test(simplification_scope Transforms simplification-scope)
mlir_target_link_libraries(zkc-simplification_scope-test PRIVATE MLIRParser)
add_zkc_test(lowering_preservation Transforms lowering-preservation)
mlir_target_link_libraries(zkc-lowering_preservation-test PRIVATE MLIRParser)
add_zkc_test(program_artifact Transforms program-artifact)
target_link_libraries(zkc-program_artifact-test PRIVATE ZkcTranslation)
mlir_target_link_libraries(zkc-program_artifact-test PRIVATE MLIRParser)
add_zkc_test(expansion_preservation Transforms expansion-preservation)
target_compile_definitions(zkc-expansion_preservation-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical")
mlir_target_link_libraries(zkc-expansion_preservation-test PRIVATE MLIRParser)
add_zkc_test(construction_starts Transforms construction-starts)
mlir_target_link_libraries(zkc-construction_starts-test PRIVATE MLIRParser)
add_zkc_test(mathematical_correspondence Transforms mathematical-correspondence)
target_compile_definitions(zkc-mathematical_correspondence-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical")
mlir_target_link_libraries(zkc-mathematical_correspondence-test PRIVATE MLIRParser)
add_zkc_test(projection_metadata Transforms projection-metadata)
target_link_libraries(zkc-projection_metadata-test PRIVATE ZkcTranslation)
mlir_target_link_libraries(zkc-projection_metadata-test PRIVATE MLIRParser)
add_zkc_test(resource_origin_analysis IR resource-origin-analysis)
add_zkc_test(resource_origin_sources IR)
mlir_target_link_libraries(zkc-resource_origin_sources-test PRIVATE MLIRAsmParser)
mlir_target_link_libraries(zkc-resource_origin_analysis-test PRIVATE MLIRParser MLIRAsmParser)
add_zkc_test(mathematical_dependencies IR mathematical-dependencies)
mlir_target_link_libraries(zkc-mathematical_dependencies-test PRIVATE MLIRParser)
add_zkc_test(mathematical_interfaces IR mathematical-interfaces)
mlir_target_link_libraries(zkc-mathematical_interfaces-test PRIVATE MLIRParser)
add_zkc_test(algebra_formation IR algebra-formation)
mlir_target_link_libraries(zkc-algebra_formation-test PRIVATE MLIRParser)
add_zkc_test(representations Contracts representation-domains)
add_zkc_test(properties IR registered-properties)

add_zkc_test(diagnostics IR ir-diagnostics)
add_zkc_test(dialect_registration IR dialect-registration)

find_package(Python3 REQUIRED COMPONENTS Interpreter)
find_program(zkc_record_tablegen NAMES llvm-tblgen HINTS "${LLVM_TOOLS_BINARY_DIR}" REQUIRED)
set(zkc_generation_includes ${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
list(REMOVE_DUPLICATES zkc_generation_includes)
list(JOIN zkc_generation_includes "\", \"" zkc_generation_include_json)
file(GENERATE OUTPUT "${PROJECT_BINARY_DIR}/generation-settings.json"
  CONTENT "{\"mlir_tablegen\": \"${MLIR_TABLEGEN_EXE}\", \"llvm_tablegen\": \"${zkc_record_tablegen}\", \"cxx\": \"${CMAKE_CXX_COMPILER}\", \"source_include\": \"${PROJECT_SOURCE_DIR}/include\", \"generated_include\": \"${PROJECT_BINARY_DIR}/include\", \"dependency_include\": [\"${zkc_generation_include_json}\"]}\n")


# The tests below drive this build's own tools as separate processes, and no
# other build's. Each takes no arguments: it names the tool it needs and
# support/tools.py resolves it, from what is set here because this file is the
# only thing that knows which file it built. Nothing is passed an executable
# path, so no test can be handed the wrong one. To run one by hand, run it from
# here: ctest --test-dir BUILD -R NAME -V.
set(zkc_script_environment
  ZKC_CTEST_PROGRAM_CODEC=$<TARGET_FILE:zkc-program_codec-test>
  ZKC_CTEST_TABLEGEN=$<TARGET_FILE:zkc-tblgen>
  ZKC_CTEST_COMPONENTS=${PROJECT_BINARY_DIR}/component-dependencies.txt
  ZKC_CTEST_COMPILER=$<TARGET_FILE:zkc-compile>
  ZKC_CTEST_OPTIMIZER=$<TARGET_FILE:zkc-opt>
  ZKC_CTEST_REQUIREMENTS_TEST=$<TARGET_FILE:zkc-requirements-test>
  ZKC_CTEST_RESOURCE_ORIGIN_SOURCES=$<TARGET_FILE:zkc-resource_origin_sources-test>
  PYTHONPATH=${CMAKE_CURRENT_SOURCE_DIR}/support:${PROJECT_SOURCE_DIR}/../common/tests/support)

# Every Python file in this directory is a test, and its name is the test's
# name with underscores for hyphens. Registering by listing the directory is
# what stops a script from sitting here unrun: it is a test by being here. The
# glob does not descend, so vocabulary these tests share sits in support/, and
# what they share with another build's tests sits in common/tests/support.
file(GLOB zkc_scripts CONFIGURE_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/*.py)
foreach(script ${zkc_scripts})
  get_filename_component(stem ${script} NAME_WE)
  string(REPLACE "_" "-" name ${stem})
  add_test(NAME ${name} COMMAND ${Python3_EXECUTABLE} ${script})
  set_tests_properties(${name} PROPERTIES ENVIRONMENT "${zkc_script_environment}")
endforeach()

mlir_target_link_libraries(zkc-contract_mappings-test PRIVATE MLIRParser)
mlir_target_link_libraries(zkc-target_decisions-test PRIVATE MLIRParser)

add_zkc_test(program_codec Program)

add_zkc_test(relation_table_view Relation)
add_test(NAME relation-table-view COMMAND zkc-relation_table_view-test
  "${PROJECT_SOURCE_DIR}/adapters/plonky3/fixtures/recurrence")
set_tests_properties(relation-table-view PROPERTIES LABELS native)

add_zkc_test(relation_bundle_polynomial Relation)
add_test(NAME relation-bundle-polynomial COMMAND zkc-relation_bundle_polynomial-test
  "${PROJECT_SOURCE_DIR}/adapters/plonky3/fixtures/recurrence"
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/relation/polynomial-chunks.json")
set_tests_properties(relation-bundle-polynomial PROPERTIES LABELS native)

add_zkc_test(mathematical_comparison Transforms mathematical-comparison)
target_compile_definitions(zkc-mathematical_comparison-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-mathematical_comparison-test PRIVATE MLIRParser)

add_zkc_test(nested_contractions Transforms nested-contractions)
target_compile_definitions(zkc-nested_contractions-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-nested_contractions-test PRIVATE MLIRParser)

add_zkc_test(nested_contractions_source Compiler nested-contractions-source)
target_compile_definitions(zkc-nested_contractions_source-test PRIVATE
  ZKC_NESTED_SOURCE="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/language/nested-matrix.zkc")
mlir_target_link_libraries(zkc-nested_contractions_source-test PRIVATE MLIRParser)

add_zkc_test(finite_verification_capacity Transforms finite-verification-capacity)
target_compile_definitions(zkc-finite_verification_capacity-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-finite_verification_capacity-test PRIVATE MLIRParser)

add_zkc_test(total_verification_capacity Transforms total-verification-capacity)
target_compile_definitions(zkc-total_verification_capacity-test PRIVATE
  ZKC_FINITE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-total_verification_capacity-test PRIVATE MLIRParser)

add_zkc_test(program_logical_realizations Program program-logical-realizations)
add_zkc_test(program_resource_origins Program program-resource-origins)

add_zkc_test(computation_realization Transforms computation-realization)
target_compile_definitions(zkc-computation_realization-test PRIVATE
  ZKC_COMPUTATION_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-computation_realization-test PRIVATE MLIRParser MLIRPass)

# Original-source computation ownership coverage uses the maintained source emitter.
target_link_libraries(zkc-computation_realization-test PRIVATE ZkcTranslation)

add_zkc_test(cpu_target Compiler cpu-target)
mlir_target_link_libraries(zkc-cpu_target-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(computation_physical_plan Transforms computation-physical-plan)
target_compile_definitions(zkc-computation_physical_plan-test PRIVATE
  ZKC_COMPUTATION_PHYSICAL_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-computation_physical_plan-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(physical_schedule Transforms physical-schedule)
target_compile_definitions(zkc-physical_schedule-test PRIVATE
  ZKC_SCHEDULE_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures")
mlir_target_link_libraries(zkc-physical_schedule-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(computation_frontier Transforms computation-frontier)
target_compile_definitions(zkc-computation_frontier-test PRIVATE
  ZKC_FRONTIER_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/computation")
mlir_target_link_libraries(zkc-computation_frontier-test PRIVATE MLIRParser)

add_zkc_test(computation_normalization Transforms computation-normalization)
target_compile_definitions(zkc-computation_normalization-test PRIVATE
  ZKC_NORMALIZATION_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/computation_normalization")
mlir_target_link_libraries(zkc-computation_normalization-test PRIVATE MLIRParser)

add_zkc_test(collect_fold Transforms collect-fold)
target_compile_definitions(zkc-collect_fold-test PRIVATE
  ZKC_LOOP_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-collect_fold-test PRIVATE MLIRParser MLIRSCFDialect)

add_zkc_test(computation_schedule Transforms computation-schedule)
target_compile_definitions(zkc-computation_schedule-test PRIVATE
  ZKC_LOOP_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-computation_schedule-test PRIVATE MLIRParser MLIRSCFDialect)

add_zkc_test(host_entry Compiler host-entry)
mlir_target_link_libraries(zkc-host_entry-test PRIVATE MLIRParser)

add_zkc_test(language_entry_functions Language language-entry-functions)
add_zkc_test(power_of_two_recipe Transforms power-of-two-recipe)
mlir_target_link_libraries(zkc-power_of_two_recipe-test PRIVATE MLIRParser)
add_zkc_test(language_source_terms Compiler language-source-terms)
add_zkc_test(language_source_claims Compiler language-source-claims)
target_compile_definitions(zkc-language_source_claims-test PRIVATE
  ZKC_CLAIM_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/source-claims")

add_zkc_test(resident_representations Transforms resident-representations)
add_zkc_test(halo2curves_provider Compiler halo2curves-provider)
mlir_target_link_libraries(zkc-halo2curves_provider-test PRIVATE MLIRParser MLIRPass)
mlir_target_link_libraries(zkc-resident_representations-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(native_preferences Transforms native-preferences)
mlir_target_link_libraries(zkc-native_preferences-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(aggregate_layouts Transforms aggregate-layouts)
mlir_target_link_libraries(zkc-aggregate_layouts-test PRIVATE MLIRParser MLIRPass)

add_zkc_test(scoped_schedule Transforms scoped-schedule)
target_compile_definitions(zkc-scoped_schedule-test PRIVATE
  ZKC_LOOP_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite")
mlir_target_link_libraries(zkc-scoped_schedule-test PRIVATE MLIRParser MLIRSCFDialect)

add_zkc_test(structured_admission IR structured-admission)
mlir_target_link_libraries(zkc-structured_admission-test PRIVATE MLIRParser)
add_zkc_test(pass_policy Transforms)
add_test(NAME pass-policy COMMAND zkc-pass_policy-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/finite/total-zip.mlir")
set_tests_properties(pass-policy PROPERTIES LABELS native)
mlir_target_link_libraries(zkc-pass_policy-test PRIVATE MLIRParser MLIRPass)
