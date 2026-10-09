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

add_zkc_test(math_realization Transforms)
add_test(NAME math-realization COMMAND zkc-math_realization-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical/helper-realization.mlir")
set_tests_properties(math-realization PROPERTIES LABELS native)
mlir_target_link_libraries(zkc-math_realization-test PRIVATE MLIRParser)
add_zkc_test(map_realization Transforms)
add_test(NAME map-realization COMMAND zkc-map_realization-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical/map-realization.mlir")
set_tests_properties(map-realization PROPERTIES LABELS native)
mlir_target_link_libraries(zkc-map_realization-test PRIVATE MLIRParser)
add_zkc_test(language_package Compiler language-package)
add_zkc_test(asset_sharing Compiler asset-sharing)
add_zkc_test(language_interface Compiler language-interface)
add_zkc_test(language_assets Language language-assets)
add_zkc_test(language_expression_assets Language language-expression-assets)
target_compile_definitions(zkc-language_expression_assets-test PRIVATE
  ZKC_SUMCHECK_LIBRARY="${PROJECT_SOURCE_DIR}/../libraries/sumcheck/expression.zkc"
  ZKC_EXPRESSION_SUMCHECK_PROJECT="${PROJECT_SOURCE_DIR}/../examples/projects/expression-sumcheck")
add_zkc_test(language_asset_ir Compiler language-asset-ir)
mlir_target_link_libraries(zkc-language_asset_ir-test PRIVATE MLIRParser)
add_zkc_test(language_specifications Language language-specifications)
add_zkc_test(language_bundle_relations Compiler language-bundle-relations)
add_zkc_test(language_entries Language language-entries)
add_zkc_test(language_entry_ir Compiler)
mlir_target_link_libraries(zkc-language_entry_ir-test PRIVATE MLIRParser)
add_test(NAME language-entry-ir COMMAND zkc-language_entry_ir-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/language/schnorr.zkc")
set_tests_properties(language-entry-ir PROPERTIES LABELS native)
add_zkc_test(language_specification_ir Compiler language-specification-ir)
mlir_target_link_libraries(zkc-language_specification_ir-test PRIVATE MLIRParser)
add_zkc_test(language_natural Language language-natural)
add_zkc_test(language_power Compiler language-power)
add_zkc_test(language_polynomial Compiler)
mlir_target_link_libraries(zkc-language_polynomial-test PRIVATE MLIRParser)
add_test(NAME language-polynomial COMMAND zkc-language_polynomial-test
  "${CMAKE_CURRENT_SOURCE_DIR}/fixtures/language/polynomial.zkc")
set_tests_properties(language-polynomial PROPERTIES LABELS native)
add_zkc_test(language_boolean Compiler language-boolean)
add_zkc_test(language_map Compiler language-map)
mlir_target_link_libraries(zkc-language_boolean-test PRIVATE MLIRParser)
add_zkc_test(language_capabilities Compiler language-capabilities)
add_zkc_test(language_inference Compiler language-inference)
add_zkc_test(language_lexical Compiler language-lexical)
add_zkc_test(language_placement Compiler language-placement)
add_zkc_test(language_types Compiler language-types)
mlir_target_link_libraries(zkc-language_types-test PRIVATE MLIRParser)
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
# Also driven with the Rust ring provider by tests/protocol/test_clean_air_conformance.py.
add_zkc_test(clean_air_conformance Relation)
add_test(NAME clean-air-conformance COMMAND zkc-clean_air_conformance-test
  "${PROJECT_SOURCE_DIR}/../tests/fixtures/clean/air-control.json")
set_tests_properties(clean-air-conformance PROPERTIES LABELS native)
add_zkc_test(operation_contracts Contracts operation-contracts)
target_compile_definitions(zkc-operation_contracts-test PRIVATE
  ZKC_HISTORY_FIXTURE="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/contracts/history.txt")
add_zkc_test(linear_interfaces Transforms linear-interfaces)
add_zkc_test(target_decisions Transforms target-decisions)
target_link_libraries(zkc-target_decisions-test PRIVATE ZkcTranslation)
add_zkc_test(domains IR nominal-domains)
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
add_zkc_test(mathematical_correspondence Transforms mathematical-correspondence)
target_compile_definitions(zkc-mathematical_correspondence-test PRIVATE
  ZKC_MATH_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/mathematical")
mlir_target_link_libraries(zkc-mathematical_correspondence-test PRIVATE MLIRParser)
add_zkc_test(projection_metadata Transforms projection-metadata)
target_link_libraries(zkc-projection_metadata-test PRIVATE ZkcTranslation)
mlir_target_link_libraries(zkc-projection_metadata-test PRIVATE MLIRParser)
add_zkc_test(resource_origin_analysis IR resource-origin-analysis)
target_compile_definitions(zkc-resource_origin_analysis-test PRIVATE
  ZKC_ORIGIN_FIXTURES="${CMAKE_CURRENT_SOURCE_DIR}/fixtures/resource-origins")
mlir_target_link_libraries(zkc-resource_origin_analysis-test PRIVATE MLIRParser)
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
  PYTHONPATH=${CMAKE_CURRENT_SOURCE_DIR}/support:${PROJECT_SOURCE_DIR}/../tests/support)

# Every Python file in this directory is a test, and its name is the test's
# name with underscores for hyphens. Registering by listing the directory is
# what stops a script from sitting here unrun: it is a test by being here. The
# glob does not descend, so vocabulary these tests share sits in support/, and
# what they share with another build's tests sits in tests/support.
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
