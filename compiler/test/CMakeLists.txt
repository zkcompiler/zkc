# Native API tests and tool-level integration checks. Every test.cpp here is
# built and named from this one list: two of them used to be declared a
# directory up, which put their binaries somewhere else and made them look, to
# anyone reading this file, like sources nothing ran.
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

add_zkc_test(compilation CompilerCore compilation-api)
add_zkc_test(json Support json-carrier)
add_zkc_test(requirements Contracts)
add_zkc_test(generic Contracts generic-signatures)
add_zkc_test(bindings IR operation-bindings)
add_zkc_test(source Compiler source-document)
add_zkc_test(frontend_analysis FrontendLoading frontend-analysis)
add_zkc_test(checked_library Frontend checked-library)
add_zkc_test(library_entry Frontend library-entry-layout)
add_zkc_test(frontend_provenance Frontend frontend-provenance)
add_zkc_test(export Compiler protocol-export)
add_zkc_test(admission Protocol protocol-admission)
add_zkc_test(variants Compiler local-variants)
add_zkc_test(symbols IR protocol-symbols)
add_zkc_test(family_symbols Compiler input-family-symbols)
add_zkc_test(relation Relation relation-model)
add_zkc_test(relation_authoring FrontendLoading relation-authoring-model)
add_zkc_test(air Relation air-model)
add_zkc_test(air_polynomial Relation air-polynomial-model)
add_zkc_test(claims Compiler claims-api)
add_zkc_test(execution Compiler source-execution)
add_zkc_test(input_family_provenance Compiler input-family-static-provenance)
add_zkc_test(oracle_access Protocol oracle-access)
add_zkc_test(operation_contracts Contracts operation-contracts)
target_compile_definitions(zkc-operation_contracts-test PRIVATE
  ZKC_HISTORY_FIXTURE="${PROJECT_SOURCE_DIR}/../tests/fixtures/variants/history-contracts.txt")
add_zkc_test(polynomial_domain_contracts Protocol polynomial-domain-contracts)
add_zkc_test(linear_interfaces Compiler linear-interfaces)
add_zkc_test(obligations Protocol obligation-closure)
add_zkc_test(domains IR nominal-domains)
add_zkc_test(representations Contracts representation-domains)
add_zkc_test(properties IR registered-properties)

add_zkc_test(diagnostics IR ir-diagnostics)
add_zkc_test(ir_verification IR ir-verification)
target_link_libraries(zkc-symbols-test PRIVATE MLIRParser)

find_package(Python3 REQUIRED COMPONENTS Interpreter)

# The tests below drive this build's own tools as separate processes, and no
# other build's. Each takes no arguments: it names the tool it needs and
# support/tools.py resolves it, from what is set here because this file is the
# only thing that knows which file it built. Nothing is passed an executable
# path, so no test can be handed the wrong one. To run one by hand, run it from
# here: ctest --test-dir BUILD -R NAME -V.
set(zkc_script_environment
  ZKC_CTEST_COMPONENTS=${PROJECT_BINARY_DIR}/component-dependencies.txt
  ZKC_CTEST_COMPILER=$<TARGET_FILE:zkc-compile>
  ZKC_CTEST_OPTIMIZER=$<TARGET_FILE:zkc-opt>
  ZKC_CTEST_SOURCE_BENCH=$<TARGET_FILE:zkc-source-bench>
  ZKC_CTEST_SERVICE_COMPILER=$<TARGET_FILE:zkc-service-compile>
  ZKC_CTEST_SERVICE_OPTIMIZER=$<TARGET_FILE:zkc-service-opt>
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
