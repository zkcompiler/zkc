add_subdirectory(lib)

# Test-only pass driver. The source is shared with zkc-opt so its textual-input
# boundary cannot drift, while the compile definition keeps test pass symbols
# out of the production binary.
add_llvm_executable(zkc-test-opt ../tools/zkc-opt/zkc-opt.cpp)
llvm_update_compile_flags(zkc-test-opt)
target_compile_definitions(zkc-test-opt PRIVATE ZKC_ENABLE_TEST_PASSES)
target_link_libraries(zkc-test-opt PRIVATE
  MLIROptLib
  MLIRFuncDialect
  MLIRTransforms
  ZkcArtifact
  ZkcOir
  ZkcPir
  ZkcPirTransforms
  ZkcTestPasses
)
mlir_check_all_link_libraries(zkc-test-opt)

configure_lit_site_cfg(
  ${CMAKE_CURRENT_SOURCE_DIR}/lit.site.cfg.py.in
  ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.py
  MAIN_CONFIG
  ${CMAKE_CURRENT_SOURCE_DIR}/lit.cfg.py
)

# One list, two consumers: these are also the substitutions lit.cfg.py
# registers — a new tool is added here and there together.
set(ZKC_TEST_DEPENDS
  zkc-artifact
  zkc-derive
  zkc-family
  zkc-opt
  zkc-project
  zkc-test-opt
  zkc-registry-lint
  zkc-relation
  zkc-run
  zkc-seal
  zkc-translate
)

add_lit_testsuite(check-zkc "Running the zkc lit tests"
  ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS ${ZKC_TEST_DEPENDS}
)
