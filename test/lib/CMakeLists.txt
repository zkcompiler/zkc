# DISABLE_INSTALL keeps the test-pass library out of the default install
# set; only production libraries ship.
add_mlir_library(ZkcTestPasses
  DISABLE_INSTALL
  TestArtifactLifecycle.cpp
  TestCompilerCore.cpp
  TestHoleParameters.cpp
  TestDuplexFraming.cpp
  TestInterpreter.cpp
  TestKzgBatchCore.cpp
  TestPirCompilerProvider.cpp
  TestSealEngine.cpp
  TestSealedGuard.cpp
  TestSoundnessEvaluator.cpp
  TestSoundnessCatalog.cpp
  TestSoundnessKernel.cpp
  TestSoundnessKzgPreservation.cpp
  TestSoundnessProjection.cpp
  TestSoundnessRuntime.cpp
  TestSoundnessRuleBodies.cpp
  TestSoundnessSemanticRegressions.cpp
  TestSoundnessSite.cpp

  EXCLUDE_FROM_LIBMLIR

  LINK_LIBS PUBLIC
  MLIRPass
  MLIRTransformUtils
  ZkcArtifact
  ZkcCompiler
  ZkcCompilerPir
  ZkcEncoding
  ZkcInterpreter
  ZkcPir
  ZkcPirTransforms
  ZkcRegistry
  ZkcSemantics
  ZkcSoundness
  ZkcSoundnessPir
)

target_include_directories(ZkcTestPasses PRIVATE
  ${PROJECT_SOURCE_DIR}/lib
)
