add_zkc_unittest(ZkcSoundnessTests
  ArtifactJudgmentTest.cpp
  TransformerGroupTest.cpp)
target_link_libraries(ZkcSoundnessTests PRIVATE ZkcSoundness)
