add_zkc_unittest(ZkcRelationTests
  AnchorProjectionTest.cpp
  R1csHeaderTest.cpp)
target_link_libraries(ZkcRelationTests PRIVATE ZkcRelation)
