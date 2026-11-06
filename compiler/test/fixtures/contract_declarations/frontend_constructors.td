#ifndef ZKC_TEST_FRONTEND_CONSTRUCTORS
#define ZKC_TEST_FRONTEND_CONSTRUCTORS
// Every declaration inventory spells each frontend constructor form once.
def OracleHead : ZKC_FrontendConstructor<"oracle", "OracleHandle">;
def OracleSequenceHead
    : ZKC_FrontendConstructor<"oracle_sequence", "OracleHandleSequence">;
def : ZKC_FrontendConstructor<"finite", "FiniteDescriptor">;
def : ZKC_FrontendConstructor<"descriptor_product", "DescriptorProduct">;
def : ZKC_FrontendConstructor<"descriptor_sequence", "DescriptorSequence">;
include "frontend_schemes.td"
#endif
