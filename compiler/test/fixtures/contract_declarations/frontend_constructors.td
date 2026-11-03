#ifndef ZKC_TEST_FRONTEND_CONSTRUCTORS
#define ZKC_TEST_FRONTEND_CONSTRUCTORS
// Every declaration inventory spells each frontend constructor form once.
def OracleHead : ZKC_FrontendConstructor<"oracle", "OracleHandle">;
def OracleSequenceHead
    : ZKC_FrontendConstructor<"oracle_sequence", "OracleHandleSequence">;
#endif
