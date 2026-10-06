#ifndef ZKC_DIALECT_IR_TD
#define ZKC_DIALECT_IR_TD

// Convenience aggregate for generation and coordinated clients.
include "zkc/Dialect/Dialects.td"
include "zkc/Dialect/Types.td"
include "zkc/Dialect/Protocol/IR/ProtocolOps.td"
include "zkc/Dialect/Algebra/IR/AlgebraOps.td"
include "zkc/Dialect/Polynomial/IR/PolynomialOps.td"
include "zkc/Dialect/Local/IR/LocalOps.td"
include "zkc/Dialect/Crypto/IR/CryptoOps.td"
include "zkc/Dialect/Table/IR/TableOps.td"
include "zkc/Dialect/Plan/IR/PlanOps.td"
include "zkc/Dialect/PCS/IR/PCSOps.td"
include "zkc/Dialect/Oracle/IR/OracleOps.td"
include "zkc/Dialect/Relation/IR/RelationOps.td"
include "zkc/Dialect/Claim/IR/ClaimOps.td"

include "zkc/Dialect/Data/IR/DataOps.td"

#endif
