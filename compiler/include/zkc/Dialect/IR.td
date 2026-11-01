#ifndef ZKC_DIALECT_IR_TD
#define ZKC_DIALECT_IR_TD

// Convenience aggregate for generation and coordinated clients.
include "zkc/Dialect/Dialects.td"
include "zkc/Dialect/Types.td"
include "zkc/Dialect/Protocol/IR/ProtocolOps.td"
include "zkc/Dialect/Algebra/IR/AlgebraOps.td"
include "zkc/Dialect/Polynomial/IR/PolynomialOps.td"
include "zkc/Dialect/Exec/IR/ExecOps.td"
include "zkc/Dialect/Crypto/IR/CryptoOps.td"
include "zkc/Dialect/Commitment/IR/CommitmentOps.td"
include "zkc/Dialect/Relation/IR/RelationOps.td"

include "zkc/Dialect/Data/IR/DataOps.td"

include "zkc/Dialect/Runtime/IR/RuntimeOps.td"
include "zkc/Dialect/Residue/IR/ResidueOps.td"
#endif
