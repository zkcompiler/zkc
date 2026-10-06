#ifndef ZKC_COMPILER_PUBLIC_COIN_H
#define ZKC_COMPILER_PUBLIC_COIN_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/JSON.h"

namespace zkc {
/// Analyze an owned, expanded, unsimplified copy of an admitted protocol
/// module. The independent requirement selects an entry, its verifier decision,
/// bound input components and exact public challenge deliveries. The original
/// is unchanged. This is a conservative syntactic dependence check, not a
/// Fiat-Shamir transformation or security theorem. See the public-coin profile
/// for the accepted fragment and bounded work/report contract.
llvm::Expected<llvm::json::Value>
analyzePublicCoin(mlir::ModuleOp original, llvm::StringRef requirement);
/// Recompute the whole report from source and requirement, then compare the
/// supplied JSON value exactly, with unsigned integer tokens and unique object
/// keys. Candidate metadata never grants a premise.
llvm::Error checkPublicCoin(mlir::ModuleOp original,
                            llvm::StringRef requirement,
                            llvm::StringRef report);
} // namespace zkc
#endif
