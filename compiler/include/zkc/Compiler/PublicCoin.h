#ifndef ZKC_COMPILER_PUBLIC_COIN_H
#define ZKC_COMPILER_PUBLIC_COIN_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Transforms/MathematicalSelection.h"
#include "zkc/Transforms/OracleSelection.h"
#include "llvm/Support/JSON.h"

namespace zkc {
/// Analyze the independently selected authored or checked realized subject.
/// Shared calls and repeat bodies remain a definition DAG. The conservative
/// observation judgment is neither transcript binding nor a security theorem.
/// Preparation/realization use the independent policies exactly once; caller
/// modules are unchanged. See the public-coin specification for bounds.
llvm::Expected<llvm::json::Value>
analyzePublicCoin(mlir::ModuleOp original, llvm::StringRef requirement,
                  MathematicalSelectionPolicy policy = {},
                  const protocol::OracleRealizationPolicy &oraclePolicy = {});
/// Recompute the whole report from source and requirement, then compare the
/// supplied JSON value exactly, with unsigned integer tokens and unique object
/// keys. The caller supplies the policy independently; candidate metadata never
/// grants a premise.
llvm::Error
checkPublicCoin(mlir::ModuleOp original, llvm::StringRef requirement,
                llvm::StringRef report, MathematicalSelectionPolicy policy = {},
                const protocol::OracleRealizationPolicy &oraclePolicy = {});
} // namespace zkc
#endif
