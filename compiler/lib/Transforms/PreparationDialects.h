#ifndef ZKC_TRANSFORMS_PREPARATIONDIALECTS_H
#define ZKC_TRANSFORMS_PREPARATIONDIALECTS_H

#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraDialect.h"
#include "zkc/Dialect/Data/IR/DataDialect.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialDialect.h"
#include "zkc/Dialect/Protocol/IR/ProtocolDialect.h"
#include "zkc/Dialect/Runtime/IR/RuntimeDialect.h"

namespace zkc::mathematical {
// Include temporary candidates and polynomial realization, even when none of
// their output dialects occurs in the input. Keep direct APIs and pass-manager
// preloading on this inventory; verifiers must never load dialects themselves.
inline void registerPreparationDialects(mlir::DialectRegistry &registry) {
  registry.insert<algebra::AlgebraDialect, data::DataDialect, exec::ExecDialect,
                  poly::PolynomialDialect, protocol_ir::ProtocolDialect,
                  runtime::RuntimeDialect, mlir::arith::ArithDialect,
                  mlir::cf::ControlFlowDialect, mlir::func::FuncDialect>();
}

inline void loadPreparationDialects(mlir::MLIRContext &context) {
  mlir::DialectRegistry dependencies;
  registerPreparationDialects(dependencies);
  auto names = dependencies.getRegisteredDialectNames();
  // Under a pass manager these are already loaded before parallel execution.
  // Direct callers initialize their context before sharing it with workers.
  if (llvm::all_of(names, [&](llvm::StringRef name) {
        return context.getLoadedDialect(name) != nullptr;
      }))
    return;
  context.appendDialectRegistry(dependencies);
  for (llvm::StringRef name : names)
    context.getOrLoadDialect(name);
}
} // namespace zkc::mathematical

#endif
