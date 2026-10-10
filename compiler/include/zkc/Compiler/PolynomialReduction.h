#ifndef ZKC_COMPILER_POLYNOMIAL_REDUCTION_H
#define ZKC_COMPILER_POLYNOMIAL_REDUCTION_H

#include "mlir/IR/BuiltinOps.h"
#include "llvm/Support/JSON.h"

namespace zkc {
/// Check independently supplied boolean-sum-to-point requirements against an
/// immutable protocol source and an unsimplified participant candidate in the
/// same context. Neither input is changed. The returned report identifies the
/// actual ports and actions; it is not a theorem or an execution certificate.
/// Requirements are bounded to 1 MiB, nesting 64 and 64 records. Both modules
/// must pass ordinary admission. Mathematical rewrites after this check remain
/// trusted/tested and invalidate the report unless owned by checked
/// compilation.
llvm::Expected<llvm::json::Value>
checkPolynomialReductions(mlir::ModuleOp original, mlir::ModuleOp candidate,
                          llvm::StringRef requirements,
                          bool fuseVectorReductions = false);
} // namespace zkc
#endif
