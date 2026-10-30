#ifndef ZKC_DIALECT_INVOCATIONPARAMETERS_H
#define ZKC_DIALECT_INVOCATIONPARAMETERS_H
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/Diagnostics.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/Support/Error.h"
#include <string>
#include <vector>
namespace zkc {
namespace exec {
class ApplyOp;
}
/// Check actual typed parameters against the catalog's closed scope. No byte
/// decoding, target installation, asset authorization or execution is done.
mlir::LogicalResult
verifyInvocationParameters(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                           llvm::StringRef contract, mlir::ArrayAttr arguments,
                           mlir::ArrayAttr parameters);
namespace protocol {
/// Explicit interchange with the program/0 parameter spellings. Native
/// consumers use the attributes directly. Neither direction is a fallback
/// native parser or evidence of source correspondence.
llvm::Expected<mlir::ArrayAttr>
decodeInvocationParameters(llvm::StringRef contract, mlir::ArrayAttr arguments,
                           llvm::ArrayRef<std::string> parameters);
llvm::Expected<mlir::ArrayAttr>
decodeInvocationParameters(mlir::MLIRContext *, const BindingApplication &,
                           llvm::ArrayRef<std::string> parameters);
llvm::Expected<std::vector<std::string>>
encodeInvocationParameters(llvm::StringRef contract, mlir::ArrayAttr arguments,
                           mlir::ArrayAttr parameters);
llvm::Expected<std::vector<std::string>>
    encodeInvocationParameters(exec::ApplyOp);
/// Compare actual attributes to independently decoded boundary data; never
/// print or execute the candidate to obtain its expected value.
bool invocationParametersMatch(llvm::StringRef contract,
                               mlir::ArrayAttr arguments,
                               mlir::ArrayAttr parameters,
                               llvm::ArrayRef<std::string> expected);
} // namespace protocol
} // namespace zkc
#endif
