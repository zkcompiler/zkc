#ifndef ZKC_DIALECT_BINDINGS_H
#define ZKC_DIALECT_BINDINGS_H

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Diagnostics.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

namespace zkc {
/// Derive mathematical ports directly from catalog scope and kinded native
/// static values. Domains use StringAttr, complete types TypeAttr, naturals
/// ui64 IntegerAttr, and the numerical family a trailing DenseBoolArrayAttr.
/// This checks logical formation and requirements, not a target installation,
/// message codec, execution stage, or reached invocation parameters.
mlir::FunctionType
resolveLogicalSignature(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                        mlir::MLIRContext *context, llvm::StringRef contract,
                        llvm::ArrayRef<mlir::Attribute> arguments);
/// Wrap mathematical value ports in the explicit ordered execution ABI.
mlir::FunctionType executableBindingSignature(mlir::FunctionType values);
/// Check optional standard call argument/result dictionaries against actual
/// ABI.
mlir::LogicalResult verifyCallAttributes(mlir::Operation *, unsigned inputs,
                                         unsigned outputs);
} // namespace zkc

namespace zkc::protocol {
/// Decode in already loaded dialects; return a null type if one is missing.
/// This operation never registers or loads dialects into the caller context.
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
/// Decode/encode static values only at neutral-model interchange boundaries.
llvm::Expected<mlir::ArrayAttr>
decodeBindingArguments(mlir::MLIRContext *, const BindingApplication &);
llvm::Expected<std::vector<std::string>>
encodeBindingArguments(llvm::StringRef contract, mlir::ArrayAttr arguments);
/// Reconstruct the exact executable ABI at a neutral-model boundary.
llvm::Expected<mlir::FunctionType> bindingSignature(mlir::MLIRContext *,
                                                    const BindingApplication &,
                                                    bool physical);
/// Compare actual native attributes and ports with an independently resolved
/// neutral record. No candidate execution, printing or byte round trip is used.
bool bindingMatches(runtime::BindingOp, const OperationBinding &,
                    bool physical);
/// Import a complete independently admitted neutral binding into native IR.
/// Physical selection is represented by its actual ports, never a parallel
/// physical_arguments attribute. This is not an alternative native parser.
llvm::Expected<runtime::BindingOp> importBinding(mlir::OpBuilder &,
                                                 mlir::Location,
                                                 const OperationBinding &,
                                                 bool physical);
/// Read a closed declaration. A Protocol module fixes its stage; a builtin
/// module admits logical or physical formation. Consumers of the latter must
/// also check their selected stage and actual invocation ports.
llvm::Expected<protocol::OperationBinding> readBinding(mlir::Operation *);
llvm::Expected<protocol::OperationBinding> operationBinding(mlir::Operation *);
} // namespace zkc::protocol

#endif
