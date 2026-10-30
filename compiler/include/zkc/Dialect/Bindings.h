#ifndef ZKC_DIALECT_BINDINGS_H
#define ZKC_DIALECT_BINDINGS_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Diagnostics.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Contracts/Bindings.h"

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
} // namespace zkc

namespace zkc::protocol {
/// Decode in already loaded dialects; return a null type if one is missing.
/// This operation never registers or loads dialects into the caller context.
mlir::Type decodeBoundType(mlir::MLIRContext *, const BoundType &);
llvm::Expected<BoundType> encodeBoundType(mlir::Type, bool physical);
/// Read a closed declaration. A Protocol module fixes its stage; a builtin
/// module admits logical or physical formation. Consumers of the latter must
/// also check their selected stage and actual invocation ports.
llvm::Expected<protocol::OperationBinding> readBinding(mlir::Operation *);
llvm::Expected<protocol::OperationBinding> operationBinding(mlir::Operation *);
} // namespace zkc::protocol

#endif
