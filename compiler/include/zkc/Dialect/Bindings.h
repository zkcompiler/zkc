#ifndef ZKC_DIALECT_BINDINGS_H
#define ZKC_DIALECT_BINDINGS_H

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Diagnostics.h"
#include "zkc/Contracts/Binding.h"
#include "zkc/Dialect/BindingTypes.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/SmallVector.h"
#include <optional>

namespace zkc {
/// In-process binding request and choice. Static values retain their native
/// kinds. valueType is empty before layout selection and otherwise contains
/// the complete data-only physical signature, including inactive children.
/// Scope/outcome ABI is derived with executableBindingSignature.
struct NativeBindingApplication {
  std::string contract;
  llvm::SmallVector<mlir::Attribute> arguments;
  std::string implementation;
  mlir::FunctionType valueType = {};
  /// Supplies context for requests without static arguments or selected ports.
  mlir::MLIRContext *context = nullptr;
};
/// Derive installed native ports from exact static arguments and optional
/// complete layout evidence. This owns installation/signature formation only;
/// it neither emits a declaration nor validates a physical plan or invocation.
mlir::FunctionType resolveInstalledSignature(
    llvm::function_ref<mlir::InFlightDiagnostic()> emit, mlir::MLIRContext *,
    const NativeBindingApplication &, bool physical,
    const protocol::ImplementationCatalog &, mlir::Type familyLayout = {});
/// Derive mathematical ports directly from catalog scope and kinded native
/// static values. Domains use StringAttr, complete types TypeAttr, naturals
/// ui64 IntegerAttr, and the numerical family a trailing DenseBoolArrayAttr.
/// This checks logical formation and requirements, not a target installation,
/// message codec, execution stage, or reached invocation parameters.
mlir::FunctionType
resolveLogicalSignature(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                        mlir::MLIRContext *context, llvm::StringRef contract,
                        llvm::ArrayRef<mlir::Attribute> arguments);
/// Resolve every catalog term directly, including associated identities and
/// complete type applications. The result borrows no operation and grants no
/// executable installation or invocation admission.
mlir::FailureOr<llvm::SmallVector<mlir::Attribute>>
resolveBindingTerms(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                    mlir::MLIRContext *, llvm::StringRef contract,
                    llvm::ArrayRef<mlir::Attribute> arguments);
/// Wrap mathematical value ports in the explicit ordered execution ABI.
mlir::FunctionType executableBindingSignature(mlir::FunctionType values);
/// Check optional standard call argument/result dictionaries against actual
/// ABI.
mlir::LogicalResult verifyCallAttributes(mlir::Operation *, unsigned inputs,
                                         unsigned outputs);

/// Inspect a declaration's exact logical signature and executable ABI without
/// resolving its implementation constraint. Only logical ports are accepted.
/// This read-only meaning query grants no installation or stage admission and
/// does not make a pinned operation eligible for replacement.
mlir::FunctionType
readLogicalBindingSignature(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                            mlir::Operation *);

/// Checked native declaration view. The actual ABI and complete layouts are
/// admitted against the installed implementation, without exporting native
/// types. Recheck after mutating the declaration or its enclosing profile.
/// This supplies no reached invocation, codec execution or resource authority.
struct NativeBinding {
  runtime::BindingOp declaration;
  mlir::FunctionType logicalType, valueType;
  bool physical;
};
/// Check context, static formation, exact callable ports, uniform stage,
/// selected provider and complete implementation-family layouts. An explicit
/// stage additionally constrains a declaration in a builtin module.
mlir::FailureOr<NativeBinding>
readNativeBinding(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                  mlir::Operation *,
                  std::optional<bool> physical = std::nullopt);
mlir::FailureOr<NativeBinding>
readNativeBinding(llvm::function_ref<mlir::InFlightDiagnostic()> emit,
                  mlir::Operation *, std::optional<bool> physical,
                  const protocol::ImplementationCatalog &);
/// Resolve a binding reference in its lexical symbol table, then check the
/// native declaration. Does not check the user's actual invocation ports.
mlir::FailureOr<NativeBinding> lookupNativeBinding(mlir::Operation *user);
} // namespace zkc

namespace zkc::protocol {
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
/// Explicit neutral-model export adapter. Native admission and the independent
/// neutral resolver both check the result; export also imposes byte-profile
/// limits. Failures emit no diagnostics. Inner semantic consumers use
/// readNativeBinding instead.
llvm::Expected<protocol::OperationBinding> readBinding(mlir::Operation *);
/// Export a referenced declaration at a neutral boundary. Native semantic
/// users resolve the declaration with lookupNativeBinding instead.
llvm::Expected<protocol::OperationBinding> operationBinding(mlir::Operation *);
} // namespace zkc::protocol

#endif
