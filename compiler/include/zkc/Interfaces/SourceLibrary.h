#ifndef ZKC_INTERFACES_SOURCELIBRARY_H
#define ZKC_INTERFACES_SOURCELIBRARY_H
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectInterface.h"
#include "zkc/Support/Json.h"
namespace zkc {
/// The name must identify a registered operation. Attributes are the complete
/// dictionary, including property-backed inherent attributes, not a subset.
/// All referenced types and operations must be loaded before verification.
struct ResolvedOperation {
  llvm::StringRef name;
  llvm::SmallVector<mlir::Type> inputs;
  mlir::Type output;
  llvm::SmallVector<mlir::NamedAttribute> attributes;
  bool ordered;
};
/// An installed model for a closed, ordered dependency set. A model can span
/// several dialects and operation slots. Descriptors resolve within installed
/// code; they cannot load providers. Models must be deterministic and
/// immutable.
class SourceLibraryInterface
    : public mlir::DialectInterface::Base<SourceLibraryInterface> {
public:
  explicit SourceLibraryInterface(mlir::Dialect *dialect) : Base(dialect) {}
  /// Nonempty ordered [name, revision] pairs, with nonempty strings and unique
  /// names. One interface instance is installed on each owning dialect.
  virtual llvm::json::Value dependencies() const = 0;
  virtual mlir::Type conditionType(mlir::Builder &) const = 0;
  virtual llvm::Expected<mlir::Type> decodeType(const llvm::json::Value &,
                                                mlir::Builder &) const = 0;
  virtual llvm::Expected<llvm::json::Value> encodeType(mlir::Type) const = 0;
  virtual llvm::Expected<ResolvedOperation>
  resolveOperation(const llvm::json::Value &, mlir::Builder &) const = 0;
};
/// Resolve exactly one loaded model. Unknown or ambiguous sets are refused.
/// The consumer must finish loading its library models and dependent dialects
/// at invocation setup, before parsing, translation or running passes.
/// The result borrows the context's interface; it does not own a registration.
llvm::Expected<const SourceLibraryInterface *>
resolveLibrary(const llvm::json::Value &, mlir::MLIRContext &);
/// Leaf verifier: check enclosure only, after ODS structural/type verification.
/// It does not establish library membership. The owning program's region
/// verifier resolves its context once and checks every operation below it.
mlir::LogicalResult verifySourceOperationContext(mlir::Operation *);
/// Check exact identity, attributes, and signature against an already resolved
/// operation. Export and program verification share this check.
mlir::LogicalResult verifySourceOperation(mlir::Operation *,
                                          const ResolvedOperation &);
} // namespace zkc
#endif
