#ifndef ZKC_COMPILER_COMPILATION_H
#define ZKC_COMPILER_COMPILATION_H

#include "mlir/IR/DialectRegistry.h"
#include "zkc/Protocol/PhysicalOptions.h"
#include "zkc/Source/Document.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/LinearContraction.h"
#include <memory>

namespace zkc {
namespace frontend {
class Analysis;
}
struct ConstructedProtocol;
/// Requested work; import preserves the stage encoded by the source document.
enum class ProtocolAction { Import, Expand, Project, Plan };
struct ProtocolOptions {
  ProtocolAction action = ProtocolAction::Plan;
  protocol::PhysicalOptions physical;
};
enum class TableAction { Import, Plan, Lazy, Materialized };
struct TableOptions {
  TableAction action = TableAction::Plan;
  bool simplify = false;
};

/// Owns the context and IR. Protocol compilations also own their original
/// source spelling; table compilations have no
/// Document. Borrowed accessors remain valid until this result is
/// destroyed/reassigned. Mutating module() invalidates any conclusions about
/// its previous contents.
class Compilation {
  struct Storage;
  std::unique_ptr<Storage> storage;
  explicit Compilation(std::unique_ptr<Storage>);
  friend llvm::Expected<Compilation>
  compileProtocol(source::Document, const ProtocolOptions &,
                  const mlir::DialectRegistry &);
  friend llvm::Expected<Compilation>
  compileTable(const llvm::json::Value &, const TableOptions &,
               const mlir::DialectRegistry &);

  friend llvm::Expected<ConstructedProtocol>
  constructProtocol(const frontend::Analysis &, source::Construction,
                    const mlir::DialectRegistry &);

public:
  Compilation(Compilation &&) noexcept;
  Compilation &operator=(Compilation &&) noexcept;
  ~Compilation();
  mlir::ModuleOp module() const;
  const source::Document *source() const;
  /// Populated only by ProtocolAction::Expand.
  llvm::ArrayRef<protocol::AlgorithmOrigin> origins() const;
  const LinearContractionStats &statistics() const;
};

/// A checked construction's context-owned IR and independently checkable
/// certificate. The compilation retains the original, pre-construction source.
/// Its origins are empty and its optimization statistics are zero.
struct ConstructedProtocol {
  Compilation compilation;
  llvm::json::Value certificate;
};
/// Bind selectors and lower from the same successful, captured analysis.
/// Owns its context and performs binding and lowering on one source internally.
/// The descriptor remains caller policy. Failure returns one CompilationError.
llvm::Expected<ConstructedProtocol>
constructProtocol(const frontend::Analysis &, source::Construction,
                  const mlir::DialectRegistry &);

/// compileProtocol and compileTable initialize an invocation-owned context.
/// Extensions register dialects/interfaces in the supplied registry before
/// calling. The
/// invocation registers built-in dialects; an empty additional registry is
/// valid. Every failure is one owned CompilationError (Compiler/Diagnostics.h),
/// including upstream errors without refusal identifiers. No partial artifact
/// is returned, including when an extension emits an error but reports success.
llvm::Expected<Compilation> compileProtocol(source::Document,
                                            const ProtocolOptions &,
                                            const mlir::DialectRegistry &);
llvm::Expected<Compilation> compileTable(const llvm::json::Value &,
                                         const TableOptions &,
                                         const mlir::DialectRegistry &);
} // namespace zkc
#endif
