#ifndef ZKC_COMPILER_COMPILATION_H
#define ZKC_COMPILER_COMPILATION_H

#include "mlir/IR/DialectRegistry.h"
#include "zkc/Protocol/PhysicalOptions.h"
#include "zkc/Source/Document.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/LinearContraction.h"
#include <memory>

namespace zkc {
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

/// Owns the context, IR, original source spelling and expansion provenance.
/// Borrowed accessors remain valid until this result is destroyed/reassigned.
/// Mutating module() invalidates any conclusions about its previous contents.
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

public:
  Compilation(Compilation &&) noexcept;
  Compilation &operator=(Compilation &&) noexcept;
  ~Compilation();
  mlir::ModuleOp module() const;
  const source::Document *source() const;
  llvm::ArrayRef<protocol::AlgorithmOrigin> origins() const;
  const LinearContractionStats &statistics() const;
};

/// Both entry points initialize an invocation-owned context. Extensions must
/// register dialects/interfaces in the supplied registry before calling. The
/// invocation registers built-in dialects; an empty additional registry is valid.
/// Refusals return owned errors, never partially transformed artifacts.
llvm::Expected<Compilation> compileProtocol(source::Document,
                                            const ProtocolOptions &,
                                            const mlir::DialectRegistry &);
llvm::Expected<Compilation> compileTable(const llvm::json::Value &,
                                         const TableOptions &,
                                         const mlir::DialectRegistry &);
} // namespace zkc
#endif
