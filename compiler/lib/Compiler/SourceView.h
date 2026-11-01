#ifndef ZKC_LIB_COMPILER_SOURCEVIEW_H
#define ZKC_LIB_COMPILER_SOURCEVIEW_H

#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "llvm/Support/JSON.h"
#include <map>

namespace mlir {
class AsmParserState;
}
namespace llvm {
class SourceMgr;
}

namespace zkc::protocol {
// Bounded, read-only coordinates over actual source SSA. Closed scoped regions
// expose their checked logical inputs and outputs; they do not acquire another
// executable body. All Operation and Type handles borrow native and its
// context.
struct SourceBlock;
struct SourceInstruction {
  mlir::Operation *operation = nullptr;
  std::vector<unsigned> operands;
  std::vector<mlir::Type> results;
  std::vector<SourceBlock> regions;
  std::string site;
};
enum class SourceTerminator { Return, Yield, Condition, Stop };
struct SourceBlock {
  std::vector<mlir::Type> inputs, outputs;
  std::vector<SourceInstruction> instructions;
  SourceTerminator terminator = SourceTerminator::Return;
  mlir::Operation *terminal = nullptr;
  std::vector<unsigned> returned;
};
struct SourceDefinition {
  mlir::Operation *operation = nullptr;
  std::string name, kind;
  std::vector<std::string> roles;
  std::vector<std::vector<std::string>> inputRoles, outputRoles;
  bool hasBody = false;
  SourceBlock body;
};
struct SourceView {
  SourceView() = default;
  SourceView(SourceView &&) = default;
  // Assignment could release the old context before destroying its module.
  SourceView &operator=(SourceView &&) = delete;
  // When cloned from a checked original, keep its immutable context alive.
  // Declared before native so the module is destroyed before that context.
  std::optional<language::CheckedOriginal> originalOwner;
  mlir::OwningOpRef<mlir::ModuleOp> native;
  std::string identity, entry;
  std::vector<SourceDefinition> definitions;
  std::map<std::string, unsigned> names;
  // Boundary publication, built by the profile visitor. Native analyses read
  // operations and the typed view above, never this positional wire schema.
  llvm::json::Value publication = nullptr;
  // Per-operation boundary descriptors are used only when publishing routes.
  std::map<mlir::Operation *, llvm::json::Value> descriptors;
  std::vector<StructuredSourceAssociation> associations;
  const SourceDefinition *find(llvm::StringRef name) const;
};
llvm::Expected<SourceView> readSourceView(
    llvm::StringRef bytes, llvm::StringRef entry, mlir::MLIRContext &context,
    StructuredSourceProfile profile = StructuredSourceProfile::Original);
llvm::Expected<SourceView> readSourceView(
    mlir::OwningOpRef<mlir::ModuleOp> native, llvm::StringRef bytes,
    llvm::StringRef entry, const mlir::AsmParserState *parser,
    const llvm::SourceMgr *manager,
    const llvm::DenseMap<mlir::Operation *, mlir::Operation *>
        *writtenOperations,
    StructuredSourceProfile profile = StructuredSourceProfile::Original);
// Called only by the source profile visitor after admitting the actual body.
llvm::Expected<SourceDefinition>
buildSourceDefinition(mlir::Operation &, llvm::StringRef name,
                      llvm::StringRef kind, const SourceExecutionClosure &);
} // namespace zkc::protocol
namespace zkc::language::detail {
// Private access clones the admitted module; no mutable checked handle crosses
// the public language API. The returned view retains its context owner.
struct OriginalAccess {
  static llvm::Expected<protocol::SourceView> read(const CheckedOriginal &);
};
} // namespace zkc::language::detail
#endif
