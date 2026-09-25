#ifndef ZKC_PROTOCOL_CONSTRUCTION_INTERNAL_H
#define ZKC_PROTOCOL_CONSTRUCTION_INTERNAL_H
#include "zkc/Source/Model.h"
#include "llvm/Support/JSON.h"
#include <memory>
namespace zkc::protocol {
namespace construction {
class Construction;
}
/// Pure emission result. The compiler must import/verify the candidate and
/// enforce the portable certificate bound before publishing it.
struct ConstructionDraft {
  source::Module source;
  llvm::json::Value certificate;
};
/// Package-private bridge from compiler orchestration to pure analysis.
/// Owns admitted source/identity/descriptor snapshots and analysis state.
/// This is a native preparation, not an MLIR or cryptographic judgment.
class PreparedConstruction {
  std::unique_ptr<construction::Construction> state;
  explicit PreparedConstruction(std::unique_ptr<construction::Construction>);
  friend llvm::Expected<PreparedConstruction>
      prepareConstruction(source::Module, source::Module, source::Construction);

public:
  PreparedConstruction(PreparedConstruction &&) noexcept;
  PreparedConstruction &operator=(PreparedConstruction &&) noexcept;
  ~PreparedConstruction();
  const source::Module &source() const;
  /// The compiler checks source() as IR before requesting emission. Consumes
  /// this preparation; only destruction/assignment is valid after moving it.
  llvm::Expected<ConstructionDraft> emit() &&;
};
/// Only compiler orchestration calls this bridge: inputs have structural
/// admission and source/selector transport was performed against original.
llvm::Expected<PreparedConstruction>
prepareConstruction(source::Module source, source::Module original,
                    source::Construction);
} // namespace zkc::protocol
#endif
