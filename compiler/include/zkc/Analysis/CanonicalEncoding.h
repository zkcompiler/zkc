#ifndef ZKC_ANALYSIS_CANONICALENCODING_H
#define ZKC_ANALYSIS_CANONICALENCODING_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/Support/JSON.h"
#include <memory>
namespace zkc {
/// A bounded symbolic interpretation of actual straight-line scoped helpers.
/// It recognizes encodings, not arbitrary deterministic dependencies. All IDs
/// and SSA references belong to this immutable analysis instance.
class CanonicalEncodingAnalysis {
public:
  using Id = unsigned;
  enum class Kind {
    Input,
    Integer,
    Bytes,
    Concat,
    Encode,
    Length,
    Hash,
    Reduce
  };
  struct Node {
    Kind kind;
    mlir::Type type;
    std::string name;
    llvm::SmallVector<Id> inputs;
    uint64_t integer = 0;
    /// Input known to be the checked full digest carried by a history step.
    bool digestInput = false;
  };
  struct Encoding {
    llvm::SmallVector<Id> inputs;
    std::string tag;
  };
  explicit CanonicalEncodingAnalysis(mlir::Operation *owner);
  ~CanonicalEncodingAnalysis();
  llvm::Expected<Id> input(mlir::Type, llvm::StringRef name,
                           bool digest = false);
  llvm::Expected<llvm::SmallVector<Id>> apply(mlir::func::FuncOp,
                                              llvm::ArrayRef<Id>);
  /// Verify ordered unambiguous encoding, with whole actual values only.
  llvm::Expected<Encoding> encoding(Id);
  const Node &node(Id) const;
  llvm::Expected<llvm::json::Value> exportGraph() const;

private:
  struct Impl;
  std::unique_ptr<Impl> impl;
};
} // namespace zkc
#endif
