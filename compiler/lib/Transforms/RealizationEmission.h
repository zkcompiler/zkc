#ifndef ZKC_TRANSFORMS_REALIZATIONEMISSION_H
#define ZKC_TRANSFORMS_REALIZATIONEMISSION_H

#include "mlir/IR/Builders.h"
#include "zkc/Contracts/Binding.h"
#include "llvm/ADT/StringSet.h"
#include <map>
#include <tuple>

namespace zkc::mathematical {
/// Producer-only allocation in a private candidate. Existing declarations are
/// reserved by name, never rewritten or reused: an authored implementation pin
/// does not become an implicit choice for another operation. Only applications
/// emitted by this instance are deduplicated, including their exact pins.
///
/// The caller owns occurrence spelling, insertion points and candidate
/// publication. The owner must be a symbol table with one region and one block;
/// emitted uses must resolve their bindings in that table. The candidate must
/// undergo resolved-contract verification and independent correspondence
/// checking before publication. Readers must not use this producer to
/// reconstruct their expected operations.
class RealizationEmitter {
  mlir::Operation *unit;
  std::string prefix;
  llvm::StringSet<> names;
  unsigned next = 0;
  using Key = std::tuple<std::string, std::vector<std::string>, std::string>;
  std::map<Key, std::string> bindings;

public:
  RealizationEmitter(mlir::Operation *candidate, llvm::StringRef bindingPrefix);

  mlir::FlatSymbolRefAttr binding(mlir::OpBuilder &, mlir::Location,
                                  const protocol::BindingApplication &);

  mlir::Operation *emit(mlir::OpBuilder &, mlir::Location, llvm::StringRef site,
                        const protocol::BindingApplication &,
                        mlir::ValueRange inputs, mlir::TypeRange outputs,
                        llvm::ArrayRef<std::string> parameters = {});
};
} // namespace zkc::mathematical

#endif
