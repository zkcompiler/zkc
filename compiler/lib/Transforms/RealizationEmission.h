#ifndef ZKC_TRANSFORMS_REALIZATIONEMISSION_H
#define ZKC_TRANSFORMS_REALIZATIONEMISSION_H

#include "NativeBindingApplication.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"
#include <map>

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
  std::map<std::pair<std::string, std::string>,
           llvm::DenseMap<mlir::ArrayAttr, std::string>>
      bindings;

public:
  RealizationEmitter(mlir::Operation *candidate, llvm::StringRef bindingPrefix);
  void reserveNames(mlir::Operation *source);

  mlir::FlatSymbolRefAttr binding(mlir::OpBuilder &, mlir::Location,
                                  const NativeBindingApplication &);
};
} // namespace zkc::mathematical

#endif
