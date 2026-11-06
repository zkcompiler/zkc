#ifndef ZKC_TRANSFORMS_REALIZATIONEMISSION_H
#define ZKC_TRANSFORMS_REALIZATIONEMISSION_H

#include "NativeBindingApplication.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/StringSet.h"
#include <cstdint>
#include <functional>
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
  std::function<void(uint64_t)> reserve;
  std::function<mlir::Operation *(llvm::StringRef)> liveLookup;
  struct CreatedBinding {
    std::string name;
    mlir::Operation *operation;
    mlir::DictionaryAttr attributes;
  };
  std::map<std::pair<std::string, std::string>,
           llvm::DenseMap<mlir::ArrayAttr, CreatedBinding>>
      bindings;

public:
  RealizationEmitter(
      mlir::Operation *candidate, llvm::StringRef bindingPrefix,
      std::function<void(uint64_t)> reserve = {},
      std::function<mlir::Operation *(llvm::StringRef)> liveLookup = {});
  void reserveNames(mlir::Operation *source);

  mlir::FlatSymbolRefAttr binding(mlir::OpBuilder &, mlir::Location,
                                  const NativeBindingApplication &);
  // Reserve every live declaration lookup before executing it, including
  // declarations inserted by other producer work since construction. Failure
  // emits no binding; the caller owns sticky exhaustion and scratch disposal.
  mlir::FailureOr<mlir::FlatSymbolRefAttr>
  bindingWithWork(mlir::OpBuilder &, mlir::Location,
                  const NativeBindingApplication &,
                  llvm::function_ref<bool(uint64_t)> charge);
};
} // namespace zkc::mathematical

#endif
