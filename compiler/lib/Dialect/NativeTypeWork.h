#ifndef ZKC_DIALECT_NATIVETYPEWORK_H
#define ZKC_DIALECT_NATIVETYPEWORK_H

#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/IR/BuiltinTypes.h"
#include "zkc/Dialect/TypeFormation.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringMap.h"
#include <functional>
#include <memory>
#include <optional>

namespace zkc::protocol {
struct TypePolicyFacts;
}
namespace zkc::generic {
struct Operation;
}

namespace zkc::detail {
// A dynamically scoped debit for native callbacks whose public MLIR signatures
// cannot carry caller work. The exact allowance owns these immutable results;
// no operation, symbol, supplied predicate or stage admission is cached here.
struct NativeTypeWork {
  struct Structure {
    uint64_t nodes, bytes;
    unsigned height;
  };
  struct Formation {
    LogicalTypePermissions permissions;
    unsigned nodes, height;
  };
  llvm::DenseMap<mlir::Attribute, Structure> attributes;
  llvm::DenseMap<mlir::Type, Structure> types;
  llvm::DenseMap<mlir::Type, Formation> formations;
  bool indexedContracts = false;
  llvm::StringMap<const generic::Operation *> contracts;
  using Application = std::pair<mlir::StringAttr, mlir::ArrayAttr>;
  struct OracleKindTypes {
    mlir::Type data, query, answer;
    std::optional<uint64_t> rows;
  };
  llvm::DenseMap<Application, OracleKindTypes> oracleKinds;
  llvm::DenseMap<Application, mlir::FunctionType> signatures;
  llvm::DenseMap<Application, mlir::Type> constructed;
  llvm::DenseMap<Application, llvm::SmallVector<mlir::Attribute>> bindingTerms;
  struct BindingTypes {
    mlir::FunctionType logical, values;
  };
  llvm::DenseMap<mlir::DictionaryAttr, BindingTypes> bindings;
  struct Policy {
    std::shared_ptr<const protocol::TypePolicyFacts> facts;
    unsigned nodes;
    size_t bytes;
  };
  llvm::DenseMap<mlir::Type, LogicalTypePermissions> formed;
  llvm::DenseMap<mlir::Type, Policy> policies;
};
class NativeTypeWorkScope {
  NativeTypeWorkScope *previous;
  std::function<void(uint64_t)> debit;
  inline static thread_local NativeTypeWorkScope *active = nullptr;

public:
  NativeTypeWork &work;
  NativeTypeWorkScope(NativeTypeWork &work, std::function<void(uint64_t)> debit)
      : previous(active), debit(std::move(debit)), work(work) {
    active = this;
  }
  ~NativeTypeWorkScope() { active = previous; }
  NativeTypeWorkScope(const NativeTypeWorkScope &) = delete;
  static NativeTypeWork *current() { return active ? &active->work : nullptr; }
  static void charge(uint64_t amount = 1) {
    if (active)
      active->debit(amount);
  }
};
} // namespace zkc::detail
#endif
