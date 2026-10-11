#ifndef ZKC_DIALECT_PROTOCOL_CONSTRUCTION_H
#define ZKC_DIALECT_PROTOCOL_CONSTRUCTION_H

#include "zkc/Contracts/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Checked, immutable selection over ordinary Local definitions. Message
/// sites are the ordered leaves of one source payload; a handler runs once.
struct ConstructionRule {
  using Kind = ConstructionRuleKind;
  Kind kind;
  mlir::FlatSymbolRefAttr handler;
  llvm::SmallVector<std::string> sites;
  llvm::SmallVector<unsigned> inputs;
  llvm::SmallVector<mlir::Type> payload;
  llvm::SmallVector<mlir::Type> chunks;
};
struct ConstructionCodec {
  std::string provider;
  llvm::SmallVector<mlir::Type> record;
  mlir::FlatSymbolRefAttr initialize, write, finish;
  llvm::SmallVector<unsigned> inputs;
};
struct ConstructionPlan {
  enum class Root { Local, Host } root;
  mlir::FlatSymbolRefAttr symbol, target, initializer;
  std::string provider, suite;
  unsigned service;
  bool nativeBase;
  llvm::SmallVector<mlir::Type> state;
  llvm::SmallVector<ConstructionRule> rules;
  std::optional<ConstructionCodec> codec;
};
/// Strictly checks record shape, symbols, ordinary signatures and root/start
/// permissions. Occurrence admission additionally checks sites and authority
/// against the prepared protocol before rewriting any participant code.
llvm::Expected<ConstructionPlan>
readConstructionPlan(protocol_ir::ConstructionOp record,
                     mlir::SymbolTableCollection &symbols);
} // namespace zkc::protocol
#endif
