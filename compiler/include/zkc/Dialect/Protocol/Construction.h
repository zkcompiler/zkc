#ifndef ZKC_DIALECT_PROTOCOL_CONSTRUCTION_H
#define ZKC_DIALECT_PROTOCOL_CONSTRUCTION_H

#include "zkc/Contracts/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/Support/Error.h"

namespace zkc::protocol {
/// Checked, immutable selection over ordinary scoped functions. Message
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
struct ConstructionApplication {
  mlir::FlatSymbolRefAttr construction;
  std::string site;
};
struct ConstructionPlan {
  enum class Root { Local, Host } root;
  mlir::FlatSymbolRefAttr symbol, target, initializer;
  std::string provider, suite;
  llvm::SmallVector<unsigned> services;
  bool nativeBase;
  llvm::SmallVector<mlir::Type> state;
  llvm::SmallVector<ConstructionRule> rules;
  std::optional<ConstructionCodec> codec;
  llvm::SmallVector<ConstructionApplication> applications;
  bool rootOnly = false;
};
struct ConstructionInvocation {
  std::string site;
  mlir::FlatSymbolRefAttr handler;
  llvm::SmallVector<unsigned> inputs;
};
/// A source-resolved execution selection. Child rules carry expanded occurrence
/// identities; child starts retain their original callee input coordinates.
struct ResolvedConstruction {
  ConstructionPlan plan;
  llvm::SmallVector<ConstructionInvocation> invocations;
  llvm::SmallVector<mlir::FlatSymbolRefAttr> definitions;
};
/// Strictly checks record shape, symbols, ordinary signatures and root/start
/// permissions. Occurrence admission additionally checks sites and authority
/// against the prepared protocol before rewriting any participant code.
llvm::Expected<ConstructionPlan>
readConstructionPlan(protocol_ir::ConstructionOp record,
                     mlir::SymbolTableCollection &symbols);
/// Resolve child selections against original protocol calls, including roles,
/// service roots and complete child coverage. Uses one bounded traversal and
/// refuses cycles, overlapping subtrees and unreferenced fallback within a
/// child. The enclosing original protocol module must have passed formation;
/// call signatures, role maps and SSA scope are premises of this traversal.
llvm::Expected<ResolvedConstruction>
resolveConstructionPlan(protocol_ir::ConstructionOp record,
                        mlir::SymbolTableCollection &symbols);
} // namespace zkc::protocol
#endif
