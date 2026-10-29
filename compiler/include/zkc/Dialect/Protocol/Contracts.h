#ifndef ZKC_DIALECT_PROTOCOL_CONTRACTS_H
#define ZKC_DIALECT_PROTOCOL_CONTRACTS_H

#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include <optional>
#include <variant>

namespace zkc::protocol_ir {
// Contract selectors keep logical anchors distinct from role-local components.
// Both directions address the original common signature, before realization.
struct ContractPort {
  bool output;
  unsigned index;
};
struct ContractComponent {
  ContractPort port;
  mlir::StringAttr role;
  mlir::Type type;
};
struct ContractAnchor {
  ContractPort port;
  OracleKindAttr kind;
};
using ContractSelector = std::variant<ContractComponent, ContractAnchor>;
struct ContractApplication {
  mlir::FlatSymbolRefAttr relation;
  llvm::SmallVector<ContractSelector> operands;
};
struct ContractClause {
  mlir::StringAttr kind, name;
  ContractApplication subject;
  std::optional<ContractApplication> residual;
  std::optional<ContractComponent> decision;
};
struct ContractStatement {
  StatementOp statement;
  // Only an explicitly named target supplies an exact selection. An unnamed
  // statement may match a target without selecting that declaration.
  std::optional<unsigned> clause;
};
struct DeclarationContracts {
  llvm::SmallVector<ContractClause> clauses;
  llvm::SmallVector<ContractStatement> statements;
};
// Read the complete inventory with the same bounded rules as formation. This
// does not admit the complete protocol or interpret a relation's predicate.
// Operations/attributes borrow the source context; mutation invalidates the
// view.
mlir::FailureOr<DeclarationContracts>
readContracts(MathematicalOp owner, mlir::SymbolTableCollection &symbols);

// Declaration metadata only. The owner is the enclosing protocol definition.
// The native layout is documented in docs/spec/ir/protocols.md.
mlir::LogicalResult verifyContracts(MathematicalOp owner,
                                    mlir::SymbolTableCollection &symbols);
// Resolve an explicit selection in its containing protocol. Returns null for
// absent or unresolved selections; verifyContracts establishes full formation.
mlir::ArrayAttr getStatementTarget(StatementOp statement);
} // namespace zkc::protocol_ir

#endif
