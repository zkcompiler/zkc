#include "zkc/Dialect/Protocol/Contracts.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Relation/IR/RelationOps.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;

namespace zkc::protocol_ir {
namespace {
struct Selector {
  bool output;
  unsigned port;
  StringAttr role;
  Type type;
};
class Contracts {
  MathematicalOp owner;
  SymbolTableCollection &symbols;
  unsigned remaining = 100000;

  LogicalResult refuse(StringRef detail) {
    return diagnostics::emit(owner.emitOpError(), "protocol-contract", detail);
  }
  std::optional<Selector> selector(Attribute attr) {
    auto row = dyn_cast<ArrayAttr>(attr);
    if (!remaining || !row || row.size() != 3)
      return {};
    --remaining;
    auto direction = dyn_cast<StringAttr>(row[0]);
    auto index = dyn_cast<IntegerAttr>(row[1]);
    auto role = dyn_cast<StringAttr>(row[2]);
    if (!direction || (direction != "input" && direction != "output") ||
        !index || !index.getType().isSignlessInteger(64) ||
        index.getInt() < 0 || !role || !is_contained(owner.getRoles(), role))
      return {};
    bool output = direction == "output";
    auto types = output ? owner.getFunctionType().getResults()
                        : owner.getFunctionType().getInputs();
    auto scopes = output ? owner.getOutputRoles() : owner.getInputRoles();
    uint64_t port = index.getInt();
    if (port >= types.size() || port >= scopes.size())
      return {};
    auto roles = dyn_cast<ArrayAttr>(scopes[port]);
    if (!roles || !is_contained(roles, role))
      return {};
    return Selector{output, unsigned(port), role, types[port]};
  }
  LogicalResult application(Attribute attr, bool &hasOutput) {
    auto row = dyn_cast<ArrayAttr>(attr);
    if (!remaining || !row || row.size() != 2)
      return refuse(
          "application must contain a relation reference and selectors");
    --remaining;
    auto reference = dyn_cast<FlatSymbolRefAttr>(row[0]);
    auto operands = dyn_cast<ArrayAttr>(row[1]);
    auto declaration =
        reference ? symbols.lookupNearestSymbolFrom<relation::DeclareOp>(
                        owner, reference)
                  : relation::DeclareOp();
    if (!declaration || !operands ||
        declaration->getParentOp() != owner->getParentOp() ||
        operands.size() != declaration.getSignature().getNumInputs())
      return refuse(
          "application requires an owned relation and its complete input ABI");
    hasOutput = false;
    for (auto [operand, type] :
         zip(operands, declaration.getSignature().getInputs())) {
      auto selected = selector(operand);
      if (!selected || selected->type != type)
        return refuse(
            "selector port, role or type differs from the relation ABI");
      hasOutput |= selected->output;
    }
    return success();
  }
  bool matches(StatementOp statement, ArrayAttr clause) {
    if (!remaining)
      return false;
    --remaining;
    auto subject = cast<ArrayAttr>(clause[2]);
    if (statement.getRelationAttr() != subject[0])
      return false;
    auto decision = selector(clause[4]);
    if (!decision || statement.getAcceptance() != decision->port)
      return false;
    auto operands = cast<ArrayAttr>(subject[1]);
    if (operands.size() != statement.getNumOperands() ||
        operands.size() != statement.getSelectors().size())
      return false;
    for (auto [operand, value, role] :
         zip(operands, statement.getInputs(), statement.getSelectors())) {
      auto selected = selector(operand);
      if (!selected || selected->output || selected->role != role ||
          selected->port >= owner.getBody().front().getNumArguments() ||
          value != owner.getBody().front().getArgument(selected->port))
        return false;
    }
    return true;
  }

public:
  Contracts(MathematicalOp owner, SymbolTableCollection &symbols)
      : owner(owner), symbols(symbols) {}
  LogicalResult run() {
    auto clauses = owner.getContractsAttr();
    if (!clauses)
      clauses = ArrayAttr::get(owner.getContext(), {});
    if (clauses.size() > 4096)
      return refuse("contract inventory exceeds the declaration limit");
    llvm::StringSet<> names;
    SmallVector<ArrayAttr> targets;
    for (auto attr : clauses) {
      auto row = dyn_cast<ArrayAttr>(attr);
      if (!row || row.size() != 5)
        return refuse("clause requires exactly kind, name, subject, residual "
                      "and decision");
      auto kind = dyn_cast<StringAttr>(row[0]);
      auto name = dyn_cast<StringAttr>(row[1]);
      if (!kind ||
          (kind != "target" && kind != "input" && kind != "output" &&
           kind != "continuation") ||
          !name || name.getValue().empty() || name.getValue().size() > 512 ||
          !names.insert(name.getValue()).second)
        return refuse("clause kind or unique name is invalid");
      bool output;
      if (failed(application(row[2], output)))
        return failure();
      if (((kind == "input" || kind == "continuation") && output) ||
          (kind == "output" && !output))
        return refuse("clause subject has invalid input/output directions");
      if (kind == "continuation") {
        if (failed(application(row[3], output)))
          return failure();
        if (!output)
          return refuse("continuation residual must select an output");
      } else if (!isa<UnitAttr>(row[3]))
        return refuse("only a continuation may have a residual");
      if (!isa<UnitAttr>(row[4])) {
        auto decision = selector(row[4]);
        if (kind == "input" || !decision || !decision->output ||
            !decision->type.isSignlessInteger(1))
          return refuse("decision requires one available Boolean output");
      } else if (kind == "target")
        return refuse("target requires a decision");
      if (kind == "target")
        targets.push_back(row);
    }
    for (auto statement : owner.getBody().front().getOps<StatementOp>()) {
      // Named Entry projections resolve only within this declaration. Unnamed
      // standalone statements do not supply exact selected-target evidence.
      auto selected = statement.getTargetAttr();
      if ((selected || !targets.empty()) &&
          !any_of(targets, [&](ArrayAttr target) {
            if (!remaining)
              return false;
            --remaining;
            return (!selected || target[1] == selected) &&
                   matches(statement, target);
          }))
        return diagnostics::emit(
            statement.emitOpError(), "protocol-contract-statement",
            "entry statement target is absent or disagrees with its owned "
            "declaration");
    }
    return success();
  }
};
} // namespace
LogicalResult verifyContracts(MathematicalOp owner,
                              SymbolTableCollection &symbols) {
  return Contracts(owner, symbols).run();
}
ArrayAttr getStatementTarget(StatementOp statement) {
  auto owner = dyn_cast<MathematicalOp>(statement->getParentOp());
  auto name = statement.getTargetAttr();
  if (!owner || !name || !owner.getContractsAttr())
    return {};
  for (auto attr : owner.getContractsAttr()) {
    auto clause = dyn_cast<ArrayAttr>(attr);
    if (clause && clause.size() == 5 && clause[1] == name) {
      auto kind = dyn_cast<StringAttr>(clause[0]);
      return kind && kind == "target" ? clause : ArrayAttr();
    }
  }
  return {};
}
} // namespace zkc::protocol_ir
