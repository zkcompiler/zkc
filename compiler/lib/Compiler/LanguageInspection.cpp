#include "zkc/Compiler/LanguageInspection.h"
#include "LanguageInterface.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/StringMap.h"
using namespace llvm;
namespace zkc::language {
namespace {
class Inspection {
  const LanguageInterface &view;
  const Limits &limits;
  function_ref<Error(const ApplicationOccurrence &)> visitor;
  uint64_t remaining;
  StringMap<const InterfaceProtocol *> protocols;
  SmallVector<unsigned> path;
  bool charge(uint64_t amount) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  }
  Error limit() {
    return error("source.limit", "application inspection limit exceeded");
  }
  Expected<AppliedSelector> bind(protocol_ir::ApplyOp operation,
                                 ArrayRef<unsigned> roles,
                                 const InterfaceSelector &selector) {
    if (!charge(selector.native.size() + 1))
      return limit();
    if (selector.role >= roles.size())
      return error("source.interface",
                   "application selector role is out of bounds");
    AppliedSelector result{roles[selector.role], {}};
    for (auto index : selector.native) {
      if (index >= (selector.output ? operation.getNumResults()
                                    : operation.getNumOperands()))
        return error("source.interface",
                     "application selector value is out of bounds");
      result.values.push_back(selector.output ? operation.getResult(index)
                                              : operation.getOperand(index));
    }
    return result;
  }
  Expected<SmallVector<AppliedSelector>>
  bind(protocol_ir::ApplyOp operation, ArrayRef<unsigned> roles,
       const InterfaceApplication &application) {
    SmallVector<AppliedSelector> result;
    for (const auto &selector : application.operands) {
      auto selected = bind(operation, roles, selector);
      if (!selected)
        return selected.takeError();
      result.push_back(std::move(*selected));
    }
    return result;
  }
  Error apply(const InterfaceProtocol &caller, protocol_ir::ApplyOp op) {
    auto found = protocols.find(op.getCallee());
    if (found == protocols.end())
      return error("source.interface", "application callee is absent");
    const auto &callee = *found->second;
    if (!charge(path.size() + op.getRoles().size() + 1))
      return limit();
    if (op.getRoles().size() != callee.roles.size())
      return error("source.interface", "application role count differs");
    SmallVector<unsigned> roles;
    SmallSet<unsigned, 8> seen;
    for (auto role : op.getRoles()) {
      auto name = mlir::cast<mlir::StringAttr>(role).getValue();
      if (!charge(caller.roles.size()))
        return limit();
      auto found = llvm::find(caller.roles, name);
      if (found == caller.roles.end())
        return error("source.interface", "application role is absent");
      unsigned index = found - caller.roles.begin();
      if (!seen.insert(index).second)
        return error("source.interface", "application roles are not distinct");
      roles.push_back(index);
    }
    std::vector<AppliedClause> clauses;
    for (const auto &clause : callee.clauses) {
      if (!charge(1))
        return limit();
      auto subject = bind(op, roles, clause.subject);
      if (!subject)
        return subject.takeError();
      AppliedClause binding{clause, std::move(*subject), {}, {}};
      if (clause.residual) {
        auto residual = bind(op, roles, *clause.residual);
        if (!residual)
          return residual.takeError();
        binding.residual = std::move(*residual);
      }
      if (clause.decision) {
        auto decision = bind(op, roles, *clause.decision);
        if (!decision)
          return decision.takeError();
        binding.decision = std::move(*decision);
      }
      clauses.push_back(std::move(binding));
    }
    return visitor({view, caller, callee, op, path, roles, clauses});
  }
  Error block(const InterfaceProtocol &caller, mlir::Block &body) {
    if (path.size() >= limits.parseDepth)
      return limit();
    path.push_back(0);
    for (auto &op : body) {
      if (!charge(1 + op.getNumOperands() + op.getNumResults()))
        return limit();
      if (auto application = mlir::dyn_cast<protocol_ir::ApplyOp>(op)) {
        if (auto error = apply(caller, application))
          return error;
      } else if (auto repeat = mlir::dyn_cast<protocol_ir::RepeatOp>(op)) {
        if (auto error = block(caller, repeat.getBody().front()))
          return error;
      } else if (op.getNumRegions()) {
        return error("source.interface", "unclassified application region");
      }
      ++path.back();
    }
    path.pop_back();
    return Error::success();
  }

public:
  Inspection(const LanguageInterface &view, const Limits &limits,
             function_ref<Error(const ApplicationOccurrence &)> visitor)
      : view(view), limits(limits), visitor(visitor), remaining(limits.work) {}
  Error run(mlir::ModuleOp module) {
    for (const auto &protocol : view.protocols) {
      if (!charge(protocol.symbol.size() + 1))
        return limit();
      protocols.try_emplace(protocol.symbol, &protocol);
    }
    auto native =
        mlir::cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    for (auto function :
         native.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
      auto found = protocols.find(function.getSymName());
      if (found == protocols.end())
        return error("source.interface", "caller definition is absent");
      if (auto error = block(*found->second, function.getBody().front()))
        return error;
    }
    return Error::success();
  }
};
} // namespace
Error inspectApplications(
    StringRef original, StringRef interface,
    function_ref<Error(const ApplicationOccurrence &)> visitor,
    const Limits &limits, ArrayRef<Asset> assets) {
  return detail::withInterface(
      original, interface, limits, assets,
      [&](mlir::ModuleOp module, LanguageInterface &&view) {
        return Inspection(view, limits, visitor).run(module);
      });
}
Error inspectApplications(
    const CheckedOriginal &original,
    function_ref<Error(const ApplicationOccurrence &)> visitor,
    const Limits &limits) {
  return detail::withInterface(
      original, limits,
      [&](mlir::ModuleOp module, const LanguageInterface &view) {
        return Inspection(view, limits, visitor).run(module);
      });
}
} // namespace zkc::language
