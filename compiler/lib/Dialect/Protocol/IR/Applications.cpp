#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include <functional>
using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "protocol-application", reason);
}
} // namespace
LogicalResult
protocol_ir::ApplyOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto callee =
      tables.lookupNearestSymbolFrom<MathematicalOp>(*this, getCalleeAttr());
  auto caller = (*this)->getParentOfType<MathematicalOp>();
  if (!callee || !caller || callee->getParentOp() != caller->getParentOp() ||
      failed(callee->getName().verifyInvariants(callee)) ||
      !hasSingleElement(callee.getBody()) || callee.getBody().front().empty() ||
      callee.getInputRoles().size() !=
          callee.getFunctionType().getNumInputs() ||
      callee.getOutputRoles().size() !=
          callee.getFunctionType().getNumResults() ||
      !llvm::equal(getOperandTypes(), callee.getFunctionType().getInputs()) ||
      !llvm::equal(getResultTypes(), callee.getFunctionType().getResults()) ||
      getRoles().size() != callee.getRoles().size())
    return refuse(*this, "requires a matching common protocol interface");
  llvm::DenseSet<Attribute> seen;
  for (auto role : getRoles())
    if (!is_contained(caller.getRoles(), role) || !seen.insert(role).second)
      return refuse(
          *this, "role substitution must be injective into the caller roster");
  for (auto sets : {callee.getInputRoles(), callee.getOutputRoles()})
    for (auto item : sets) {
      auto set = dyn_cast<ArrayAttr>(item);
      if (!set || set.empty())
        return refuse(*this, "invalid callee role interface");
      for (auto role : set)
        if (!is_contained(callee.getRoles(), role))
          return refuse(*this, "invalid callee role interface");
    }
  // Statements bind entry ports and entry decisions; silently rebinding them
  // through an application would assert a different predicate.
  if (!callee.getBody().front().getOps<StatementOp>().empty())
    return refuse(*this,
                  "entry statement bindings cannot be applied as a component");
  // Entry completion has an entry-relative result tuple. Expanding it as a
  // component would silently change the target and potentially the signature.
  if (callee.walk([](FinishIfOp) { return WalkResult::interrupt(); })
          .wasInterrupted())
    return refuse(
        *this, "conditional entry completion cannot be applied as a component");
  if (getSite().size() > 4096)
    return refuse(*this, "application site exceeds 4096 bytes");
  return success();
}
namespace mathematical {
LogicalResult verifyApplications(protocol_ir::ProtocolModuleOp module) {
  struct Summary {
    uint64_t work;
    unsigned depth;
    uint64_t indices = 0, sites = 0, siteBytes = 0, longestSite = 0;
  };
  llvm::DenseMap<Operation *, Summary> summaries;
  llvm::DenseSet<Operation *> active;
  SymbolTableCollection tables;
  std::function<LogicalResult(Operation *)> visit =
      [&](Operation *function) -> LogicalResult {
    if (summaries.count(function))
      return success();
    if (!active.insert(function).second)
      return refuse(function, "static applications must be acyclic");
    if (active.size() > 64)
      return refuse(function, "application depth exceeds 64");
    Summary summary{0, 1};
    SmallVector<Operation *> operations;
    function->getRegion(0).walk<WalkOrder::PreOrder>(
        [&](Operation *op) { operations.push_back(op); });
    for (auto *operation : operations) {
      auto &op = *operation;
      uint64_t work = 1;
      summary.indices += op.getNumOperands() + op.getNumResults();
      if (auto roles = op.getAttrOfType<ArrayAttr>("roles"))
        summary.indices += roles.size();
      if (auto site = op.getAttrOfType<StringAttr>("site")) {
        ++summary.sites;
        summary.siteBytes += site.size();
        summary.longestSite =
            std::max(summary.longestSite, uint64_t(site.size()));
      }
      if (auto call = dyn_cast<protocol_ir::ApplyOp>(op)) {
        if (failed(call.verifySymbolUses(tables)))
          return failure();
        auto callee =
            tables.lookupNearestSymbolFrom<protocol_ir::MathematicalOp>(
                call, call.getCalleeAttr());
        if (failed(visit(callee)))
          return failure();
        auto nested = summaries.lookup(callee);
        work += nested.work + call.getNumOperands() + call.getNumResults();
        summary.depth = std::max(summary.depth, nested.depth + 1);
        // Count SSA slots and role selectors as well as operations. A small
        // number of variadic operations can otherwise allocate enormous IR.
        summary.indices +=
            nested.indices + 2 * (call.getNumOperands() + call.getNumResults());
        for (auto sets : {callee.getInputRoles(), callee.getOutputRoles()})
          for (auto owners : sets)
            summary.indices += cast<ArrayAttr>(owners).size();
        // Outer applications first prefix nested application sites. Their
        // decimal length can therefore grow before the nested call expands.
        // Four digits bound every admitted site (at most 4096 bytes).
        uint64_t prefix = 8 + 4 + call.getSite().size();
        summary.sites += nested.sites;
        summary.siteBytes += nested.siteBytes + nested.sites * prefix;
        if (nested.sites)
          summary.longestSite =
              std::max(summary.longestSite, nested.longestSite + prefix);
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto helper = tables.lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
        // The enclosing verifier has already admitted every pure helper.
        if (!helper)
          return refuse(call, "requires a matching pure helper");
        if (failed(visit(helper)))
          return failure();
        auto nested = summaries.lookup(helper);
        work += nested.work;
        summary.indices += nested.indices;
        summary.depth = std::max(summary.depth, nested.depth + 1);
      }
      if (work > 100000 - summary.work || summary.depth > 64)
        return refuse(
            function,
            "application expansion exceeds 100000 operations or depth 64");
      if (summary.indices > 1000000 || summary.siteBytes > 16 * 1024 * 1024 ||
          summary.longestSite > 4096)
        return refuse(
            function,
            "application expansion exceeds SSA or site storage budget");
      summary.work += work;
    }
    active.erase(function);
    summaries[function] = summary;
    return success();
  };
  uint64_t total = 0, indices = 0, siteBytes = 0;
  for (auto function :
       module.getBody().front().getOps<protocol_ir::MathematicalOp>()) {
    if (failed(visit(function)))
      return failure();
    auto work = summaries.lookup(function).work;
    if (work > 100000 - total)
      return refuse(module,
                    "module application expansion exceeds 100000 operations");
    total += work;
    indices += summaries.lookup(function).indices;
    siteBytes += summaries.lookup(function).siteBytes;
    if (indices > 1000000 || siteBytes > 16 * 1024 * 1024)
      return refuse(
          module,
          "module application expansion exceeds SSA or site storage budget");
  }
  return success();
}
} // namespace mathematical
} // namespace zkc
