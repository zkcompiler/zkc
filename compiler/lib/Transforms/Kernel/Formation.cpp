#include "../HelperNormalization.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "kernel-formation", detail);
}
std::string fresh(SymbolTable &symbols, StringRef base) {
  std::string name = base.str();
  unsigned suffix = 0;
  while (symbols.lookup(name))
    name = (base + "_" + Twine(suffix++)).str();
  return name;
}
// Standard symbol walking also sees references nested inside attributes. The
// unit's mathematical vocabulary admits only flat helper/domain dependencies.
LogicalResult dependencies(Operation *body, SymbolTable &symbols,
                           llvm::SetVector<Operation *> &pending,
                           uint64_t &remaining) {
  auto walk = body->walk([&](Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining)
      return WalkResult::interrupt();
    remaining -= cost;
    return WalkResult::advance();
  });
  if (walk.wasInterrupted())
    return failure();
  auto uses = SymbolTable::getSymbolUses(body);
  if (!uses)
    return failure();
  for (const auto &use : *uses) {
    auto reference = dyn_cast<FlatSymbolRefAttr>(use.getSymbolRef());
    if (!remaining || !reference)
      return failure();
    --remaining;
    auto *definition = symbols.lookup(reference.getValue());
    if (!isa_and_nonnull<func::FuncOp, data::DomainOp>(definition))
      return failure();
    pending.insert(definition);
  }
  return success();
}
std::string freshSite(local::FuncOp wrapper, StringRef prefix) {
  llvm::StringSet<> used;
  wrapper.walk([&](Operation *op) {
    if (auto site = op->getAttrOfType<StringAttr>("site"))
      used.insert(site.getValue());
  });
  std::string site = prefix.str();
  unsigned suffix = 0;
  while (used.contains(site))
    site = (prefix + "_recipe_" + Twine(suffix++)).str();
  return site;
}
void emitGuard(OpBuilder &builder, Location location, Value condition,
               StringAttr site, StringRef controlSite) {
  auto branch = local::LocalIfOp::create(builder, location, TypeRange{},
                                         ValueRange{condition}, controlSite);
  auto *yes = new Block;
  auto *no = new Block;
  branch.getThenRegion().push_back(yes);
  branch.getElseRegion().push_back(no);
  builder.setInsertionPointToEnd(yes);
  local::LocalYieldOp::create(builder, location, ValueRange{});
  builder.setInsertionPointToEnd(no);
  local::StopOp::create(builder, location, site.getValue(), "reject");
  builder.setInsertionPointAfter(branch);
}
} // namespace

LogicalResult formCalculation(local::FuncOp wrapper, Operation *sourceOwner,
                              MathematicalSelectionPolicy policy) {
  if (!wrapper.getBody().hasOneBlock())
    return refuse(wrapper, "expected one mathematical wrapper block");
  auto &body = wrapper.getBody().front();
  auto returned = dyn_cast<local::ReturnOp>(body.back());
  if (!returned)
    return refuse(wrapper, "expected a returning mathematical wrapper");
  SmallVector<Operation *> operations;
  local::GuardOp guard;
  for (auto &op : body.without_terminator()) {
    if (auto check = dyn_cast<local::GuardOp>(op)) {
      if (guard)
        return refuse(wrapper, "at most one trailing guard is admitted");
      guard = check;
    } else {
      if (guard || (!mathematical::isTotal(&op) && !isa<func::CallOp>(op)))
        return refuse(wrapper, "entry must contain original total mathematics");
      operations.push_back(&op);
    }
  }
  auto guardControl =
      guard ? freshSite(wrapper, "guard_control") : std::string();
  if (operations.empty() && guard) {
    OpBuilder builder(guard);
    emitGuard(builder, guard.getLoc(), guard.getCondition(),
              guard.getSiteAttr(), guardControl);
    guard.erase();
    return success();
  }
  SymbolTable outer(wrapper->getParentOp()), sourceSymbols(sourceOwner);
  OpBuilder builder(wrapper);
  auto name = fresh(outer, (wrapper.getSymName() + "_kernel").str());
  auto unit = ModuleOp::create(builder, wrapper.getLoc(), name);
  unit.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&unit.getBody().front());
  SmallVector<Value> outputs(returned.getInputs());
  unsigned condition = outputs.size();
  if (guard) {
    auto found = llvm::find(outputs, guard.getCondition());
    condition = std::distance(outputs.begin(), found);
    if (found == outputs.end())
      outputs.push_back(guard.getCondition());
  }
  SmallVector<Type> types;
  for (auto value : outputs)
    types.push_back(value.getType());
  auto entryName = fresh(sourceSymbols, "_kernel_entry");
  auto entry = func::FuncOp::create(
      builder, wrapper.getLoc(), entryName,
      builder.getFunctionType(wrapper.getArgumentTypes(), types));
  auto *entryBody = entry.addEntryBlock();
  builder.setInsertionPointToEnd(entryBody);
  IRMapping mapping;
  mapping.map(body.getArguments(), entryBody->getArguments());
  for (auto *op : operations) {
    auto *copy = builder.clone(*op, mapping);
    copy->removeAttr("site");
  }
  SmallVector<Value> results;
  for (auto value : outputs)
    results.push_back(mapping.lookup(value));
  func::ReturnOp::create(builder, wrapper.getLoc(), results);

  // Retain the original reachable helper/domain closure verbatim. Numerical
  // normalization belongs to the later checked Kernel realization edge.
  llvm::SetVector<Operation *> pending;
  uint64_t remaining = 1000000;
  if (failed(dependencies(entry, sourceSymbols, pending, remaining)))
    return refuse(wrapper, "dependency inspection limit or unresolved symbol");
  for (unsigned index = 0; index < pending.size(); ++index) {
    auto *source = pending[index];
    if (failed(dependencies(source, sourceSymbols, pending, remaining)))
      return refuse(wrapper,
                    "dependency inspection limit or unresolved symbol");
    builder.setInsertionPointToEnd(&unit.getBody().front());
    builder.clone(*source);
  }

  // Replace the mathematical wrapper by its ordered invocation and partial
  // control. No executable occurrence is assigned the call's own site.
  auto *replacement = new Block;
  wrapper.getBody().push_back(replacement);
  for (auto argument : body.getArguments())
    replacement->addArgument(argument.getType(), argument.getLoc());
  builder.setInsertionPointToEnd(replacement);
  OperationState state(wrapper.getLoc(), CallOp::getOperationName());
  state.addOperands(replacement->getArguments());
  state.addTypes(types);
  state.addAttribute(
      "callee", SymbolRefAttr::get(
                    builder.getContext(), name,
                    {FlatSymbolRefAttr::get(builder.getContext(), entryName)}));
  // Numerical names are derived later from this actual ordered invocation.
  std::string callSite = freshSite(wrapper, "kernel");
  state.addAttribute("site", builder.getStringAttr(callSite));
  state.addAttribute(
      "policy",
      builder.getArrayAttr({builder.getBoolAttr(policy.finiteBulk),
                            builder.getBoolAttr(policy.vectorReductionFusion),
                            builder.getBoolAttr(policy.collectFoldFusion)}));
  auto call = cast<CallOp>(builder.create(state));
  if (guard)
    emitGuard(builder, guard.getLoc(), call.getResult(condition),
              guard.getSiteAttr(), guardControl);
  local::ReturnOp::create(
      builder, wrapper.getLoc(),
      call.getResults().take_front(returned.getNumOperands()));
  body.erase();
  return success();
}

FailureOr<MathematicalSelectionPolicy>
selectionPolicy(CallOp call, MathematicalSelectionPolicy fallback) {
  if (auto raw = call->getAttr("policy")) {
    auto policy = dyn_cast<ArrayAttr>(raw);
    if (!policy || policy.size() != 3 || !isa<BoolAttr>(policy[0]) ||
        !isa<BoolAttr>(policy[1]) || !isa<BoolAttr>(policy[2]))
      return failure();
    return MathematicalSelectionPolicy{cast<BoolAttr>(policy[0]).getValue(),
                                       cast<BoolAttr>(policy[1]).getValue(),
                                       cast<BoolAttr>(policy[2]).getValue()};
  }
  return fallback;
}

} // namespace zkc::kernel
