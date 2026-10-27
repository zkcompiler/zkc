#include "../HelperNormalization.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecDialect.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/SetVector.h"

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
} // namespace

OwningOpRef<mlir::ModuleOp> closeComputation(func::FuncOp source,
                                             uint64_t &remaining) {
  if (!source || !source->getParentOp() ||
      !source->getParentOp()->hasTrait<OpTrait::SymbolTable>())
    return {};
  SymbolTable symbols(source->getParentOp());
  llvm::SetVector<Operation *> closure;
  closure.insert(source);
  for (unsigned i = 0; i < closure.size(); ++i)
    if (failed(dependencies(closure[i], symbols, closure, remaining)))
      return {};
  OpBuilder builder(source.getContext());
  OwningOpRef<mlir::ModuleOp> unit(
      mlir::ModuleOp::create(builder, source.getLoc(), "_computation"));
  unit->getOperation()->setAttr("exec.computation", builder.getUnitAttr());
  builder.setInsertionPointToEnd(unit->getBody());
  for (Operation *declaration : closure) {
    if (!chargeCopy(declaration, remaining))
      return {};
    auto *copy = builder.clone(*declaration);
    if (declaration == source.getOperation())
      cast<func::FuncOp>(copy).setPublic();
  }
  if (failed(verifyKernelClosure(source->getParentOp(), source, *unit)) ||
      failed(mathematical::verifyComputationUnit(*unit)))
    return {};
  return unit;
}

func::FuncOp resolveInvocation(Operation *call,
                               SymbolTableCollection &symbols) {
  if (auto scoped = dyn_cast_or_null<exec::ComputeOp>(call))
    return scoped.resolveCallee(symbols);
  return {};
}

LogicalResult formCalculation(func::FuncOp wrapper, Operation *sourceOwner,
                              MathematicalSelectionPolicy policy,
                              std::optional<CalculationGuard> guard) {
  if (!wrapper.getBody().hasOneBlock())
    return refuse(wrapper, "expected one mathematical wrapper block");
  auto &body = wrapper.front();
  auto returned = dyn_cast<func::ReturnOp>(body.back());
  if (!returned)
    return refuse(wrapper, "expected a returning mathematical wrapper");
  if (guard &&
      (!guard->condition || guard->condition.getParentBlock() != &body ||
       !guard->condition.getType().isSignlessInteger(1) || !guard->site ||
       guard->site.getValue().empty()))
    return refuse(wrapper, "guard requires a wrapper condition and occurrence");
  SmallVector<Operation *> operations;
  for (auto &op : body.without_terminator()) {
    if (!mathematical::isTotal(&op) && !isa<func::CallOp>(op))
      return refuse(wrapper, "entry must contain original total mathematics");
    operations.push_back(&op);
  }
  SymbolTable outer(wrapper->getParentOp()), sourceSymbols(sourceOwner);
  OpBuilder builder(wrapper);
  auto outputs = SmallVector<Value>(returned.getOperands());
  unsigned condition = outputs.size();
  if (guard) {
    condition =
        std::distance(outputs.begin(), llvm::find(outputs, guard->condition));
    if (condition == outputs.size())
      outputs.push_back(guard->condition);
  }
  SmallVector<Type> types(ValueRange(outputs).getTypes());
  SymbolRefAttr callee;
  if (!operations.empty()) {
    auto name = fresh(outer, (wrapper.getSymName() + "_computation").str());
    auto unit = mlir::ModuleOp::create(builder, wrapper.getLoc(), name);
    unit->setAttr("exec.computation", builder.getUnitAttr());
    builder.setInsertionPointToEnd(unit.getBody());
    auto entryName = fresh(sourceSymbols, "_entry");
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
    SmallVector<Value> values;
    for (auto value : outputs)
      values.push_back(mapping.lookup(value));
    func::ReturnOp::create(builder, wrapper.getLoc(), values);
    llvm::SetVector<Operation *> pending;
    uint64_t remaining = 1000000;
    if (failed(dependencies(entry, sourceSymbols, pending, remaining)))
      return refuse(wrapper,
                    "unresolved or excessive mathematical dependencies");
    for (unsigned index = 0; index < pending.size(); ++index) {
      auto *source = pending[index];
      if (failed(dependencies(source, sourceSymbols, pending, remaining)))
        return refuse(wrapper,
                      "unresolved or excessive mathematical dependencies");
      builder.setInsertionPointToEnd(unit.getBody());
      builder.clone(*source);
    }
    callee = SymbolRefAttr::get(
        builder.getContext(), name,
        {FlatSymbolRefAttr::get(builder.getContext(), entryName)});
  }
  auto resultTypes = SmallVector<Type>(wrapper.getResultTypes());
  auto inputs = SmallVector<Type>(wrapper.getArgumentTypes());
  inputs.insert(inputs.begin(), runtime::ScopeType::get(builder.getContext()));
  wrapper.setType(builder.getFunctionType(
      inputs, {exec::OutcomeType::get(builder.getContext(), resultTypes)}));
  wrapper.setNoInline(true);
  auto *replacement = new Block;
  wrapper.getBody().push_back(replacement);
  replacement->addArguments(
      inputs, SmallVector<Location>(inputs.size(), wrapper.getLoc()));
  std::unique_ptr<Block> originalBody(
      wrapper.getBody().getBlocks().remove(body.getIterator()));
  builder.setInsertionPointToEnd(replacement);
  exec::ScopedExecutionBuilder control(builder, wrapper);
  SmallVector<Value> results;
  if (callee) {
    results = control.invoke(
        exec::ComputeOp::getOperationName(), types,
        control.scoped(replacement->getArguments().drop_front()),
        {builder.getNamedAttr("callee", callee),
         builder.getNamedAttr("site", builder.getStringAttr("computation")),
         builder.getNamedAttr(
             "policy", builder.getArrayAttr(
                           {builder.getBoolAttr(policy.finiteBulk),
                            builder.getBoolAttr(policy.vectorReductionFusion),
                            builder.getBoolAttr(policy.collectFoldFusion)}))});
  } else {
    for (Value output : outputs)
      results.push_back(replacement->getArgument(
          1 + cast<BlockArgument>(output).getArgNumber()));
  }
  if (guard) {
    auto outline = [&](unsigned index) {
      OpBuilder::InsertionGuard restore(builder);
      builder.setInsertionPoint(wrapper);
      auto name = fresh(
          outer,
          (wrapper.getSymName() + (index ? "_reject" : "_continue")).str());
      auto region = func::FuncOp::create(
          builder, wrapper.getLoc(), name,
          builder.getFunctionType(
              {runtime::ScopeType::get(builder.getContext())},
              {exec::OutcomeType::get(builder.getContext(), {})}));
      outer.insert(region);
      region.setPrivate();
      region.setNoInline(true);
      region->setAttr("runtime.region", builder.getUnitAttr());
      region.addEntryBlock();
      builder.setInsertionPointToEnd(&region.front());
      exec::ScopedExecutionBuilder branch(builder, region);
      if (index)
        branch.reject("reject", guard->site.getValue());
      else
        branch.complete({});
      return region;
    };
    control.conditional(results[condition], {}, {}, "guard_control", outline);
  }
  control.returned(ArrayRef(results).take_front(resultTypes.size()));
  return success();
}

FailureOr<MathematicalSelectionPolicy>
selectionPolicy(Operation *call, MathematicalSelectionPolicy fallback) {
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
