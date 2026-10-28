#include "OracleCommonPlan.h"
#include "OracleVerificationContext.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
namespace pir = protocol_ir;
Error refuse() { return error("oracle-common-body"); }
bool block(const OracleCommonBlock &plan, Block &actual) {
  if (!equal(actual.getArgumentTypes(), plan.types) ||
      actual.getOperations().size() != plan.instructions.size())
    return false;
  llvm::DenseMap<unsigned, Value> values;
  for (auto [id, value] : zip(plan.arguments, actual.getArguments()))
    if (!values.try_emplace(id, value).second)
      return false;
  for (auto [expected, op] : zip(plan.instructions, actual)) {
    if (op.getName().getStringRef() != expected.name ||
        op.getAttrDictionary() != expected.attributes ||
        !equal(op.getResultTypes(), expected.types) ||
        op.getNumOperands() != expected.inputs.size() ||
        op.getNumRegions() != unsigned(bool(expected.region)))
      return false;
    for (auto [id, input] : zip(expected.inputs, op.getOperands()))
      if (!values.contains(id) || values.lookup(id) != input)
        return false;
    if (expected.region && (!hasSingleElement(op.getRegion(0)) ||
                            !block(*expected.region, op.getRegion(0).front())))
      return false;
    for (auto [id, value] : zip(expected.outputs, op.getResults()))
      if (!values.try_emplace(id, value).second)
        return false;
  }
  return true;
}
bool local(const OracleLocalRecipe &recipe, func::FuncOp actual,
           const SourceExecutionClosure &closure) {
  if (!actual || !actual.isPrivate() || actual->hasAttr("runtime.region") ||
      actual.getSymName() != recipe.name || actual.getNumResults() != 1 ||
      actual.getNumArguments() != recipe.inputs.size() + 1 ||
      !isa<runtime::ScopeType>(actual.getArgument(0).getType()) ||
      !equal(actual.getArgumentTypes().drop_front(), recipe.inputs))
    return false;
  auto outcome = dyn_cast<exec::OutcomeType>(actual.getResultTypes()[0]);
  if (!outcome || !equal(outcome.getPayload(), recipe.outputs))
    return false;
  auto found = closure.bodies.find(actual.getSymName().str());
  if (found == closure.bodies.end() ||
      found->second.size() != recipe.instructions.size() + 1)
    return false;
  SmallVector<Value> values(actual.getArguments().drop_front());
  for (auto [i, expected] : enumerate(recipe.instructions)) {
    const auto &step = found->second[i];
    auto op = dyn_cast<exec::ApplyOp>(step.operation);
    if (!op || !step.regions.empty() ||
        step.inputs.size() != expected.inputs.size() ||
        !equal(ValueRange(step.outputs).getTypes(), expected.types) ||
        op.getSite() != "step_" + std::to_string(i) ||
        op.getParameters().size() != expected.parameters.size())
      return false;
    for (auto [id, input] : zip(expected.inputs, step.inputs))
      if (id >= values.size() || values[id] != input)
        return false;
    for (auto [attribute, parameter] :
         zip(op.getParameters(), expected.parameters))
      if (cast<StringAttr>(attribute).getValue() != parameter)
        return false;
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (!binding || binding.getContract() != expected.binding.contract ||
        binding.getImplementation() != expected.binding.implementation ||
        binding.getArguments().size() != expected.binding.arguments.size())
      return false;
    for (auto [attribute, argument] :
         zip(binding.getArguments(), expected.binding.arguments))
      if (cast<StringAttr>(attribute).getValue() != argument)
        return false;
    append_range(values, step.outputs);
  }
  const auto &last = found->second.back();
  if (!isa<exec::ReturnOp>(last.operation) || !last.regions.empty() ||
      last.inputs.size() != recipe.results.size())
    return false;
  for (auto [id, input] : zip(recipe.results, last.inputs))
    if (id >= values.size() || values[id] != input)
      return false;
  return true;
}
// Every extra declaration is reachable from a checked generated primitive or
// the realized entry. Original declarations retain their exact body. A spare
// implementation cannot hide behind an unused symbol in a checked candidate.
bool inventory(pir::ProtocolModuleOp source, pir::ProtocolModuleOp candidate,
               ArrayRef<std::string> entries, ArrayRef<Operation *> roots) {
  llvm::StringSet<> original, allowed;
  for (auto &op : source.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    if (!name)
      return false;
    original.insert(name.getValue());
    if (isa<pir::OracleDefinitionOp>(op)) {
      if (SymbolTable::lookupSymbolIn(candidate, name))
        return false;
      continue;
    }
    auto *actual = SymbolTable::lookupSymbolIn(candidate, name);
    if (!actual || (!is_contained(entries, name.getValue()) &&
                    !OperationEquivalence::isEquivalentTo(
                        &op, actual, OperationEquivalence::IgnoreLocations)))
      return false;
    allowed.insert(name.getValue());
  }
  SmallVector<Operation *> pending(roots.begin(), roots.end());
  for (const auto &entry : entries)
    pending.push_back(SymbolTable::lookupSymbolIn(candidate, entry));
  llvm::DenseSet<Operation *> seen;
  while (!pending.empty()) {
    auto *op = pending.pop_back_val();
    if (!op || !seen.insert(op).second)
      continue;
    auto name = SymbolTable::getSymbolName(op);
    if (!name || op->getParentOp() != candidate)
      return false;
    allowed.insert(name.getValue());
    if (!original.contains(name.getValue()))
      if (auto function = dyn_cast<func::FuncOp>(op)) {
        if (!function.isPrivate())
          return false;
        if (function.getNumArguments() &&
            isa<runtime::ScopeType>(function.getArgument(0).getType()) &&
            !function->hasAttr("runtime.region")) {
          Builder builder(candidate.getContext());
          auto expected =
              builder.getArrayAttr({name, builder.getArrayAttr({})});
          if (function->getAttr("runtime.origin") != expected)
            return false;
        }
      }
    bool good = true;
    op->walk([&](Operation *nested) {
      for (auto attribute : nested->getAttrs())
        attribute.getValue().walk([&](SymbolRefAttr symbol) {
          if (!symbol.getNestedReferences().empty()) {
            good = false;
            return;
          }
          auto *target =
              SymbolTable::lookupSymbolIn(candidate, symbol.getRootReference());
          if (!target) {
            good = false;
            return;
          }
          auto targetName = SymbolTable::getSymbolName(target).getValue();
          if (original.contains(targetName))
            return;
          if (!isa<func::FuncOp, runtime::BindingOp>(target)) {
            good = false;
            return;
          }
          pending.push_back(target);
        });
    });
    if (!good)
      return false;
  }
  for (auto &op : candidate.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&op);
    if (!name || !allowed.contains(name.getValue()))
      return false;
  }
  return true;
}
} // namespace
Error checkIdealOracleRealization(ModuleOp prepared,
                                  const OracleCommonRealization &actual) {
  auto entries = idealOracleEntries(prepared);
  if (!entries)
    return entries.takeError();
  ModuleOp actualModule = actual.module.get();
  if (!actualModule || actualModule == prepared ||
      actualModule.getContext() != prepared.getContext() ||
      actualModule->getAttrDictionary() != prepared->getAttrDictionary() ||
      !hasSingleElement(actualModule.getBody()->getOperations()) ||
      actual.entries.size() != entries->size())
    return refuse();
  auto sourceContext = OracleVerificationContext::read(prepared);
  if (!sourceContext)
    return sourceContext.takeError();
  auto targetContext = OracleVerificationContext::read(actualModule);
  if (!targetContext) {
    consumeError(targetContext.takeError());
    return refuse();
  }
  auto source = sourceContext->getUnit();
  auto candidate = targetContext->getUnit();
  if (source->getAttrDictionary() != candidate->getAttrDictionary())
    return refuse();
  SmallVector<Operation *> roots;
  auto root = [&](func::FuncOp function) {
    if (function)
      roots.push_back(function);
  };
  for (auto [entry, realized] : zip(*entries, actual.entries)) {
    if (entry != realized.entry)
      return refuse();
    auto requirements = idealOracleRequirements(prepared, entry);
    if (!requirements)
      return requirements.takeError();
    if (realized.controllers.size() != requirements->controllers.size() ||
        realized.allocators.size() != requirements->storage.constructors.size())
      return refuse();
    for (auto [expected, item] :
         zip(requirements->controllers, realized.controllers)) {
      if (expected.role != item.role || expected.kind != item.kind ||
          expected.access != item.access)
        return refuse();
      if (auto e = checkOracleQueryController(
              *targetContext, *sourceContext, requirements->storage, item.role,
              item.kind, requirements->capacity, item.body, item.access))
        return e;
      const auto &body = item.body;
      root(body.initialize);
      root(body.advance);
      root(body.finish);
      root(body.evaluate);
      root(body.contents);
      for (auto helper : body.resume)
        root(helper);
      for (auto helper : body.rowCounts)
        root(helper);
      for (auto helper : body.leafCounts)
        root(helper);
      for (auto helper : body.constructionCounts)
        root(helper);
      for (const auto &constructor : body.constructors) {
        root(constructor.lookup);
        root(constructor.functions.answer);
        for (const auto &query : constructor.functions.queries)
          root(query.position);
      }
    }
    for (auto [ordinal, constructor] :
         enumerate(requirements->storage.constructors)) {
      if (realized.allocators[ordinal].size() != constructor.roles.size())
        return refuse();
      for (auto [role, helper] : enumerate(realized.allocators[ordinal])) {
        if (auto e = checkOracleAnchorAllocator(
                *targetContext, helper, requirements->storage, ordinal, role))
          return e;
        root(helper);
      }
    }
    auto plan =
        planIdealOracleCommon(prepared, entry, *requirements,
                              realized.controllers, realized.allocators);
    if (!plan)
      return plan.takeError();
    auto program = dyn_cast_or_null<pir::MathematicalOp>(
        SymbolTable::lookupSymbolIn(candidate, entry));
    if (!program || program->getAttrDictionary() != plan->attributes ||
        !hasSingleElement(program.getBody()) ||
        !block(plan->body, program.getBody().front()) ||
        realized.locals.size() != plan->locals.size())
      return refuse();
    const auto &closure = targetContext->getClosure();
    for (auto [recipe, helper] : zip(plan->locals, realized.locals)) {
      if (!local(recipe, helper, closure))
        return refuse();
      root(helper);
    }
  }
  if (!inventory(source, candidate, *entries, roots))
    return refuse();
  return Error::success();
}
} // namespace zkc::protocol
