#include "zkc/Transforms/VectorReductions.h"
#include "AlgorithmSupport.h"
#include "CheckedCandidate.h"
#include "ComputationSelection.h"
#include "MathematicalSupport.h"
#include "RealizationTrace.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/detail/Builders.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
using Record = protocol::detail::AlgorithmExpansionRecord;
using Occurrence = protocol::detail::AlgorithmOccurrence;
using StateAccess = protocol::detail::AlgorithmStateAccess;
using Reductions = std::map<std::string, SelectedReduction>;

protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return {};
  auto root =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  return root && root.getProfile() == protocol_ir::Profile::Protocol
             ? root
             : protocol_ir::ProtocolModuleOp();
}
LogicalResult refuse(Operation *op, StringRef reason) {
  return diagnostics::emit(op->emitOpError(), "vector-reduction-correspondence",
                           reason);
}
bool fieldBound(StringRef contract) {
  return !contract.starts_with("index.") && contract != "control.require";
}
ArrayAttr arguments(MLIRContext *context, StringRef contract, StringRef field) {
  return ArrayAttr::get(
      context, fieldBound(contract)
                   ? ArrayRef<Attribute>{StringAttr::get(context, field)}
                   : ArrayRef<Attribute>{});
}
// Symbol allocation is a naming convention only, shared with the reader. It
// grants no operation or formula semantics and creates no candidate IR.
class BindingNames {
  llvm::StringSet<> names;
  std::map<std::pair<std::string, std::string>, std::string> assigned;
  unsigned next = 0;

public:
  explicit BindingNames(protocol_ir::ProtocolModuleOp root) {
    for (Operation &op : root.getBody().front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  StringRef get(StringRef contract, StringRef field) {
    auto key =
        std::make_pair(contract.str(), fieldBound(contract) ? field.str() : "");
    auto found = assigned.find(key);
    if (found != assigned.end())
      return found->second;
    std::string name;
    do {
      name = "_vector_reduction_binding_" + std::to_string(next++);
    } while (!names.insert(name).second);
    return assigned.emplace(std::move(key), std::move(name)).first->second;
  }
};

// Exact native contract recognition, never a source reducer spelling. The
// typed operation and its resolved logical binding must both agree.
algebra::MapRealizeOp reductionMap(local::ApplyOp call, SymbolTable &symbols,
                                   OptimizationOutcome *outcome = nullptr) {
  if (outcome)
    *outcome = {OptimizationStatus::Unsupported,
                OptimizationReason::CallEligibility};
  if (!call || call->getNumResults() != 1 || !call->getResult(0).hasOneUse())
    return {};
  auto map = symbols.lookup<algebra::MapRealizeOp>(call.getCallee());
  auto sum = dyn_cast_if_present<algebra::VectorSumOp>(call->getNextNode());
  if (!map || !sum || sum->getNumOperands() != 1 ||
      sum->getOperand(0) != call->getResult(0))
    return {};
  auto reference = sum->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto binding =
      reference
          ? symbols.lookup<local::OperationBindingOp>(reference.getValue())
          : local::OperationBindingOp();
  auto field = cast<algebra::FieldType>(sum->getResult(0).getType());
  if (!binding || binding.getContract() != "vector.sum" ||
      !binding.getImplementation().empty() ||
      binding.getArguments() !=
          arguments(call.getContext(), "vector.sum", field.getDomain()) ||
      sum->getAttrOfType<ArrayAttr>("parameters") !=
          ArrayAttr::get(call.getContext(), {})) {
    if (outcome && binding && !binding.getImplementation().empty())
      *outcome = {OptimizationStatus::ReplacementRestricted,
                  OptimizationReason::ImplementationRestriction};
    return {};
  }
  if (outcome)
    *outcome = OptimizationOutcome::success();
  return map;
}

class Rewriter {
  protocol_ir::ProtocolModuleOp root;
  SymbolTable symbols;
  BindingNames names;
  llvm::StringSet<> emitted;
  OpBuilder builder;
  Record &record;
  RealizationScope &scope;
  bool &changed;

public:
  Rewriter(protocol_ir::ProtocolModuleOp root, Record &record,
           RealizationScope &scope, bool &changed)
      : root(root), symbols(root), names(root), builder(root.getContext()),
        record(record), scope(scope), changed(changed) {}
  LogicalResult
  run(const Reductions &reductions,
      const std::map<std::string, OptimizationOutcome> &decisions) {
    SmallVector<local::ApplyOp> calls;
    root.walk([&](local::ApplyOp call) { calls.push_back(call); });
    for (auto call : calls) {
      OptimizationOutcome outcome;
      auto map = reductionMap(call, symbols, &outcome);
      if (!map || !reductions.count(call.getCallee().str())) {
        // Map-product and missing-recipe decisions were recorded at the
        // declaration. This occurrence additionally records actual eligibility.
        if (map) {
          auto found = decisions.find(call.getCallee().str());
          outcome = found == decisions.end()
                        ? OptimizationOutcome{OptimizationStatus::Unsupported,
                                              OptimizationReason::Equation}
                        : found->second;
        }
        scope.selection(call, record, DecisionFamily::VectorReduction,
                        RealizationChoice::Ordered, outcome);
        continue;
      }
      scope.selection(call, record, DecisionFamily::VectorReduction,
                      RealizationChoice::MapSum,
                      OptimizationOutcome::success());
      if (!changed)
        scope.propose();
      changed = true;
      auto function = call->getParentOfType<local::FuncOp>();
      auto saved = protocol::detail::occurrence(record, function.getSymName(),
                                                protocol::attr(call, "site"));
      if (!saved)
        return refuse(call, "missing retained occurrence");
      Occurrence origin = *saved;
      origin.path.emplace_back(origin.originalSite, map.getHelper().str());
      origin.definition = map.getHelper().str();
      origin.declaration = map.getSymName().str();
      ++origin.depth;
      if (origin.depth > 64 || origin.path.size() > 64)
        return diagnostics::emit(call.emitOpError(), "interactive-call-depth");
      record.occurrences.erase(
          {function.getSymName().str(), protocol::attr(call, "site").str()});
      Operation *sum = call->getNextNode();
      auto field = cast<algebra::FieldType>(sum->getResult(0).getType());
      builder.setInsertionPoint(call);
      unsigned nextSite = 0;
      auto emit = [&](StringRef contract, ValueRange inputs, Type output,
                      bool guard) -> Operation * {
        if (!record.work) {
          scope.failure(RequiredFailure{
              "fusion emission work",
              CapacityCause{WorkOwner::AlgorithmExpansion, 1, record.work}});
          diagnostics::emit(call.emitOpError(), "algorithm-expansion-limit");
          return nullptr;
        }
        --record.work;
        auto name = names.get(contract, field.getDomain());
        if (emitted.insert(name).second) {
          OpBuilder::InsertionGuard position(builder);
          builder.setInsertionPointToStart(&root.getBody().front());
          local::OperationBindingOp::create(
              builder, map.getLoc(), name, contract,
              arguments(root.getContext(), contract, field.getDomain()), "");
        }
        std::string site = protocol::attr(sum, "site").str();
        if (guard) {
          origin.originalSite = "map_" + std::to_string(nextSite++);
          auto encoded = protocol::algorithmSite(
              origin.path, origin.originalSite, record.originBytes);
          if (!encoded) {
            scope.failure(RequiredFailure{
                "fusion origin encoding",
                CapacityCause{
                    WorkOwner::AlgorithmOriginBytes, {}, record.originBytes}});
            diagnostics::emit(call.emitOpError(), encoded.takeError());
            return nullptr;
          }
          site = std::move(*encoded);
          if (!record.occurrences
                   .emplace(
                       protocol::detail::OccurrenceKey{
                           function.getSymName().str(), site},
                       origin)
                   .second) {
            (void)refuse(call, "colliding generated occurrence");
            return nullptr;
          }
        }
        OperationState state(guard ? map.getLoc() : sum->getLoc(),
                             protocol::boundOperationName(contract));
        state.addOperands(inputs);
        if (output)
          state.addTypes(output);
        state.addAttribute("binding",
                           FlatSymbolRefAttr::get(root.getContext(), name));
        state.addAttribute("site", builder.getStringAttr(site));
        state.addAttribute("parameters", builder.getArrayAttr({}));
        return builder.create(state);
      };
      Value rows;
      auto index =
          IntegerType::get(root.getContext(), 64, IntegerType::Unsigned);
      for (auto [i, row] : enumerate(map.getRowwise())) {
        if (!row)
          continue;
        auto length = emit("vector.length", call->getOperand(i), index, true);
        if (!length)
          return failure();
        if (!rows)
          rows = length->getResult(0);
        else {
          auto equal = emit("index.equal", {rows, length->getResult(0)},
                            builder.getI1Type(), true);
          if (!equal || !emit("control.require", equal->getResult(0), {}, true))
            return failure();
        }
      }
      const auto &reduction = reductions.at(map.getSymName().str());
      SmallVector<Value> inputs;
      for (unsigned input : reduction.inputs)
        inputs.push_back(call->getOperand(input));
      auto reduced = emit(reduction.recipe->target, inputs, field, false);
      if (!reduced)
        return failure();
      sum->getResult(0).replaceAllUsesWith(reduced->getResult(0));
      sum->erase();
      call.erase();
    }
    return success();
  }
};

// A reader of the actual candidate, using source SSA substitution. It neither
// builds replacement IR nor calls Rewriter. Unselected pairs must be identical.
class Correspondence {
  using Values = llvm::DenseMap<Value, Value>;
  SymbolTable originalSymbols, candidateSymbols;
  BindingNames names;
  const Record &input;
  Record expected;
  llvm::DenseSet<Operation *> addedBindings;
  std::string function;

  bool charge() {
    if (!expected.checkWork)
      return false;
    --expected.checkWork;
    return true;
  }
  LogicalResult bind(ValueRange before, ValueRange after, Values &values) {
    if (before.size() != after.size())
      return failure();
    for (auto [a, b] : zip(before, after)) {
      if (a.getType() != b.getType())
        return failure();
      values[a] = b;
    }
    return success();
  }
  LogicalResult replacement(local::ApplyOp call, algebra::MapRealizeOp map,
                            Operation *sum, Block &target,
                            Block::iterator &cursor, Values &values) {
    auto saved = protocol::detail::occurrence(input, function,
                                              protocol::attr(call, "site"));
    if (!saved)
      return refuse(call, "missing retained occurrence");
    Occurrence origin = *saved;
    origin.path.emplace_back(origin.originalSite, map.getHelper().str());
    origin.definition = map.getHelper().str();
    origin.declaration = map.getSymName().str();
    ++origin.depth;
    if (origin.depth > 64 || origin.path.size() > 64)
      return refuse(call, "occurrence depth");
    expected.occurrences.erase({function, protocol::attr(call, "site").str()});
    auto field = cast<algebra::FieldType>(sum->getResult(0).getType());
    unsigned nextSite = 0;
    auto primitive = [&](StringRef contract, ValueRange operands, Type result,
                         bool guard) -> Operation * {
      if (!charge() || !expected.work || cursor == target.end())
        return nullptr;
      --expected.work;
      Operation *actual = &*cursor++;
      std::string site = protocol::attr(sum, "site").str();
      if (guard) {
        origin.originalSite = "map_" + std::to_string(nextSite++);
        auto encoded = protocol::algorithmSite(origin.path, origin.originalSite,
                                               expected.checkOriginBytes);
        if (!encoded) {
          consumeError(encoded.takeError());
          return nullptr;
        }
        auto measured = protocol::algorithmSite(
            origin.path, origin.originalSite, expected.originBytes);
        if (!measured) {
          consumeError(measured.takeError());
          return nullptr;
        }
        site = std::move(*encoded);
        if (!expected.occurrences
                 .emplace(protocol::detail::OccurrenceKey{function, site},
                          origin)
                 .second)
          return nullptr;
      }
      auto name = names.get(contract, field.getDomain());
      auto binding = candidateSymbols.lookup<local::OperationBindingOp>(name);
      if (!binding || binding.getContract() != contract ||
          !binding.getImplementation().empty() ||
          binding.getArguments() !=
              arguments(call.getContext(), contract, field.getDomain()) ||
          binding->getAttrs().size() != 4 ||
          actual->getName().getStringRef() !=
              protocol::boundOperationName(contract) ||
          actual->getNumRegions() ||
          actual->getNumResults() != unsigned(bool(result)) ||
          (result && actual->getResult(0).getType() != result) ||
          !llvm::equal(actual->getOperands(), operands) ||
          actual->getAttrs().size() != 3 ||
          protocol::attr(actual, "site") != site ||
          actual->getAttrOfType<FlatSymbolRefAttr>("binding") !=
              FlatSymbolRefAttr::get(call.getContext(), name) ||
          actual->getAttrOfType<ArrayAttr>("parameters") !=
              ArrayAttr::get(call.getContext(), {}))
        return nullptr;
      addedBindings.insert(binding);
      return actual;
    };
    Value rows;
    Type index = IntegerType::get(call.getContext(), 64, IntegerType::Unsigned);
    for (auto [i, row] : enumerate(map.getRowwise())) {
      if (!row)
        continue;
      auto operand = values.lookup(call->getOperand(i));
      if (!operand)
        return refuse(call, "unbound collection");
      auto length = primitive("vector.length", operand, index, true);
      if (!length)
        return refuse(call, "ordered row length");
      if (!rows)
        rows = length->getResult(0);
      else {
        auto equal = primitive("index.equal", {rows, length->getResult(0)},
                               IntegerType::get(call.getContext(), 1), true);
        if (!equal ||
            !primitive("control.require", equal->getResult(0), {}, true))
          return refuse(call, "ordered shape guard");
      }
    }
    SmallVector<Value> inputs;
    for (Value operand : call->getOperands()) {
      Value mapped = values.lookup(operand);
      if (!mapped)
        return refuse(call, "unbound map input");
      inputs.push_back(mapped);
    }
    if (cursor == target.end())
      return refuse(call, "missing reduction payload");
    Operation *payload = &*cursor;
    Operation *after = payload;
    auto result = compareMapSum(map, inputs, rows, after, candidateSymbols,
                                addedBindings, expected.checkWork);
    if (failed(result) || after != payload->getNextNode() ||
        payload->getNumResults() != 1 || *result != payload->getResult(0))
      return refuse(call, "reduction formula correspondence");
    auto dot = primitive("vector.dot", payload->getOperands(), field, false);
    if (!dot || failed(bind(sum->getResults(), dot->getResults(), values)))
      return refuse(call, "dot operation or result");
    return success();
  }
  LogicalResult block(Block &source, Block &target, unsigned depth) {
    if (depth > 64)
      return refuse(source.getParentOp(), "region depth");
    Values values;
    if (failed(bind(source.getArguments(), target.getArguments(), values)))
      return refuse(target.getParentOp(), "block arguments");
    auto cursor = target.begin();
    for (auto it = source.begin(); it != source.end(); ++it) {
      Operation &op = *it;
      if (!charge() || cursor == target.end())
        return refuse(&op, "work limit or missing operation");
      auto call = dyn_cast<local::ApplyOp>(op);
      auto map = reductionMap(call, originalSymbols);
      if (map && !isa<local::ApplyOp>(*cursor)) {
        Operation *sum = &*++it;
        if (failed(replacement(call, map, sum, target, cursor, values)))
          return failure();
        continue;
      }
      Operation &actual = *cursor++;
      if (op.getName() != actual.getName() ||
          op.getAttrDictionary() != actual.getAttrDictionary() ||
          op.getNumRegions() != actual.getNumRegions() ||
          op.getResultTypes() != actual.getResultTypes() ||
          op.getNumOperands() != actual.getNumOperands())
        return refuse(&actual, "surrounding operation");
      for (auto [a, b] : zip(op.getOperands(), actual.getOperands()))
        if (!values.lookup(a) || values.lookup(a) != b)
          return refuse(&actual, "surrounding operand or result substitution");
      for (auto [a, b] : zip(op.getRegions(), actual.getRegions()))
        if (!a.hasOneBlock() || !b.hasOneBlock() ||
            failed(block(a.front(), b.front(), depth + 1)))
          return refuse(&actual, "region correspondence");
      if (failed(bind(op.getResults(), actual.getResults(), values)))
        return refuse(&actual, "result correspondence");
    }
    return cursor == target.end()
               ? success()
               : refuse(target.getParentOp(), "extra operation");
  }

public:
  Correspondence(protocol_ir::ProtocolModuleOp original,
                 protocol_ir::ProtocolModuleOp candidate, const Record &input)
      : originalSymbols(original), candidateSymbols(candidate), names(original),
        input(input), expected(input) {}
  LogicalResult run(protocol_ir::ProtocolModuleOp original,
                    protocol_ir::ProtocolModuleOp candidate, Record &output) {
    llvm::DenseSet<Operation *> retained;
    for (Operation &op : original.getBody().front()) {
      if (!charge())
        return refuse(&op, "declaration work limit");
      auto name = SymbolTable::getSymbolName(&op);
      auto actual = name ? candidateSymbols.lookup(name.getValue()) : nullptr;
      if (!actual)
        return refuse(&op, "missing declaration");
      retained.insert(actual);
      if (auto local = dyn_cast<local::FuncOp>(op)) {
        auto replacement = dyn_cast<local::FuncOp>(actual);
        if (!replacement ||
            local->getAttrDictionary() != actual->getAttrDictionary() ||
            !local.getBody().hasOneBlock() ||
            !replacement.getBody().hasOneBlock())
          return refuse(actual, "local declaration");
        function = local.getSymName().str();
        if (failed(block(local.getBody().front(), replacement.getBody().front(),
                         0)))
          return failure();
      } else if (!OperationEquivalence::isEquivalentTo(
                     &op, actual, OperationEquivalence::IgnoreLocations))
        return refuse(actual, "changed declaration");
    }
    auto originalOrder = original.getBody().front().begin();
    for (Operation &op : candidate.getBody().front()) {
      if (retained.contains(&op)) {
        if (originalOrder == original.getBody().front().end() ||
            SymbolTable::getSymbolName(&*originalOrder++) !=
                SymbolTable::getSymbolName(&op))
          return refuse(&op, "retained declaration order");
      } else if (!addedBindings.contains(&op))
        return refuse(&op, "unexpected declaration");
    }
    if (!expected.sameExpansion(output))
      return refuse(candidate, "occurrence records or cumulative limits");
    output.checkWork = expected.checkWork;
    output.checkOriginBytes = expected.checkOriginBytes;
    return success();
  }
};
LogicalResult check(ModuleOp original, ModuleOp candidate, const Record &input,
                    Record &output) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  auto before = unit(original), after = unit(candidate);
  if (!input.retained || input.finished || !before || !after ||
      original->getAttrDictionary() != candidate->getAttrDictionary() ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse(candidate, "retained preparation context");
  return Correspondence(before, after, input).run(before, after, output);
}
} // namespace
LogicalResult verifyVectorReductionsPreserved(
    ModuleOp original, ModuleOp candidate,
    const protocol::AlgorithmExpansionState &originalState,
    const protocol::AlgorithmExpansionState &candidateState) {
  auto output = StateAccess::get(candidateState);
  return check(original, candidate, StateAccess::get(originalState), output);
}
LogicalResult fuseVectorReductions(ModuleOp module,
                                   protocol::AlgorithmExpansionState &state,
                                   RealizationTrace *trace) {
  return fuseVectorReductions(module, state, mathematicalRecipes().reductions,
                              trace);
}
LogicalResult fuseVectorReductions(ModuleOp module,
                                   protocol::AlgorithmExpansionState &state,
                                   ArrayRef<ReductionRecipe> reductionRecipes,
                                   RealizationTrace *trace) {
  RealizationScope scope(trace, "vector-reductions", module, {true, true});
  const auto &input = StateAccess::get(state);
  if (!input.retained || input.finished || !unit(module))
    return refuse(module, "expected retained preparation");
  if (failed(verify(module)))
    return failure();
  // Read every original formula, not just live or eligible applications.
  auto products = describeMapProducts(module, trace);
  if (failed(products))
    return failure();
  const MathematicalRecipes recipes{mathematicalRecipes().lanes,
                                    reductionRecipes};
  Reductions reductions;
  std::map<std::string, OptimizationOutcome> decisions;
  std::optional<SymbolTable> subjects;
  if (trace)
    subjects.emplace(unit(module));
  for (const auto &[name, product] : *products) {
    OptimizationOutcome outcome;
    auto selected = selectMapSum(product, recipes, &outcome);
    if (trace) {
      decisions.emplace(name, outcome);
      scope.selection(subjects->lookup(name), DecisionFamily::VectorReduction,
                      selected ? RealizationChoice::MapSum
                               : RealizationChoice::Ordered,
                      outcome);
    }
    if (selected)
      reductions.emplace(name, std::move(*selected));
  }
  mathematical::CheckedCandidate candidate(module);
  Record output = input;
  bool changed = false;
  if (failed(Rewriter(unit(*candidate), output, scope, changed)
                 .run(reductions, decisions)))
    return failure();
  scope.failure(VerificationDecision{VerificationObservation::Unclassified,
                                     "vector reduction correspondence",
                                     {},
                                     {}});
  if (failed(candidate.publish([&](ModuleOp before, ModuleOp after) {
        return check(before, after, input, output);
      })))
    return failure();
  StateAccess::set(state, std::move(output));
  if (changed)
    scope.publish();
  else
    scope.complete(CompletionKind::Unchanged);
  return success();
}
} // namespace zkc::mathematical
