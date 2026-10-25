#include "zkc/Transforms/VectorReductions.h"
#include "AlgorithmSupport.h"
#include "CheckedCandidate.h"
#include "ComputationSelection.h"
#include "MapOccurrence.h"
#include "MathematicalSupport.h"
#include "RealizationTrace.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/detail/Builders.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
using Record = protocol::detail::AlgorithmExpansionRecord;
using Occurrence = protocol::detail::AlgorithmOccurrence;
using StateAccess = protocol::detail::AlgorithmStateAccess;
using Reductions = std::map<std::string, SelectedReduction>;

LogicalResult fuseVectorReductionsImpl(ModuleOp,
                                       protocol::AlgorithmExpansionState &,
                                       ArrayRef<ReductionRecipe>,
                                       RealizationTrace *,
                                       llvm::function_ref<bool(Operation *)>);

protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  if (!hasSingleElement(*module.getBody()))
    return {};
  auto root =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  return root && root.getProfile() != protocol_ir::Profile::Physical
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
  if (auto policy = map->getAttrOfType<ArrayAttr>("policy");
      policy && !cast<BoolAttr>(policy[1]).getValue()) {
    if (outcome)
      *outcome = {OptimizationStatus::PolicyDisabled,
                  OptimizationReason::Policy};
    return {};
  }
  auto reference = sum->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto binding = reference
                     ? symbols.lookup<runtime::BindingOp>(reference.getValue())
                     : runtime::BindingOp();
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
  LogicalResult run(const Reductions &reductions,
                    const std::map<std::string, OptimizationOutcome> &decisions,
                    llvm::function_ref<bool(Operation *)> select) {
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
      if (select && !select(call))
        continue;
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
          runtime::BindingOp::create(
              builder, map.getLoc(), name, contract,
              arguments(root.getContext(), contract, field.getDomain()), "",
              mlir::ArrayAttr{});
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
      auto realized = emitMapPayload(
          map, symbols.lookup<func::FuncOp>(map.getHelper()).getBody().front(),
          call.getInputs(), MapPayloadForm::Dot,
          [&](const protocol::BindingApplication &application,
              ValueRange inputs, TypeRange outputs, ArrayRef<std::string>) {
            return emit(application.contract, inputs,
                        outputs.empty() ? Type() : outputs.front(),
                        application.contract != "vector.dot");
          },
          &reductions.at(map.getSymName().str()));
      if (!realized)
        return diagnostics::emit(call.emitOpError(), realized.takeError());
      if (realized->status != LaneRealizationStatus::Realized)
        return failure();
      sum->getResult(0).replaceAllUsesWith(realized->value);
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
      auto binding = candidateSymbols.lookup<runtime::BindingOp>(name);
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
    SmallVector<Value> inputs;
    for (Value operand : call->getOperands()) {
      auto mapped = values.lookup(operand);
      if (!mapped)
        return refuse(call, "unbound map input");
      inputs.push_back(mapped);
    }
    unsigned guards = 0;
    for (bool row : map.getRowwise())
      if (row)
        guards += guards ? 3 : 1;
    Operation *begin = cursor == target.end() ? nullptr : &*cursor;
    Operation *end = begin;
    for (unsigned i = 0; i != guards + 1; ++i) {
      if (!end)
        return refuse(call, "missing guarded reduction");
      end = end->getNextNode();
    }
    auto *payload = begin;
    for (unsigned i = 0; i != guards; ++i)
      payload = payload->getNextNode();
    if (payload->getNumResults() != 1)
      return refuse(call, "reduction result");
    auto *read = begin;
    VerificationDecision outcome;
    auto result = readMapPayload(
        map, inputs, true, read, end, payload->getResult(0), candidateSymbols,
        addedBindings, expected.checkWork, expected.checkWork, outcome);
    if (failed(result) || read != end)
      return refuse(call, "reduction formula correspondence");
    // The semantic worker checked all operands and nominal contracts. The
    // standalone edge additionally preserves its exact naming/record contract.
    for (unsigned i = 0; i != guards + 1; ++i) {
      auto *actual = &*cursor;
      auto ref = actual->getAttrOfType<FlatSymbolRefAttr>("binding");
      auto binding =
          ref ? candidateSymbols.lookup<runtime::BindingOp>(ref.getValue())
              : runtime::BindingOp();
      if (!binding || (i == guards && binding.getContract() != "vector.dot") ||
          !primitive(binding.getContract(), actual->getOperands(),
                     actual->getNumResults() ? actual->getResult(0).getType()
                                             : Type(),
                     i != guards))
        return refuse(call, "guarded reduction naming or binding");
    }
    if (failed(bind(sum->getResults(), ValueRange{*result}, values)))
      return refuse(call, "reduction result substitution");
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
                    protocol_ir::ProtocolModuleOp candidate, Record &output,
                    bool compareRecords = true) {
    auto debit = llvm::scope_exit([&] {
      output.checkWork = expected.checkWork;
      output.checkOriginBytes = expected.checkOriginBytes;
    });
    llvm::DenseSet<Operation *> retained;
    SmallVector<Operation *> retainedOrder;
    auto anonymous = candidate.getBody().front().begin();
    for (Operation &op : original.getBody().front()) {
      if (!charge())
        return refuse(&op, "declaration work limit");
      auto name = SymbolTable::getSymbolName(&op);
      Operation *actual = nullptr;
      if (name) {
        actual = candidateSymbols.lookup(name.getValue());
      } else {
        while (anonymous != candidate.getBody().front().end() &&
               SymbolTable::getSymbolName(&*anonymous))
          ++anonymous;
        if (anonymous != candidate.getBody().front().end())
          actual = &*anonymous++;
      }
      if (!actual)
        return refuse(&op, "missing declaration");
      retained.insert(actual);
      retainedOrder.push_back(actual);
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
    auto originalOrder = retainedOrder.begin();
    for (Operation &op : candidate.getBody().front()) {
      if (retained.contains(&op)) {
        if (originalOrder == retainedOrder.end() || *originalOrder++ != &op)
          return refuse(&op, "retained declaration order");
      } else if (!addedBindings.contains(&op))
        return refuse(&op, "unexpected declaration");
    }
    if (compareRecords && !expected.sameExpansion(output))
      return refuse(candidate, "occurrence records or cumulative limits");
    if (!compareRecords)
      output = expected;
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

// Finish has already expanded ordinary calls. Reconstruct only the coordinates
// of this immutable late subject, retaining the caller's cumulative allowances.
// These coordinates identify occurrences; the correspondence reader still
// interprets every actual guard, payload and surrounding declaration.
LogicalResult retainedRecord(ModuleOp source, Record &record) {
  auto root = unit(source);
  if (!root)
    return refuse(source, "expected a logical map subject");
  llvm::DenseSet<Operation *> helpers;
  uint64_t expandedOperations;
  if (failed(algebra::collectMapHelpers(root, helpers, expandedOperations)))
    return failure();
  // Formula extraction has its own per-body limits. Debit its complete
  // expanded helper work here as well so repeated late attempts cannot renew
  // that allowance merely by rebuilding their occurrence coordinates.
  if (expandedOperations > record.inspectionWork)
    return diagnostics::emit(source.emitError(), "algorithm-expansion-limit");
  record.inspectionWork -= expandedOperations;
  record.occurrences.clear();
  record.retained = true;
  record.finished = false;
  SymbolTable symbols(root);
  for (auto function : root.getBody().front().getOps<local::FuncOp>()) {
    auto result = function.walk([&](Operation *op) -> WalkResult {
      if (!record.inspectionWork) {
        (void)diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit");
        return WalkResult::interrupt();
      }
      --record.inspectionWork;
      if (auto call = dyn_cast<local::ApplyOp>(op))
        if (!symbols.lookup<algebra::MapRealizeOp>(call.getCallee())) {
          (void)refuse(call,
                       "ordinary algorithms must finish before late fusion");
          return WalkResult::interrupt();
        }
      auto site = op->getAttrOfType<StringAttr>("site");
      if (!site)
        return WalkResult::advance();
      unsigned depth = 0;
      for (auto *parent = op->getParentOp(); parent != function;
           parent = parent->getParentOp())
        if (!parent || ++depth > 64) {
          (void)diagnostics::emit(op->emitOpError(), "interactive-call-depth");
          return WalkResult::interrupt();
        }
      auto origin = function->getAttrOfType<ArrayAttr>("logical_origin");
      auto definition = origin ? cast<StringAttr>(origin[0]).getValue()
                               : function.getSymName();
      if (!record.occurrences
               .emplace(
                   protocol::detail::OccurrenceKey{function.getSymName().str(),
                                                   site.getValue().str()},
                   Occurrence{definition.str(),
                              function.getSymName().str(),
                              site.getValue().str(),
                              {},
                              depth})
               .second) {
        (void)refuse(op, "duplicate late occurrence");
        return WalkResult::interrupt();
      }
      return WalkResult::advance();
    });
    if (result.wasInterrupted())
      return failure();
  }
  return success();
}

FailureOr<std::map<std::string, std::pair<unsigned, unsigned>>>
describeRetainedProducts(ModuleOp source, Record &record,
                         RealizationTrace *trace) {
  auto root = unit(source);
  if (root.getProfile() == protocol_ir::Profile::Protocol)
    return describeMapProducts(source, trace);
  llvm::DenseSet<Operation *> helpers;
  if (failed(algebra::collectMapHelpers(root, helpers)))
    return failure();
  // Reuse the existing common-profile formula reader on an analysis-only
  // symbol table. The complete logical source was verified before reaching
  // here; this view copies exact declarations, grants no new admission and is
  // never published as a Protocol program.
  for (Operation &op : root.getBody().front()) {
    if (!helpers.contains(&op) && !isa<algebra::MapRealizeOp>(op))
      continue;
    auto charged = op.walk([&](Operation *nested) -> WalkResult {
      uint64_t cost = 1 + nested->getNumOperands() + nested->getNumResults();
      if (cost > record.inspectionWork) {
        (void)diagnostics::emit(nested->emitOpError(),
                                "algorithm-expansion-limit");
        return WalkResult::interrupt();
      }
      record.inspectionWork -= cost;
      return WalkResult::advance();
    });
    if (charged.wasInterrupted())
      return failure();
  }
  OwningOpRef<ModuleOp> view(ModuleOp::create(source.getLoc()));
  OpBuilder builder(source.getContext());
  builder.setInsertionPointToEnd(view->getBody());
  auto scope = protocol_ir::ProtocolModuleOp::create(
      builder, source.getLoc(),
      protocol_ir::ProfileAttr::get(source.getContext(),
                                    protocol_ir::Profile::Protocol));
  scope.getBody().push_back(new Block());
  builder.setInsertionPointToEnd(&scope.getBody().front());
  for (Operation &op : root.getBody().front())
    if (helpers.contains(&op) || isa<algebra::MapRealizeOp>(op))
      builder.clone(op);
  return describeMapProducts(*view, trace);
}
} // namespace

algebra::MapRealizeOp
eligibleMapSum(local::ApplyOp call, SymbolTable &symbols,
               MathematicalSelectionPolicy policy,
               ArrayRef<std::pair<std::string, std::string>> selections) {
  if (!policy.vectorReductionFusion)
    return {};
  auto map = reductionMap(call, symbols);
  if (!map)
    return {};
  auto reference =
      call->getNextNode()->getAttrOfType<FlatSymbolRefAttr>("binding");
  for (const auto &[name, implementation] : selections)
    if (reference && reference.getValue() == name)
      return {};
  return map;
}

LogicalResult
verifyRetainedMapReductionsPreserved(ModuleOp original, ModuleOp candidate,
                                     MathematicalSelectionPolicy policy) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  auto before = unit(original), after = unit(candidate);
  if (!before || !after ||
      original->getAttrDictionary() != candidate->getAttrDictionary() ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse(candidate, "late module shape or profile");
  if (!policy.vectorReductionFusion)
    return OperationEquivalence::isEquivalentTo(
               original, candidate, OperationEquivalence::IgnoreLocations)
               ? success()
               : refuse(candidate, "fusion is disabled by the caller policy");
  Record input, output;
  if (failed(retainedRecord(original, input)))
    return failure();
  return Correspondence(before, after, input).run(before, after, output, false);
}

// Call on an immutable Participant/Exec subject before expandMapRealizations.
// The returned candidate is owned; no source pointer or producer match escapes.
// Share state across selection attempts to retain the expansion/site
// allowances.
OwningOpRef<ModuleOp>
fuseRetainedMapReductions(ModuleOp source, MathematicalSelectionPolicy policy,
                          protocol::AlgorithmExpansionState &state,
                          RealizationTrace *trace,
                          llvm::function_ref<bool(Operation *)> select) {
  if (failed(verify(source)) || !unit(source))
    return {};
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  if (!policy.vectorReductionFusion)
    return candidate;
  Record input = StateAccess::get(state);
  if (failed(retainedRecord(source, input))) {
    StateAccess::set(state, std::move(input));
    return {};
  }
  protocol::AlgorithmExpansionState proposalState;
  StateAccess::set(proposalState, input);
  if (failed(fuseVectorReductionsImpl(*candidate, proposalState,
                                      mathematicalRecipes().reductions, trace,
                                      select))) {
    StateAccess::set(state, StateAccess::get(proposalState));
    return {};
  }
  StateAccess::set(state, StateAccess::get(proposalState));
  // The transactional producer already ran Correspondence with the shared
  // checking balances. Do not repeat that check with replenished allowances.
  return candidate;
}

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
  return fuseVectorReductionsImpl(module, state, reductionRecipes, trace, {});
}
namespace {
LogicalResult fuseVectorReductionsImpl(
    ModuleOp module, protocol::AlgorithmExpansionState &state,
    ArrayRef<ReductionRecipe> reductionRecipes, RealizationTrace *trace,
    llvm::function_ref<bool(Operation *)> select) {
  RealizationScope scope(trace, "vector-reductions", module, {true, true});
  Record input = StateAccess::get(state);
  if (!input.retained || input.finished || !unit(module))
    return refuse(module, "expected retained preparation");
  if (failed(verify(module)))
    return failure();
  Record discovery = input;
  auto retainDiscovery = llvm::scope_exit([&] {
    Record balances = StateAccess::get(state);
    balances.inspectionWork = discovery.inspectionWork;
    StateAccess::set(state, std::move(balances));
  });
  // Read every original formula, not just live or eligible applications.
  auto products = describeRetainedProducts(module, discovery, trace);
  if (failed(products))
    return failure();
  // The correspondence reader charges semantic comparison independently;
  // analysis-view copying belongs to the producer's inspection balance.
  input.inspectionWork = discovery.inspectionWork;
  retainDiscovery.release();
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
  bool published = false;
  auto debit = llvm::scope_exit([&] {
    if (published)
      return;
    Record balances = input;
    balances.work = output.work;
    balances.originBytes = output.originBytes;
    balances.inspectionWork = output.inspectionWork;
    balances.checkWork = output.checkWork;
    balances.checkOriginBytes = output.checkOriginBytes;
    StateAccess::set(state, std::move(balances));
  });
  bool changed = false;
  if (failed(Rewriter(unit(*candidate), output, scope, changed)
                 .run(reductions, decisions, select)))
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
  published = true;
  if (changed)
    scope.publish();
  else
    scope.complete(CompletionKind::Unchanged);
  return success();
}
} // namespace
} // namespace zkc::mathematical
