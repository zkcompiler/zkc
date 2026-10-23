#include "PhysicalPlan.h"
#include "../Transforms/Kernel/Support.h"
#include "../Transforms/NumericalLowering.h"
#include "../Transforms/NumericalSelection.h"
#include "ImplementationPlan.h"
#include "mlir/IR/RegionKindInterface.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include <map>
#include <set>

using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
namespace zkc::target {
SmallVector<Operation *> physicalPlanOperations(ModuleOp module) {
  SmallVector<Operation *> result;
  module->walk<WalkOrder::PreOrder>(
      [&](Operation *op) { result.push_back(op); });
  return result;
}
Error CheckedPhysicalPlan::checkInput(ModuleOp module) const {
  return plan.implementation->checkInput(module);
}
Expected<ModuleOp> PhysicalPlan::selectedSubject(ModuleOp source) const {
  if (!implementation)
    return error("binding-stale-selection");
  if (auto e = implementation->checkInput(source))
    return e;
  return implementation->subject();
}
Expected<OwningOpRef<ModuleOp>>
PhysicalPlan::cloneSelectedSubject(ModuleOp source) const {
  auto selected = selectedSubject(source);
  if (!selected)
    return selected.takeError();
  return OwningOpRef<ModuleOp>(cast<ModuleOp>((*selected)->clone()));
}
namespace {
void locate(Location *failureLocation, Operation *op) {
  if (failureLocation)
    *failureLocation = op->getLoc();
}
Expected<Type> defaultPort(Type type) {
  auto logical = encodeBoundType(type, false);
  if (!logical)
    return logical.takeError();
  auto physical = defaultRepresentation(*logical);
  if (!physical)
    return physical.takeError();
  auto decoded = decodeBoundType(type.getContext(), *physical);
  if (!decoded)
    return createStringError(
        "physical conversion requires loaded zkc dialects");
  return decoded;
}
Expected<SmallVector<Type>> defaultPorts(TypeRange types) {
  SmallVector<Type> result;
  for (auto type : types) {
    auto port = defaultPort(type);
    if (!port)
      return port.takeError();
    result.push_back(*port);
  }
  return result;
}
Expected<SmallVector<Type>> decodePorts(MLIRContext *context,
                                        ArrayRef<BoundType> types) {
  SmallVector<Type> result;
  for (const auto &type : types) {
    auto decoded = decodeBoundType(context, type);
    if (!decoded)
      return createStringError(
          "physical conversion requires loaded zkc dialects");
    result.push_back(decoded);
  }
  return result;
}
bool sameApplication(const BindingApplication &a, const BindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments &&
         a.implementation == b.implementation;
}
bool sameLogical(const BindingApplication &a, const BindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments;
}
bool interfaceOperation(Operation *op) {
  return isa<zkc::local::BoolConstantOp, zkc::local::ReturnOp,
             zkc::local::StopOp, zkc::local::VariantInjectOp,
             zkc::local::LocalMatchOp, zkc::local::LocalIfOp,
             zkc::local::LocalForOp, zkc::local::LocalYieldOp,
             zkc::local::LocalConditionOp>(op);
}
using Indices = llvm::DenseMap<Operation *, OperationIndex>;
Indices indexOperations(ArrayRef<Operation *> operations) {
  Indices indices;
  for (auto [index, op] : enumerate(operations))
    indices[op] = index;
  return indices;
}
// Resolve one actual SSA definition through its own recorded ports. This is
// deliberately not a Type -> Type conversion map.
Type valuePort(Value value, const PhysicalPlan &plan, const Indices &indices) {
  if (auto result = dyn_cast<OpResult>(value))
    return plan.operations[indices.lookup(result.getOwner())]
        .outputs[result.getResultNumber()];
  auto arg = cast<BlockArgument>(value);
  auto *owner = arg.getOwner()->getParentOp();
  size_t blockIndex = 0;
  for (auto &region : owner->getRegions())
    for (auto &block : region) {
      if (&block == arg.getOwner())
        return plan.operations[indices.lookup(owner)]
            .blockArguments[blockIndex][arg.getArgNumber()];
      ++blockIndex;
    }
  llvm_unreachable("block argument belongs to its parent");
}
std::string fresh(std::set<std::string> &used, StringRef prefix,
                  unsigned &next) {
  std::string result;
  do {
    result = prefix.str() + std::to_string(next++);
  } while (!used.insert(result).second);
  return result;
}
// Match only an explicitly classified refusal. Unknown errors retain their
// original type and payload; diagnostic prose is never a retry protocol.
Error decline(Error e, ArrayRef<StringRef> allowed, bool &declined) {
  declined = false;
  return handleErrors(std::move(e), [&](const Refusal &refusal) -> Error {
    if (!is_contained(allowed, StringRef(refusal.code)))
      return error(refusal.code, refusal.detail);
    declined = true;
    return Error::success();
  });
}
struct ImplementationCursor {
  BindingApplication logical;
  SmallVector<mathematical::NumericalOccurrence> owners;
  // Empty for generated bindings: their identity is the owned occurrence set
  // and logical application, not a generated symbol spelling.
  std::string authored;
  std::vector<std::string> candidates;
  size_t next = 0;
  std::optional<size_t> parent;
};
class PhysicalSelection {
public:
  mathematical::NumericalSelection numerical;
  SmallVector<ImplementationCursor> implementations;
  using ImplementationKey =
      std::tuple<std::string, std::vector<std::string>,
                 std::vector<mathematical::NumericalOccurrence>, std::string>;
  std::map<ImplementationKey, size_t> implementationCoordinates;
  SmallVector<std::optional<size_t>> bindingCursors;
  PhysicalFailure failure;

  size_t representative(size_t id) {
    auto root = id;
    while (implementations[root].parent)
      root = *implementations[root].parent;
    while (id != root) {
      auto next = *implementations[id].parent;
      implementations[id].parent = root;
      id = next;
    }
    return root;
  }

  Expected<ImplementationChoice>
  choose(const BindingApplication &application,
         std::optional<StringRef> request, const CandidateCatalog &catalog,
         ArrayRef<mathematical::NumericalOccurrence> owners, StringRef authored,
         std::optional<size_t> &cursor) {
    if (request || !application.implementation.empty())
      return selectImplementation(application, request);
    auto logical = resolveBinding(application, false);
    if (!logical)
      return logical.takeError();
    if (!numerical.chargeCatalog())
      return error("finite-analysis-limit");
    // A generated declaration may stop being shared when one occurrence
    // changes recipe. Keep each source owner's alias to the same monotone
    // cursor, rather than keying a new cursor by the smaller current use set.
    SmallVector<ImplementationKey> keys;
    if (authored.empty() && !owners.empty()) {
      for (auto owner : owners)
        keys.emplace_back(application.contract, application.arguments,
                          std::vector{owner}, std::string{});
    } else
      keys.emplace_back(application.contract, application.arguments,
                        std::vector<mathematical::NumericalOccurrence>{},
                        authored.str());
    size_t id = implementations.size();
    SmallVector<size_t> merge;
    for (const auto &key : keys) {
      if (!numerical.chargeCatalog())
        return error("finite-analysis-limit");
      auto found = implementationCoordinates.find(key);
      if (found == implementationCoordinates.end())
        continue;
      auto previous = representative(found->second);
      if (id == implementations.size())
        id = previous;
      else if (previous != id && !is_contained(merge, previous))
        merge.push_back(previous);
    }
    if (id == implementations.size()) {
      auto candidates = catalog.implementations(application);
      if (!candidates)
        return candidates.takeError();
      if (!numerical.chargeCatalog(candidates->size()))
        return error("finite-analysis-limit");
      implementations.push_back({application,
                                 {owners.begin(), owners.end()},
                                 authored.str(),
                                 std::move(*candidates),
                                 0,
                                 {}});
    }
    for (auto previous : merge) {
      auto &source = implementations[previous];
      auto &target = implementations[id];
      if (source.candidates != target.candidates)
        return error("binding-operation");
      target.next = std::max(target.next, source.next);
      source.parent = id;
    }
    for (auto &key : keys)
      implementationCoordinates.insert_or_assign(std::move(key), id);
    cursor = id;
    auto &entry = implementations[id];
    for (; entry.next < entry.candidates.size(); ++entry.next) {
      if (!numerical.chargeCatalog())
        return error("finite-analysis-limit");
      auto selected = application;
      selected.implementation = entry.candidates[entry.next];
      auto installed = resolveBinding(selected, true);
      if (installed)
        return ImplementationChoice{std::move(selected), false};
      bool unavailable;
      if (auto e = decline(installed.takeError(), {"binding-implementation"},
                           unavailable))
        return e;
    }
    failure.kind = PhysicalFailureKind::ImplementationUnavailable;
    return error("binding-implementation");
  }
  Expected<bool> advance() {
    // An exhausted implementation at one endpoint can still leave a usable
    // automatic choice at the other. Never reset either endpoint's cursor.
    auto bindings = failure.bindings;
    llvm::sort(bindings);
    for (auto binding : bindings) {
      if (binding >= bindingCursors.size() || !bindingCursors[binding])
        continue;
      auto &entry = implementations[representative(*bindingCursors[binding])];
      if (entry.next + 1 < entry.candidates.size()) {
        if (!numerical.chargeCatalog())
          return error("finite-analysis-limit");
        ++entry.next;
        return true;
      }
    }
    return false;
  }
};
Expected<BindingApplication>
chooseConversion(Type from, Type to, const CandidateCatalog &catalog,
                 mathematical::NumericalSelection &selection) {
  auto source = encodeBoundType(from, true);
  if (!source)
    return source.takeError();
  auto target = encodeBoundType(to, true);
  if (!target)
    return target.takeError();
  if (!selection.chargeCatalog())
    return error("finite-analysis-limit");
  auto candidates = catalog.conversions(*source, *target);
  if (!selection.chargeCatalog(candidates.size()))
    return error("finite-analysis-limit");
  for (auto candidate : candidates) {
    // A catalog suggestion can name an uninstalled adapter. Decline that
    // suggestion; authored bindings and explicit pins were admitted separately.
    if (auto e = checkDirectConversion(candidate, *source, *target)) {
      bool unavailable;
      if (auto terminal =
              decline(std::move(e),
                      {"binding-no-conversion", "binding-implementation",
                       "binding-conversion"},
                      unavailable))
        return terminal;
      continue;
    }
    return candidate;
  }
  return error("binding-no-conversion");
}

class Proposer {
  ModuleOp module;
  zkc::protocol_ir::ProtocolModuleOp root;
  const CandidateCatalog &catalog;
  SmallVector<Operation *> operations;
  Indices indices;
  Location *failureLocation;
  PhysicalSelection &selection;
  SmallVector<BindingDecision> originals;
  std::map<std::string, BindingIndex> names;
  std::map<std::string, SmallVector<OperationIndex>> bindingUses;
  SmallVector<LinearContractionGroup> eligible;
  std::set<std::string> symbols;

  Error ports(PhysicalPlan &plan) {
    // Record every definition first; nested interface uses can refer to their
    // parent's outputs. Every operation has exactly one preorder entry.
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      for (auto &region : op->getRegions())
        for (auto &block : region) {
          auto ports = defaultPorts(block.getArgumentTypes());
          if (!ports)
            return ports.takeError();
          decision.blockArguments.push_back(std::move(*ports));
        }
      if (auto signature = op->getAttrOfType<TypeAttr>("function_type")) {
        auto functionType = cast<FunctionType>(signature.getValue());
        auto inputs = defaultPorts(functionType.getInputs());
        if (!inputs)
          return inputs.takeError();
        auto outputs = defaultPorts(functionType.getResults());
        if (!outputs)
          return outputs.takeError();
        decision.functionType =
            FunctionType::get(module.getContext(), *inputs, *outputs);
      }
      if (decision.binding) {
        auto signature = resolveBinding(
            plan.bindings[*decision.binding].binding.application, true);
        if (!signature)
          return signature.takeError();
        auto inputs = decodePorts(module.getContext(), signature->inputs);
        if (!inputs)
          return inputs.takeError();
        auto outputs = decodePorts(module.getContext(), signature->outputs);
        if (!outputs)
          return outputs.takeError();
        decision.inputs = std::move(*inputs);
        decision.outputs = std::move(*outputs);
      } else {
        auto outputs = defaultPorts(op->getResultTypes());
        if (!outputs)
          return outputs.takeError();
        decision.outputs = std::move(*outputs);
      }
    }
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      if (decision.binding)
        continue;
      if (isa<zkc::local::ReturnOp>(op)) {
        auto function = op->getParentOfType<zkc::local::FuncOp>();
        append_range(decision.inputs, plan.operations[indices.lookup(function)]
                                          .functionType.getResults());
      } else if (isa<zkc::local::LocalIfOp>(op)) {
        auto condition = defaultPort(IntegerType::get(module.getContext(), 1));
        if (!condition)
          return condition.takeError();
        decision.inputs.push_back(*condition);
        append_range(decision.inputs, decision.blockArguments[0]);
      } else if (isa<zkc::local::LocalForOp>(op)) {
        decision.inputs.push_back(decision.blockArguments[0][0]);
        append_range(decision.inputs, decision.blockArguments[0]);
      } else if (isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                     op)) {
        auto *parent = op->getParentOp();
        if (isa<zkc::local::LocalConditionOp>(op)) {
          auto condition =
              defaultPort(IntegerType::get(module.getContext(), 1));
          if (!condition)
            return condition.takeError();
          decision.inputs.push_back(*condition);
        }
        append_range(decision.inputs,
                     plan.operations[indices.lookup(parent)].outputs);
        if (isa<zkc::local::LocalForOp>(parent))
          append_range(
              decision.inputs,
              ArrayRef(
                  plan.operations[indices.lookup(parent)].blockArguments[0])
                  .drop_front(1 + parent->getNumResults()));
      } else {
        auto inputs = defaultPorts(op->getOperandTypes());
        if (!inputs)
          return inputs.takeError();
        decision.inputs = std::move(*inputs);
      }
      if (decision.inputs.size() != op->getNumOperands())
        return error("binding-operation-signature");
    }
    return Error::success();
  }

public:
  Proposer(ModuleOp module, const CandidateCatalog &catalog,
           Location *failureLocation, PhysicalSelection &selection)
      : module(module), root(cast<zkc::protocol_ir::ProtocolModuleOp>(
                            &module.getBody()->front())),
        catalog(catalog), operations(physicalPlanOperations(module)),
        indices(indexOperations(operations)), failureLocation(failureLocation),
        selection(selection) {}

  Error initialize(ArrayRef<std::pair<std::string, std::string>> requests,
                   bool contractions) {
    for (auto [index, op] : enumerate(operations)) {
      if (!selection.numerical.chargeCatalog())
        return error("finite-analysis-limit");
      if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding"))
        bindingUses[ref.getValue().str()].push_back(index);
    }
    std::map<std::string, std::string> choices;
    for (const auto &[key, implementation] : requests)
      if (!choices.emplace(key, implementation).second)
        return error("binding-duplicate-selection");
    for (auto &op : root.getBody().front()) {
      locate(failureLocation, &op);
      if (auto name = op.getAttrOfType<StringAttr>("sym_name"))
        symbols.insert(name.getValue().str());
      if (!isa<zkc::local::OperationBindingOp>(op))
        continue;
      auto binding = readBinding(&op);
      if (!binding)
        return binding.takeError();
      auto request = choices.find(binding->name);
      SmallVector<mathematical::NumericalOccurrence> owners;
      bool authoredUse = false;
      for (auto index : bindingUses[binding->name]) {
        if (!selection.numerical.chargeCatalog())
          return error("finite-analysis-limit");
        auto occurrenceOwners = selection.numerical.owners(operations[index]);
        authoredUse |= occurrenceOwners.empty();
        append_range(owners, occurrenceOwners);
        selection.failure.operations.push_back(index);
      }
      llvm::sort(owners);
      owners.erase(std::unique(owners.begin(), owners.end()), owners.end());
      // A shared declaration with any authored use cannot be erased by
      // numerical fallback, even if another use came from a recipe.
      std::optional<size_t> cursor;
      auto selected = selection.choose(
          binding->application,
          request == choices.end() ? std::nullopt
                                   : std::optional<StringRef>(request->second),
          catalog, owners, owners.empty() || authoredUse ? binding->name : "",
          cursor);
      selection.bindingCursors.push_back(cursor);
      if (!selected) {
        selection.failure.bindings.push_back(originals.size());
        if (authoredUse || owners.empty() || request != choices.end() ||
            !binding->application.implementation.empty())
          selection.failure.kind = PhysicalFailureKind::Terminal;
        return selected.takeError();
      }
      selection.failure = {};
      binding->application = std::move(selected->application);
      names.emplace(binding->name, originals.size());
      originals.push_back({std::move(*binding), BindingPurpose::Original,
                           indices.lookup(&op), selected->fixed,
                           indices.lookup(&op)});
      if (request != choices.end())
        choices.erase(request);
    }
    locate(failureLocation, root);
    if (!choices.empty())
      return error("binding-unknown-selection");
    if (contractions) {
      LinearContractionStats ignored;
      for (auto function : root.getBody().front().getOps<zkc::local::FuncOp>())
        append_range(eligible, findLinearContractions(function, ignored));
    }
    return Error::success();
  }

  Error populate(PhysicalPlan &plan, size_t groupLimit) {
    plan.bindings = originals;
    plan.operations.clear();
    plan.contractions.clear();
    auto used = symbols;
    unsigned next = 0;
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      OperationDecision decision;
      decision.operation = index;
      if (auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding")) {
        auto found = names.find(ref.getValue().str());
        if (found == names.end())
          return error("binding-reference");
        decision.binding = found->second;
      } else if (op->getParentOfType<zkc::local::FuncOp>() &&
                 !interfaceOperation(op))
        return error("binding-reference");
      plan.operations.push_back(std::move(decision));
    }
    for (const auto &group : eligible) {
      if (plan.contractions.size() >= groupLimit)
        break;
      SmallVector<std::pair<OperationIndex, BindingDecision>> pending;
      Error contractionError = Error::success();
      auto prepare = [&](Operation *op) {
        auto index = indices.lookup(op);
        auto binding = plan.operations[index].binding;
        if (!binding || plan.bindings[*binding].fixed)
          return false;
        auto clone = plan.bindings[*binding];
        bool available = false;
        for (const auto &implementation :
             catalog.diagonalImplementations(clone.binding.application)) {
          if (!selection.numerical.chargeCatalog()) {
            contractionError = error("finite-analysis-limit");
            return false;
          }
          auto candidate = clone.binding.application;
          candidate.implementation = implementation;
          auto installed = resolveDiagonalImplementation(candidate);
          if (!installed) {
            bool unavailable;
            auto terminal = decline(
                installed.takeError(),
                {"binding-implementation", "binding-contraction"}, unavailable);
            if (terminal) {
              contractionError = std::move(terminal);
              return false;
            }
            continue;
          }
          clone.binding.application = std::move(candidate);
          available = true;
          break;
        }
        if (!available)
          return false;
        clone.purpose = BindingPurpose::Contraction;
        clone.declaration.reset();
        clone.location = index;
        pending.emplace_back(index, std::move(clone));
        return true;
      };
      if (plan.bindings.size() + 1 + group.uses.size() > 4096 ||
          !prepare(group.producer)) {
        if (contractionError)
          return contractionError;
        continue;
      }
      bool available = true;
      for (const auto &use : group.uses)
        if (!prepare(use.consumer)) {
          available = false;
          break;
        }
      if (contractionError)
        return contractionError;
      if (!available)
        continue;
      ContractionDecision selected{indices.lookup(group.producer), {}};
      for (const auto &use : group.uses)
        selected.consumers.push_back(indices.lookup(use.consumer));
      for (auto &[index, binding] : pending) {
        binding.binding.name = fresh(used, "diagonal_", next);
        plan.operations[index].binding = plan.bindings.size();
        plan.bindings.push_back(std::move(binding));
      }
      plan.contractions.push_back(std::move(selected));
    }
    if (auto e = ports(plan))
      return e;
    std::map<Operation *, std::set<std::string>> sites;
    for (auto *op : operations)
      if (auto function = op->getParentOfType<zkc::local::FuncOp>())
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          sites[function].insert(site.getValue().str());
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      for (auto [operand, value] : enumerate(op->getOperands())) {
        Type from = valuePort(value, plan, indices);
        Type to = decision.inputs[operand];
        if (from == to)
          continue;
        auto application =
            chooseConversion(from, to, catalog, selection.numerical);
        if (!application) {
          bool unavailable;
          if (auto e = decline(application.takeError(),
                               {"binding-no-conversion"}, unavailable))
            return e;
          auto &failure = selection.failure;
          failure.kind = PhysicalFailureKind::ConversionUnavailable;
          failure.operations.push_back(index);
          failure.operand = unsigned(operand);
          failure.from = from;
          failure.to = to;
          if (decision.binding)
            failure.bindings.push_back(*decision.binding);
          Operation *producer = value.getDefiningOp();
          if (!producer)
            producer = cast<BlockArgument>(value).getOwner()->getParentOp();
          auto producerIndex = indices.lookup(producer);
          failure.operations.push_back(producerIndex);
          if (plan.operations[producerIndex].binding)
            failure.bindings.push_back(*plan.operations[producerIndex].binding);
          return error("binding-no-conversion");
        }
        BindingIndex binding = plan.bindings.size();
        // Reuse declarations, never conversion instructions or their results.
        for (auto [i, candidate] : enumerate(plan.bindings))
          if (candidate.purpose == BindingPurpose::Conversion &&
              sameApplication(candidate.binding.application, *application))
            binding = i;
        if (binding == plan.bindings.size()) {
          protocol::OperationBinding declaration{fresh(used, "layout_", next),
                                                 std::move(*application)};
          plan.bindings.push_back({std::move(declaration),
                                   BindingPurpose::Conversion,
                                   {},
                                   false,
                                   index});
        }
        auto function = op->getParentOfType<zkc::local::FuncOp>();
        if (!function)
          return error("binding-no-conversion");
        decision.conversions.push_back(
            {unsigned(operand), binding, from, to,
             fresh(sites[function], "layout_", next)});
      }
    }
    return Error::success();
  }
};
} // namespace

Expected<PhysicalPlan>
proposePhysical(ModuleOp module, const CandidateCatalog &catalog,
                ArrayRef<std::pair<std::string, std::string>> selections,
                PhysicalPlanOptions options, Location *failureLocation) {
  locate(failureLocation, module);
  if (failed(verify(module)) || module.getBody()->empty() ||
      !isa<zkc::protocol_ir::ProtocolModuleOp>(module.getBody()->front()))
    return error("binding-operation");
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(&module.getBody()->front());
  if (root.getProfile() != zkc::protocol_ir::Profile::Exec)
    return error("interactive-physical-stage");
  // Validate every explicit request before replacement discovery. Pins bypass
  // catalog preferences and survive even when the chosen operation is unused.
  std::map<std::string, std::string> requests;
  for (const auto &[name, implementation] : selections)
    if (!requests.emplace(name, implementation).second)
      return error("binding-duplicate-selection");
  std::map<std::string, std::string> originalPins;
  for (auto declaration :
       root.getBody().front().getOps<zkc::local::OperationBindingOp>()) {
    locate(failureLocation, declaration);
    auto binding = readBinding(declaration);
    if (!binding)
      return binding.takeError();
    originalPins.emplace(binding->name, binding->application.implementation);
    auto found = requests.find(binding->name);
    if (found == requests.end())
      continue;
    auto fixed = selectImplementation(binding->application, found->second);
    if (!fixed)
      return fixed.takeError();
    requests.erase(found);
  }
  if (!requests.empty())
    return error("binding-unknown-selection");
  auto implementation = std::make_shared<ImplementationPlan>(
      module, selections, options.numericalPolicy);
  bool hasKernels = false, hasMaps = false;
  root.walk([&](Operation *op) {
    hasKernels |= isa<kernel::ModuleOp, kernel::CallOp>(op);
    hasMaps |= isa<zkc::algebra::MapRealizeOp>(op);
  });
  bool hasNumerical = hasKernels || hasMaps;
  PhysicalSelection selection;
  if (options.numericalWork)
    selection.numerical.work = *options.numericalWork;
  if (options.numericalCopy)
    selection.numerical.remainingCopy = *options.numericalCopy;
  if (options.numericalSiteBytes)
    selection.numerical.remainingSiteBytes = *options.numericalSiteBytes;
  auto settleWork = llvm::scope_exit([&] {
    if (options.numericalCopy)
      *options.numericalCopy = selection.numerical.remainingCopy;
    if (options.numericalSiteBytes)
      *options.numericalSiteBytes = selection.numerical.remainingSiteBytes;
    if (options.numericalWork) {
      *options.numericalWork = selection.numerical.work;
      options.numericalWork->numericalSelection = nullptr;
      options.numericalWork->numericalOccurrence.reset();
    }
  });
  OwningOpRef<ModuleOp> prepared;
  mathematical::PreparedMaps maps;
  if (hasNumerical) {
    if (hasKernels)
      prepared = kernel::prepareKernelLowering(
          module, &selection.numerical.remainingCopy);
    else {
      if (!kernel::chargeCopy(module, selection.numerical.remainingCopy))
        return error("kernel-lowering", "numerical source copy capacity");
      prepared = cast<ModuleOp>(module->clone());
    }
    if (!prepared)
      return error("kernel-lowering", "numerical source preparation");
    // Checked mathematical normalization does not consult executable binding
    // choices. Apply requests to its owned result before any replacement
    // discovery, rather than cloning the complete source just to pin it.
    auto preparedRoot =
        cast<zkc::protocol_ir::ProtocolModuleOp>(prepared->getBody()->front());
    for (auto declaration : preparedRoot.getBody()
                                .front()
                                .getOps<zkc::local::OperationBindingOp>())
      for (const auto &[name, implementation] : selections)
        if (declaration.getSymName() == name)
          declaration.setImplementation(implementation);
    // Preparation and source discovery run once. All candidate attempts clone
    // this immutable closure; no view into a failed clone becomes source IR.
    if (hasKernels &&
        failed(kernel::discoverKernelCalls(*prepared, options.numericalPolicy,
                                           selection.numerical)))
      return error("kernel-lowering", "numerical occurrence discovery");
    if (hasMaps &&
        failed(mathematical::prepareRetainedMaps(
            *prepared, maps, selection.numerical, options.numericalPolicy)))
      return error("algebra-map-formula");
  }
  for (;;) {
    auto incomingCopy = selection.numerical.remainingCopy;
    auto incomingBytes = selection.numerical.remainingSiteBytes;
    selection.numerical.allowSpeculation(true);
    mathematical::RecipeConstructionWork construction(selection.numerical.work);
    bool speculative = hasNumerical && selection.numerical.canSpeculate() &&
                       selection.numerical.hasAlternatives() &&
                       construction.canDiscard(selection.numerical.work);
    selection.numerical.allowSpeculation(speculative);
    auto copyCeiling =
        speculative ? std::min(incomingCopy,
                               selection.numerical.work.discardedRecipeCopy)
                    : incomingCopy;
    auto byteCeiling =
        speculative
            ? std::min(incomingBytes,
                       selection.numerical.work.discardedRecipeSiteBytes)
            : incomingBytes;
    selection.numerical.remainingCopy = copyCeiling;
    selection.numerical.remainingSiteBytes = byteCeiling;
    // A speculative ceiling temporarily hides the ordered reserve. Settle
    // only actual performed copying/site work on every success or refusal.
    auto settleCeilings = llvm::scope_exit([&] {
      selection.numerical.remainingCopy += incomingCopy - copyCeiling;
      selection.numerical.remainingSiteBytes += incomingBytes - byteCeiling;
    });
    selection.numerical.origins.clear();
    OwningOpRef<ModuleOp> candidate;
    auto clearOrigins =
        llvm::scope_exit([&] { selection.numerical.origins.clear(); });
    ModuleOp selected = module;
    Error refusal = Error::success();
    std::optional<mathematical::RealizationSubject> capacitySubject;
    mathematical::VerificationDecision numericalOutcome;
    bool constructionCapacity = false;
    if (hasNumerical) {
      if (!kernel::chargeCopy(*prepared, selection.numerical.remainingCopy)) {
        if (!speculative)
          return error("kernel-lowering", "numerical candidate copy capacity");
        constructionCapacity = true;
        refusal = error("finite-analysis-limit");
      } else {
        candidate = cast<ModuleOp>(prepared->getOperation()->clone());
        selected = *candidate;
        if (hasKernels &&
            failed(kernel::materializeKernelCalls(
                selected, options.numericalPolicy, nullptr, selection.numerical,
                &numericalOutcome, speculative))) {
          if (numericalOutcome.outcome ==
              mathematical::VerificationObservation::OptionalCapacity) {
            capacitySubject = numericalOutcome.subject;
            constructionCapacity = speculative && numericalOutcome.capacity &&
                                   (numericalOutcome.capacity->owner ==
                                        WorkOwner::AlgorithmExpansion ||
                                    numericalOutcome.capacity->owner ==
                                        WorkOwner::AlgorithmOriginBytes);
          } else
            return error("kernel-lowering", numericalOutcome.detail);
          refusal = error("finite-analysis-limit");
        }
        if (!refusal && hasMaps &&
            failed(mathematical::materializeRetainedMaps(
                selected, maps, selection.numerical, options.numericalPolicy,
                numericalOutcome, speculative))) {
          if (numericalOutcome.outcome ==
              mathematical::VerificationObservation::OptionalCapacity) {
            capacitySubject = numericalOutcome.subject;
            constructionCapacity = speculative && numericalOutcome.capacity &&
                                   (numericalOutcome.capacity->owner ==
                                        WorkOwner::AlgorithmExpansion ||
                                    numericalOutcome.capacity->owner ==
                                        WorkOwner::AlgorithmOriginBytes);
          } else
            return error("algebra-map-lowering", numericalOutcome.detail);
          refusal = error("mathematical-analysis-limit");
        }
        auto candidateRoot = cast<zkc::protocol_ir::ProtocolModuleOp>(
            selected.getBody()->front());
        // Replacement saw fixed requests. Retained declarations keep their
        // original attributes; physical choices carry the requested pins.
        for (auto declaration : candidateRoot.getBody()
                                    .front()
                                    .getOps<zkc::local::OperationBindingOp>()) {
          auto original = originalPins.find(declaration.getSymName().str());
          if (original != originalPins.end())
            declaration.setImplementation(original->second);
        }
        if (!refusal && failed(verify(selected)))
          return error("binding-operation");
      }
    }
    if (auto e = implementation->checkInput(module))
      return e;
    selection.failure = {};
    selection.bindingCursors.clear();
    PhysicalPlan plan;
    Proposer proposer(selected, catalog, failureLocation, selection);
    if (!refusal)
      refusal = proposer.initialize(selections, options.linearContractions);
    size_t groupLimit = 4096;
    while (!refusal) {
      refusal = proposer.populate(plan, groupLimit);
      if (refusal || plan.bindings.size() <= 4096)
        break;
      if (plan.contractions.empty()) {
        refusal = error("binding-declaration-limit");
        break;
      }
      groupLimit = plan.contractions.size() - 1;
    }
    if (!refusal && options.releaseStorage) {
      auto releases =
          proposeStorage(selected, plan.operations, failureLocation);
      if (!releases)
        refusal = releases.takeError();
      else
        plan.releases = std::move(*releases);
    }
    if (!refusal && options.programCapacity) {
      if (!kernel::chargeCopy(selected, selection.numerical.remainingCopy)) {
        constructionCapacity = speculative;
        refusal = error("kernel-lowering");
      } else {
        OwningOpRef<ModuleOp> preflight(cast<ModuleOp>(selected->clone()));
        auto capacity = options.programCapacity(*preflight, plan);
        if (!capacity)
          refusal = capacity.takeError();
        else if (!capacity->empty()) {
          selection.failure.kind = PhysicalFailureKind::OptionalProgramCapacity;
          selection.failure.operations = std::move(*capacity);
          refusal = error("source-limit");
        }
      }
    }
    if (!refusal && hasNumerical &&
        failed(mathematical::verifyNumericalLowering(
            module, selected, options.numericalPolicy, selections,
            &selection.numerical.work, &numericalOutcome))) {
      if (numericalOutcome.outcome !=
          mathematical::VerificationObservation::OptionalCapacity)
        return error("numerical-lowering-correspondence",
                     numericalOutcome.detail);
      capacitySubject = numericalOutcome.subject;
      refusal = error("mathematical-analysis-limit");
    }
    if (!refusal) {
      if (auto e = implementation->checkInput(module))
        return e;
      selection.numerical.origins.clear();
      implementation->realization = std::move(candidate);
      plan.implementation = implementation;
      plan.linearContractions = options.linearContractions;
      return plan;
    }
    const auto &failure = selection.failure;
    if (!capacitySubject && !constructionCapacity &&
        failure.kind == PhysicalFailureKind::Terminal)
      return refusal;
    SmallVector<mathematical::NumericalOccurrence> implicated;
    auto operations = physicalPlanOperations(selected);
    for (auto index : failure.operations) {
      if (index >= operations.size())
        return refusal;
      // A fixed conversion endpoint remains exact. An independently automatic
      // peer may still change its implementation or numerical representation.
      if (index < plan.operations.size())
        if (auto binding = plan.operations[index].binding;
            binding && plan.bindings[*binding].fixed)
          continue;
      append_range(implicated, selection.numerical.owners(operations[index]));
    }
    auto advanced = capacitySubject
                        ? selection.numerical.advanceSubject(
                              *capacitySubject, numericalOutcome.invocation)
                    : constructionCapacity ? selection.numerical.advanceAll()
                                           : selection.advance();
    if (advanced && !*advanced && constructionCapacity && capacitySubject)
      advanced = selection.numerical.advanceAll();
    if (advanced && !*advanced && !capacitySubject && !constructionCapacity)
      advanced = selection.numerical.advance(implicated);
    if (!advanced) {
      consumeError(std::move(refusal));
      return advanced.takeError();
    }
    if (!*advanced)
      return refusal;
    // No failure is swallowed until both classification and attributable
    // monotone advancement have succeeded. Required construction quotas are
    // restored only after charging actual discarded work to their reserve.
    auto copied = copyCeiling - selection.numerical.remainingCopy;
    auto bytes = byteCeiling - selection.numerical.remainingSiteBytes;
    auto &work = selection.numerical.work;
    if (copied > work.discardedRecipeCopy ||
        bytes > work.discardedRecipeSiteBytes || !construction.discard(work))
      return refusal;
    work.discardedRecipeCopy -= copied;
    work.discardedRecipeSiteBytes -= bytes;
    selection.numerical.remainingCopy = copyCeiling;
    selection.numerical.remainingSiteBytes = byteCeiling;
    selection.numerical.origins.clear();
    consumeError(std::move(refusal));
  }
}

namespace {
Error checkFixed(const BindingApplication &source,
                 const BindingApplication &selected,
                 std::optional<StringRef> request, bool recordedFixed) {
  if (!sameLogical(source, selected))
    return error("binding-operation");
  const bool fixed = request.has_value() || !source.implementation.empty();
  if (fixed != recordedFixed ||
      (!source.implementation.empty() &&
       selected.implementation != source.implementation) ||
      (request && selected.implementation != *request))
    return error("binding-selection-conflict");
  return Error::success();
}
Error checkDefaultPorts(TypeRange logical, ArrayRef<Type> recorded) {
  if (logical.size() != recorded.size())
    return error("binding-operation-signature");
  for (auto [source, selected] : zip(logical, recorded)) {
    auto expected = defaultPort(source);
    if (!expected)
      return expected.takeError();
    if (*expected != selected)
      return error("binding-operation-signature");
  }
  return Error::success();
}
Error checkInstalledPorts(TypeRange recorded, ArrayRef<BoundType> installed) {
  if (recorded.size() != installed.size())
    return error("binding-operation-signature");
  for (auto [type, expected] : zip(recorded, installed)) {
    if (!type)
      return error("binding-operation-signature");
    auto actual = encodeBoundType(type, true);
    if (!actual)
      return actual.takeError();
    if (!(*actual == expected))
      return error("binding-operation-signature");
  }
  return Error::success();
}

// This traversal checks all *actual* SSA operand uses. It neither calls the
// opportunity finder nor enumerates uses supplied by a proposed group.
Expected<SmallVector<OperationIndex>> checkAllUses(Operation *op,
                                                   const PhysicalPlan &plan,
                                                   const Indices &indices,
                                                   Location *failureLocation) {
  locate(failureLocation, op);
  auto function = op->getParentOfType<zkc::local::FuncOp>();
  auto producer = dyn_cast<DiagonalProducerInterface>(op);
  if (!function || function.isDeclaration() ||
      !hasSingleElement(function.getBody()) ||
      mayBeGraphRegion(*op->getParentRegion()) || !producer)
    return error("binding-contraction");
  auto production = producer.getDiagonalProducerRoles();
  if (!production || production->result >= op->getNumResults() ||
      production->factorsOperand >= op->getNumOperands() ||
      production->valuesOperand >= op->getNumOperands() ||
      production->factorsOperand == production->valuesOperand)
    return error("binding-contraction");
  const auto &decision = plan.operations[indices.lookup(op)];
  if (!decision.binding)
    return error("binding-contraction");
  const auto &application =
      plan.bindings[*decision.binding].binding.application;
  // Admission is independent of the catalog's candidate-name derivation.
  // Resolve the full selected contract instance, then inspect its role ports.
  auto installed = resolveBinding(application, true);
  if (!installed)
    return installed.takeError();
  const auto *facts = operationContracts(application.contract);
  if (!facts || !facts->diagonalMap ||
      facts->diagonalMap->factorsOperand != production->factorsOperand ||
      facts->diagonalMap->valuesOperand != production->valuesOperand ||
      facts->diagonalMap->result != production->result)
    return error("binding-contraction");
  // Complete recorded ports were checked before this traversal. Requiring
  // the exact installed role and view port also excludes a dense contract
  // masquerading as a contraction group with internally consistent ports.
  const auto &view = installed->outputs[production->result];
  if (!isDiagonalRepresentation(view.representation))
    return error("binding-contraction");
  auto result = op->getResult(production->result);
  if (result.use_empty() ||
      op->getOperand(production->valuesOperand).getType() != result.getType())
    return error("binding-contraction");
  SmallVector<OperationIndex> consumers;
  for (OpOperand &use : result.getUses()) {
    auto *user = use.getOwner();
    locate(failureLocation, user);
    auto consumer = dyn_cast<DiagonalContractionInterface>(user);
    if (!consumer || user->getBlock() != op->getBlock() ||
        !op->isBeforeInBlock(user))
      return error("binding-contraction");
    auto contraction = consumer.getDiagonalContractionRoles();
    if (!contraction || use.getOperandNumber() != contraction->valuesOperand ||
        contraction->coefficientsOperand >= user->getNumOperands() ||
        contraction->coefficientsOperand == contraction->valuesOperand ||
        op->getOperand(production->factorsOperand).getType() !=
            user->getOperand(contraction->coefficientsOperand).getType())
      return error("binding-contraction");
    auto index = indices.lookup(user);
    const auto &selected = plan.operations[index];
    if (!selected.binding || selected.inputs[use.getOperandNumber()] !=
                                 decision.outputs[production->result])
      return error("binding-contraction");
    const auto &consumerApplication =
        plan.bindings[*selected.binding].binding.application;
    auto consumerInstalled = resolveBinding(consumerApplication, true);
    if (!consumerInstalled)
      return consumerInstalled.takeError();
    const auto *consumerFacts =
        operationContracts(consumerApplication.contract);
    if (!consumerFacts || !consumerFacts->linearContraction ||
        consumerFacts->linearContraction->coefficientsOperand !=
            contraction->coefficientsOperand ||
        consumerFacts->linearContraction->valuesOperand !=
            contraction->valuesOperand ||
        !(consumerInstalled->inputs[contraction->valuesOperand] == view))
      return error("binding-contraction");
    consumers.push_back(index);
  }
  llvm::sort(consumers);
  return consumers;
}
} // namespace

Expected<CheckedPhysicalPlan> validatePhysical(ModuleOp module,
                                               const PhysicalPlan &plan,
                                               const CandidateCatalog &catalog,
                                               Location *failureLocation) {
  locate(failureLocation, module);
  if (!plan.implementation)
    return error("binding-stale-selection");
  // Validate the source-to-implementation edge before physical choices.
  if (auto e = plan.implementation->verifyRealization(module))
    return e;
  ModuleOp selected = plan.implementation->subject();
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(&selected.getBody()->front());
  auto operations = physicalPlanOperations(selected);
  auto indices = indexOperations(operations);
  if (plan.operations.size() != operations.size())
    return error("binding-plan-coverage");
  if (plan.bindings.size() > 4096)
    return error("binding-declaration-limit");
  for (auto [i, decision] : enumerate(plan.operations))
    if (decision.operation != i ||
        (decision.binding && *decision.binding >= plan.bindings.size()))
      return error("binding-plan-coverage");

  std::map<std::string, std::string> requests;
  for (const auto &[key, implementation] : plan.implementation->selections())
    if (!requests.emplace(key, implementation).second)
      return error("binding-duplicate-selection");
  std::set<std::string> symbols;
  for (auto &op : root.getBody().front())
    if (!isa<zkc::local::OperationBindingOp>(op))
      if (auto name = op.getAttrOfType<StringAttr>("sym_name"))
        symbols.insert(name.getValue().str());
  std::map<std::string, BindingIndex> originals;
  size_t declarationIndex = 0;
  for (auto declaration :
       root.getBody().front().getOps<zkc::local::OperationBindingOp>()) {
    locate(failureLocation, declaration);
    if (declarationIndex >= plan.bindings.size())
      return error("binding-plan-coverage");
    const auto &decision = plan.bindings[declarationIndex];
    auto source = readBinding(declaration);
    if (!source)
      return source.takeError();
    if (decision.purpose != BindingPurpose::Original ||
        decision.declaration != indices.lookup(declaration) ||
        decision.binding.name != source->name ||
        decision.location != indices.lookup(declaration))
      return error("binding-plan-coverage");
    auto request = requests.find(source->name);
    if (auto e = checkFixed(source->application, decision.binding.application,
                            request == requests.end()
                                ? std::nullopt
                                : std::optional<StringRef>(request->second),
                            decision.fixed))
      return e;
    if (!decision.fixed) {
      auto candidates = catalog.implementations(source->application);
      if (!candidates)
        return candidates.takeError();
      if (!is_contained(*candidates,
                        decision.binding.application.implementation))
        return error("binding-implementation");
    }
    if (request != requests.end())
      requests.erase(request);
    originals.emplace(source->name, declarationIndex++);
  }
  if (!requests.empty())
    return error("binding-unknown-selection");
  for (auto [i, decision] : enumerate(plan.bindings)) {
    locate(failureLocation, root);
    if (decision.location >= operations.size())
      return error("binding-plan-coverage");
    locate(failureLocation, operations[decision.location]);
    if (i >= declarationIndex &&
        (decision.purpose == BindingPurpose::Original || decision.declaration ||
         decision.fixed))
      return error("binding-plan-coverage");
    if (!symbols.insert(decision.binding.name).second)
      return error("binding-plan-coverage");
    if (auto e = checkBindingDeclaration(decision.binding.name,
                                         decision.binding.application, true))
      return e;
  }

  // Check complete definition and use signatures before consulting any ports
  // by SSA index. This makes malformed proposal vectors ordinary refusals.
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.inputs.size() != op->getNumOperands() ||
        decision.outputs.size() != op->getNumResults())
      return error("binding-operation-signature");
    size_t blockIndex = 0;
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        if (blockIndex >= decision.blockArguments.size())
          return error("binding-operation-signature");
        if (auto e = checkDefaultPorts(block.getArgumentTypes(),
                                       decision.blockArguments[blockIndex++]))
          return e;
      }
    if (blockIndex != decision.blockArguments.size())
      return error("binding-operation-signature");
    if (auto signature = op->getAttrOfType<TypeAttr>("function_type")) {
      auto functionType = cast<FunctionType>(signature.getValue());
      if (!decision.functionType)
        return error("binding-operation-signature");
      if (auto e = checkDefaultPorts(functionType.getInputs(),
                                     decision.functionType.getInputs()))
        return e;
      if (auto e = checkDefaultPorts(functionType.getResults(),
                                     decision.functionType.getResults()))
        return e;
    } else if (decision.functionType)
      return error("binding-operation-signature");

    auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
    if (ref) {
      if (!decision.binding)
        return error("binding-plan-coverage");
      auto original = originals.find(ref.getValue().str());
      if (original == originals.end())
        return error("binding-reference");
      const auto &binding = plan.bindings[*decision.binding];
      const auto &base = plan.bindings[original->second];
      // Exact contract AND arguments, not merely physical signature equality.
      // The source verifier also checks its ODS association and parameters.
      if (failed(verifyBoundOperation(op, false)))
        return error("binding-operation");
      if (!sameLogical(binding.binding.application, base.binding.application))
        return error("binding-operation");
      if (*decision.binding != original->second &&
          (binding.purpose != BindingPurpose::Contraction || base.fixed))
        return error(base.fixed ? "binding-selection-conflict"
                                : "binding-plan-coverage");
      if (binding.purpose == BindingPurpose::Contraction &&
          !is_contained(
              catalog.diagonalImplementations(base.binding.application),
              binding.binding.application.implementation))
        return error("binding-implementation");
      auto installed = resolveBinding(binding.binding.application, true);
      if (!installed)
        return installed.takeError();
      if (auto e = checkInstalledPorts(decision.inputs, installed->inputs))
        return e;
      if (auto e = checkInstalledPorts(decision.outputs, installed->outputs))
        return e;
    } else {
      if (decision.binding || (op->getParentOfType<zkc::local::FuncOp>() &&
                               !interfaceOperation(op)))
        return error("binding-plan-coverage");
      if (auto e = checkDefaultPorts(op->getOperandTypes(), decision.inputs))
        return e;
      if (auto e = checkDefaultPorts(op->getResultTypes(), decision.outputs))
        return e;
    }
  }

  // Selected Local preorder and operand order determine instruction positions.
  // No sharing, hoisting, path search, or inferred purity is permitted here.
  std::map<Operation *, std::set<std::string>> sites;
  for (auto *op : operations)
    if (auto function = op->getParentOfType<zkc::local::FuncOp>())
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        sites[function].insert(site.getValue().str());
  SmallVector<unsigned> references(plan.bindings.size(), 0);
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.binding)
      ++references[*decision.binding];
    size_t crossing = 0;
    for (auto [operand, value] : enumerate(op->getOperands())) {
      auto from = valuePort(value, plan, indices);
      auto to = decision.inputs[operand];
      if (from == to)
        continue;
      if (crossing >= decision.conversions.size())
        return error("binding-no-conversion");
      const auto &conversion = decision.conversions[crossing++];
      if (conversion.operand != operand || conversion.from != from ||
          conversion.to != to || conversion.binding >= plan.bindings.size())
        return error("binding-no-conversion");
      const auto &binding = plan.bindings[conversion.binding];
      auto source = encodeBoundType(from, true);
      if (!source)
        return source.takeError();
      auto target = encodeBoundType(to, true);
      if (!target)
        return target.takeError();
      if (binding.purpose != BindingPurpose::Conversion)
        return error("binding-no-conversion");
      if (auto e = checkDirectConversion(binding.binding.application, *source,
                                         *target))
        return e;
      auto available = catalog.conversions(*source, *target);
      if (none_of(available, [&](const auto &candidate) {
            return sameApplication(candidate, binding.binding.application);
          }))
        return error("binding-no-conversion");
      auto function = op->getParentOfType<zkc::local::FuncOp>();
      StringRef site = conversion.site;
      const bool validSite =
          !site.empty() && site.size() <= 512 &&
          (isAlpha(site.front()) || site.front() == '_') &&
          all_of(site, [](char c) {
            return isAlnum(c) || c == '_' || c == '.' || c == '-';
          });
      if (!function || !validSite ||
          !sites[function].insert(conversion.site).second)
        return error("binding-plan-coverage");
      if (references[conversion.binding] == 0 && binding.location != i)
        return error("binding-plan-coverage");
      ++references[conversion.binding];
    }
    if (crossing != decision.conversions.size())
      return error("binding-no-conversion");
  }

  std::set<OperationIndex> grouped;
  OperationIndex previous = 0;
  LinearContractionStats stats;
  for (const auto &group : plan.contractions) {
    locate(failureLocation, root);
    if (!plan.linearContractions || group.producer >= operations.size() ||
        group.producer <= previous || group.consumers.empty())
      return error("binding-contraction");
    previous = group.producer;
    auto actual = checkAllUses(operations[group.producer], plan, indices,
                               failureLocation);
    if (!actual)
      return actual.takeError();
    if (*actual != group.consumers)
      return error("binding-contraction");
    SmallVector<OperationIndex> members{group.producer};
    append_range(members, *actual);
    for (auto index : members) {
      const auto &decision = plan.operations[index];
      if (!grouped.insert(index).second || !decision.binding ||
          plan.bindings[*decision.binding].purpose !=
              BindingPurpose::Contraction ||
          references[*decision.binding] != 1 ||
          plan.bindings[*decision.binding].location != index)
        return error("binding-contraction");
    }
    ++stats.selectedProducers;
    stats.selectedPairs += actual->size();
  }
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.binding &&
        plan.bindings[*decision.binding].purpose ==
            BindingPurpose::Contraction &&
        !grouped.count(i))
      return error("binding-contraction");
    // Explicit diagonal implementations also require all-uses preflight; they
    // do not have to be automatic, freshly cloned contraction groups.
    for (auto type : decision.outputs)
      if (auto physical = dyn_cast<zkc::plan::DataType>(type))
        if (isDiagonalRepresentation(physical.getRepresentation())) {
          auto uses = checkAllUses(op, plan, indices, failureLocation);
          if (!uses)
            return uses.takeError();
        }
  }
  for (auto [i, binding] : enumerate(plan.bindings))
    if (binding.purpose != BindingPurpose::Original && references[i] == 0)
      return error("binding-plan-coverage");
  // Statistics use the existing opportunity analysis, never as the validator's
  // all-uses or group-completeness oracle above.
  if (plan.linearContractions)
    for (auto function : root.getBody().front().getOps<zkc::local::FuncOp>())
      (void)findLinearContractions(function, stats);
  if (auto e = validateStorage(selected, plan.operations, plan.releases,
                               failureLocation))
    return e;
  if (auto e = plan.implementation->checkInput(module))
    return e;
  return CheckedPhysicalPlan(plan, stats);
}
} // namespace zkc::target
