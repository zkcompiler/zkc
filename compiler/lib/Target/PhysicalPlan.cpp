#include "PhysicalPlan.h"
#include "../Transforms/Computation/Support.h"
#include "../Transforms/NumericalSelection.h"
#include "../Transforms/ScopedPreparation.h"
#include "AggregateLayouts.h"
#include "ExecutionPorts.h"
#include "NativePlanTypes.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/RegionKindInterface.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/TimeProfiler.h"
#include <cstdint>
#include <deque>
#include <map>
#include <set>

using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
namespace zkc::target {
namespace {
std::string structure(ModuleOp module) {
  std::string result;
  raw_string_ostream out(result);
  module->print(out, OpPrintingFlags().printGenericOpForm().enableDebugInfo());
  return result;
}
SmallVector<const void *> identities(ModuleOp module) {
  SmallVector<const void *> result;
  module->walk<WalkOrder::PreOrder>([&](Operation *op) {
    result.push_back(op);
    for (auto &region : op->getRegions())
      for (auto &block : region) {
        result.push_back(&block);
        for (auto arg : block.getArguments())
          result.push_back(arg.getAsOpaquePointer());
      }
    for (auto value : op->getResults())
      result.push_back(value.getAsOpaquePointer());
  });
  return result;
}
} // namespace
struct NativeFunctionPortSelection {
  std::string function;
  bool output;
  unsigned port;
  Type physicalType;
};
struct NativeValueLayoutSelection {
  std::string function, site;
  unsigned result;
  Type physicalType;
};
struct InputSnapshot {
  ModuleOp subject;
  std::string contents;
  SmallVector<const void *> addresses;
  protocol::Assignments selections;
  bool linearContractions;
  MathematicalSelectionPolicy numericalPolicy;
  SmallVector<NativeFunctionPortSelection> functionPorts;
  SmallVector<NativeValueLayoutSelection> valueLayouts;
  CpuTarget cpuTarget;
  // This owned payload is the numerical decision, including actual recipes,
  // generated bindings, sites and SSA. Policy flags are not a replay format.
  // Accessible only inside Target; callers can obtain independent clones.
  // Actual selected finite preparation, retained for independent composition.
  // Source/candidate mutation cannot turn a producer cache into evidence.
  OwningOpRef<ModuleOp> finite;
  OwningOpRef<ModuleOp> numerical;
  Error check(ModuleOp module) const {
    // Compare only fresh live IR against opaque saved addresses. Never walk or
    // dereference a saved operation/value, including after erasure/replacement.
    if (module != subject || identities(module) != addresses ||
        structure(module) != contents)
      return error("binding-stale-selection");
    return Error::success();
  }
};
SmallVector<Operation *> physicalPlanOperations(ModuleOp module) {
  SmallVector<Operation *> result;
  module->walk<WalkOrder::PreOrder>(
      [&](Operation *op) { result.push_back(op); });
  return result;
}
Error CheckedPhysicalPlan::checkInput(ModuleOp module) const {
  return plan.input->check(module);
}
Expected<ModuleOp> PhysicalPlan::selectedSubject(ModuleOp source) const {
  if (!input)
    return error("binding-stale-selection");
  if (auto e = input->check(source))
    return e;
  return input->numerical ? *input->numerical : source;
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
Expected<Type> defaultPort(Type type) { return defaultPlanType(type); }
Expected<FunctionType>
selectedFunctionType(Operation *op, FunctionType logical,
                     ArrayRef<NativeFunctionPortSelection> selections) {
  SmallVector<Type> inputs, outputs;
  std::set<std::pair<bool, unsigned>> seen;
  auto name = op->getAttrOfType<StringAttr>("sym_name");
  for (const auto &choice : selections)
    if (name && choice.function == name.getValue()) {
      if (!seen.emplace(choice.output, choice.port).second)
        return error("binding-duplicate-selection");
      if (choice.port >=
          (choice.output ? logical.getNumResults() : logical.getNumInputs()))
        return error("binding-unknown-selection");
    }
  for (bool output : {false, true}) {
    auto &ports = output ? outputs : inputs;
    auto types = output ? logical.getResults() : logical.getInputs();
    for (auto [index, source] : enumerate(types)) {
      const NativeFunctionPortSelection *choice = nullptr;
      for (const auto &candidate : selections)
        if (name && candidate.function == name.getValue() &&
            candidate.output == output && candidate.port == index)
          choice = &candidate;
      if (!choice) {
        auto physical = defaultPort(source);
        if (!physical)
          return physical.takeError();
        ports.push_back(*physical);
        continue;
      }
      auto type = choice->physicalType;
      if (auto e = checkPhysicalType(type))
        return e;
      if (logicalValueType(type) != source)
        return error("binding-operation-signature");
      ports.push_back(type);
    }
  }
  return FunctionType::get(op->getContext(), inputs, outputs);
}

Expected<SmallVector<Type>> variantPorts(Type type, unsigned alternative) {
  if (auto e = checkPhysicalType(type))
    return e;
  auto variant = dyn_cast<data::VariantType>(logicalValueType(type));
  if (!variant || alternative >= variant.getAlternatives().size())
    return error("variant-type");
  return data::variantPayloadTypes(
      type, variant.getAlternatives()[alternative].getLabel().getValue());
}
bool sameApplication(const NativeBindingApplication &a,
                     const NativeBindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments &&
         a.implementation == b.implementation && a.valueType == b.valueType;
}
bool sameLogical(const NativeBindingApplication &a,
                 const NativeBindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments;
}
bool interfaceOperation(Operation *op) {
  return isa<zkc::exec::BooleanOp, zkc::exec::ReturnOp, zkc::exec::CompleteOp,
             zkc::exec::RejectOp, zkc::exec::VariantOp, zkc::exec::MatchOp,
             zkc::exec::TestOp, zkc::exec::RangeOp,
             zkc::runtime::ReleaseBindingsOp>(op);
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
Type valuePort(Value value, const PhysicalPlan &plan, const Indices &indices,
               const ExecutionPorts &flow) {
  const auto &definition = flow.definition(value);
  const auto &decision = plan.operations[indices.lookup(definition.owner)];
  return definition.argument
             ? decision.blockArguments[definition.block][definition.port]
             : decision.outputs[definition.port];
}
std::string fresh(std::set<std::string> &used, StringRef prefix,
                  unsigned &next) {
  std::string result;
  do {
    result = prefix.str() + std::to_string(next++);
  } while (!used.insert(result).second);
  return result;
}
// Availability is separate from preference and from Contracts admission.
// This reader also sees unused bindings, unused services and every aggregate
// child; actual service draw support cannot be inferred from an index result.
Error checkTargetPlan(ModuleOp module, const PhysicalPlan &plan,
                      const CpuTarget &cpuTarget, Location *failureLocation) {
  auto type = [&](Type physical) { return cpuTarget.checkType(physical); };
  auto ports = [&](TypeRange physical) -> Error {
    for (auto port : physical)
      if (auto e = type(port))
        return e;
    return Error::success();
  };
  auto operations = physicalPlanOperations(module);
  for (const auto &binding : plan.bindings) {
    if (binding.location < operations.size())
      locate(failureLocation, operations[binding.location]);
    auto installed =
        resolveNativeApplication(binding.binding.application, true);
    if (!installed)
      return installed.takeError();
    if (auto e = cpuTarget.checkNativeApplication(binding.binding.application))
      return e;
  }
  for (auto [index, decision] : enumerate(plan.operations)) {
    if (index < operations.size())
      locate(failureLocation, operations[index]);
    if (auto e = ports(decision.inputs))
      return e;
    if (auto e = ports(decision.outputs))
      return e;
    for (const auto &arguments : decision.blockArguments)
      if (auto e = ports(arguments))
        return e;
    if (decision.functionType) {
      if (auto e = ports(decision.functionType.getInputs()))
        return e;
      if (auto e = ports(decision.functionType.getResults()))
        return e;
    }
  }
  Error refusal = Error::success();
  module.walk([&](zkc::protocol_ir::ParticipantOp participant) {
    if (refusal)
      return;
    locate(failureLocation, participant);
    if (auto services = participant->getAttrOfType<ArrayAttr>("service_ports"))
      for (auto item : services) {
        auto port = cast<ArrayAttr>(item);
        if (auto e =
                cpuTarget.checkService(cast<StringAttr>(port[1]).getValue())) {
          refusal = std::move(e);
          return;
        }
      }
  });
  return refusal;
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
std::vector<uintptr_t>
argumentIdentities(const NativeBindingApplication &application) {
  std::vector<uintptr_t> result;
  for (Attribute argument : application.arguments)
    result.push_back(
        reinterpret_cast<uintptr_t>(argument.getAsOpaquePointer()));
  return result;
}
struct ImplementationCursor {
  NativeBindingApplication logical;
  SmallVector<mathematical::NumericalOccurrence> owners;
  // Empty for generated bindings: their identity is the owned occurrence set
  // and logical application, not a generated symbol spelling.
  std::string authored;
  std::vector<std::string> candidates;
  size_t next = 0;
  std::optional<size_t> parent;
  bool targetWithheld = false;
};
class PhysicalSelection {
public:
  mathematical::NumericalSelection numerical;
  CpuTarget cpuTarget;
  SmallVector<ImplementationCursor, 2> implementations;
  using ImplementationKey =
      std::tuple<std::string, std::vector<uintptr_t>,
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
  choose(const NativeBindingApplication &application,
         std::optional<StringRef> request, const CandidateCatalog &catalog,
         ArrayRef<mathematical::NumericalOccurrence> owners, StringRef authored,
         std::optional<size_t> &cursor) {
    if (request || !application.implementation.empty())
      return selectImplementation(application, request, cpuTarget);
    auto logical = resolveNativeApplication(application, false);
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
        keys.emplace_back(application.contract, argumentIdentities(application),
                          std::vector{owner}, std::string{});
    } else
      keys.emplace_back(application.contract, argumentIdentities(application),
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
      target.targetWithheld |= source.targetWithheld;
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
      auto descriptor = installedImplementations().find(
          selected.contract, selected.implementation);
      // Candidate order never supplies an implementation's explicit premise.
      // Trusted runtime linking permission remains an independent obligation.
      if (descriptor && descriptor->requiresExplicitSelection)
        continue;
      auto installed = descriptor &&
                               descriptor->family !=
                                   ImplementationDescriptor::Family::Exact &&
                               !selected.valueType
                           ? resolveNativeApplication(selected, false)
                           : resolveNativeApplication(selected, true);
      Error refusal = installed ? cpuTarget.checkNativeImplementation(selected)
                                : installed.takeError();
      if (!refusal &&
          !(descriptor &&
            descriptor->family != ImplementationDescriptor::Family::Exact &&
            !selected.valueType))
        refusal = cpuTarget.checkNativeApplication(selected);
      if (!refusal)
        return ImplementationChoice{std::move(selected), false};
      if (refusal)
        visitErrors(refusal, [&](const ErrorInfoBase &info) {
          if (info.isA<Refusal>())
            entry.targetWithheld |= static_cast<const Refusal &>(info).code ==
                                    "cpu-target-unavailable";
        });
      bool unavailable;
      if (auto e = decline(std::move(refusal),
                           {"binding-implementation", "cpu-target-unavailable"},
                           unavailable))
        return e;
    }
    failure.kind = PhysicalFailureKind::ImplementationUnavailable;
    return error(entry.targetWithheld ? "cpu-target-unavailable"
                                      : "binding-implementation");
  }
  Expected<bool> advance() {
    // An exhausted implementation at one endpoint can still leave a usable
    // automatic choice at the other. Never reset either endpoint's cursor.
    auto bindings = failure.bindings;
    llvm::sort(bindings);
    bool advanced = false;
    std::set<size_t> visited;
    for (auto binding : bindings) {
      if (binding >= bindingCursors.size() || !bindingCursors[binding])
        continue;
      auto id = representative(*bindingCursors[binding]);
      if (!visited.insert(id).second)
        continue;
      auto &entry = implementations[id];
      if (entry.next + 1 < entry.candidates.size()) {
        if (!numerical.chargeCatalog())
          return error("finite-analysis-limit");
        ++entry.next;
        advanced = true;
        // Capacity concerns the complete plan. Advance its automatic
        // choices together instead of rebuilding every prefix.
        if (failure.kind != PhysicalFailureKind::OptionalProgramCapacity)
          return true;
      }
    }
    return advanced;
  }
};
Expected<NativeBindingApplication>
chooseConversion(Type from, Type to, const CandidateCatalog &catalog,
                 mathematical::NumericalSelection &selection,
                 const CpuTarget &cpuTarget) {
  if (!selection.chargeCatalog())
    return error("finite-analysis-limit");
  auto candidates = catalog.conversions(from, to);
  if (!selection.chargeCatalog(candidates.size()))
    return error("finite-analysis-limit");
  for (auto candidate : candidates) {
    // A catalog suggestion can name an uninstalled adapter. Decline that
    // suggestion; authored bindings and explicit pins were admitted separately.
    if (auto e = checkDirectConversion(candidate, from, to)) {
      bool unavailable;
      if (auto terminal =
              decline(std::move(e),
                      {"binding-no-conversion", "binding-implementation",
                       "binding-conversion"},
                      unavailable))
        return terminal;
      continue;
    }
    // Special adapters bypass ImplementationCatalog. Check both independently
    // resolved endpoints after their conversion law has been admitted.
    auto installed = resolveNativeApplication(candidate, true);
    if (!installed)
      return installed.takeError();
    if (auto e = cpuTarget.checkNativeApplication(candidate)) {
      bool unavailable;
      if (auto terminal =
              decline(std::move(e), {"cpu-target-unavailable"}, unavailable))
        return terminal;
      continue;
    }
    return candidate;
  }
  return error("binding-no-conversion");
}

SmallVector<LinearContractionGroup> findExecutionContractions(
    const ExecutionPorts &flow, ArrayRef<Operation *> operations,
    const Indices &indices,
    llvm::function_ref<const OperationContracts *(Operation *)> facts,
    LinearContractionStats &stats) {
  SmallVector<LinearContractionGroup> groups;
  for (auto *op : operations) {
    const auto *contract = facts(op);
    if (!contract || !contract->diagonalMap || !flow.get(op).step)
      continue;
    ++stats.producers;
    auto producer = dyn_cast<DiagonalProducerInterface>(op);
    auto roles = producer ? producer.getDiagonalProducerRoles() : std::nullopt;
    if (!roles)
      continue;
    const auto &production = *roles;
    auto inputs = flow.inputs(op), outputs = flow.outputs(op);
    if (production.result >= outputs.size() ||
        production.factorsOperand >= inputs.size() ||
        production.valuesOperand >= inputs.size() ||
        production.factorsOperand == production.valuesOperand ||
        inputs[production.valuesOperand].getType() !=
            outputs[production.result].getType())
      continue;
    auto uses = flow.uses(outputs[production.result]);
    if (uses.empty())
      continue;
    LinearContractionGroup group{op,
                                 {production.factorsOperand,
                                  production.valuesOperand, production.result},
                                 {}};
    bool compatible = true;
    for (auto use : uses) {
      const auto *consumer = facts(use.operation);
      if (!consumer || !consumer->linearContraction ||
          flow.enclosingBody(use.operation) != flow.enclosingBody(op) ||
          indices.lookup(use.operation) <= indices.lookup(op)) {
        compatible = false;
        break;
      }
      auto contraction = dyn_cast<DiagonalContractionInterface>(use.operation);
      auto resolved = contraction ? contraction.getDiagonalContractionRoles()
                                  : std::nullopt;
      if (!resolved) {
        compatible = false;
        break;
      }
      const auto &roles = *resolved;
      auto consumed = flow.inputs(use.operation);
      if (use.operand != roles.valuesOperand ||
          roles.coefficientsOperand >= consumed.size() ||
          roles.coefficientsOperand == roles.valuesOperand ||
          consumed[roles.coefficientsOperand].getType() !=
              inputs[production.factorsOperand].getType()) {
        compatible = false;
        break;
      }
      group.uses.push_back(
          {use.operation, {roles.coefficientsOperand, roles.valuesOperand}});
    }
    if (compatible) {
      ++stats.eligibleProducers;
      stats.eligiblePairs += group.uses.size();
      llvm::sort(group.uses, [&](const auto &left, const auto &right) {
        return indices.lookup(left.consumer) < indices.lookup(right.consumer);
      });
      groups.push_back(std::move(group));
    }
  }
  return groups;
}
class Proposer {
  ModuleOp module;
  zkc::protocol_ir::ProtocolModuleOp root;
  const CandidateCatalog &catalog;
  SmallVector<Operation *> operations;
  Indices indices;
  Location *failureLocation;
  PhysicalSelection &selection;
  std::optional<ExecutionPorts> execution;
  ExecutionPorts &flow() { return *execution; }
  ArrayRef<NativeFunctionPortSelection> functionPorts;
  ArrayRef<NativeValueLayoutSelection> valueLayouts;
  SmallVector<BindingDecision> originals;
  std::map<std::string, BindingIndex> names;
  std::map<std::string, SmallVector<OperationIndex>> bindingUses;
  SmallVector<LinearContractionGroup> eligible;
  std::set<std::string> symbols;

  Error familyFailure(Error refusal, const PhysicalPlan &plan,
                      OperationIndex index) {
    auto binding = *plan.operations[index].binding;
    const auto &decision = plan.bindings[binding];
    // Malformed applications and exact authored selections are terminal.
    // Only a deferred automatic application's unavailable specialization can
    // advance its already bounded implementation cursor.
    if (decision.fixed || decision.binding.application.valueType)
      return refusal;
    return handleErrors(std::move(refusal),
                        [&](const Refusal &failure) -> Error {
                          if (failure.code == "binding-implementation" ||
                              failure.code == "binding-representation") {
                            selection.failure.kind =
                                PhysicalFailureKind::ImplementationUnavailable;
                            selection.failure.operations = {index};
                            selection.failure.bindings = {binding};
                          }
                          return error(failure.code, failure.detail);
                        });
  }

  Error aggregatePorts(PhysicalPlan &plan, llvm::DenseMap<Value, Type> &hints) {
    AggregateLayouts layouts(selection.numerical, [&](ArrayRef<size_t> owners) {
      auto &failure = selection.failure;
      failure.kind = PhysicalFailureKind::ConversionUnavailable;
      for (auto owner : owners) {
        failure.operations.push_back(owner);
        if (auto binding = plan.operations[owner].binding)
          failure.bindings.push_back(*binding);
      }
    });
    auto aggregate = [](Type type) {
      auto kind = planTypeConstructor(type);
      return kind == "sequence" || kind == "variant" || kind == "field_array" ||
             kind == "fixed_vector";
    };
    auto pin = [&](Value value, Type type, OperationIndex owner) -> Error {
      auto id = layouts.get(value);
      if (!id)
        return id.takeError();
      return layouts.pin(*id, type, owner);
    };
    auto equate = [&](Value left, Value right) -> Error {
      auto a = layouts.get(left);
      if (!a)
        return a.takeError();
      auto b = layouts.get(right);
      if (!b)
        return b.takeError();
      return layouts.equate(*a, *b);
    };
    auto payload = [&](Value value, AggregateLayouts::Id child,
                       bool packing) -> Error {
      auto id = layouts.get(value);
      if (!id)
        return id.takeError();
      return packing ? layouts.pack(*id, child, aggregate(value.getType()))
                     : layouts.equate(*id, child);
    };
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      const auto &d = plan.operations[index];
      if (d.functionType && flow().callers(op).empty())
        for (auto [value, type] :
             zip(flow().body(flow().get(op).bodies[0]).arguments,
                 d.functionType.getInputs()))
          if (auto e = pin(value, type, index))
            return e;
      if (d.binding) {
        const auto &app = plan.bindings[*d.binding].binding.application;
        auto descriptor =
            installedImplementations().find(app.contract, app.implementation);
        using Family = ImplementationDescriptor::Family;
        if (descriptor && descriptor->family == Family::Sequence &&
            !app.valueType) {
          if (app.contract == "sequence.append") {
            if (auto e = equate(flow().inputs(op)[0], flow().outputs(op)[0]))
              return e;
            auto container = layouts.get(flow().outputs(op)[0]);
            if (!container)
              return container.takeError();
            if (auto e = payload(flow().inputs(op)[1],
                                 layouts.child(*container, 0), true))
              return e;
          } else if (app.contract == "sequence.at") {
            auto container = layouts.get(flow().inputs(op)[0]);
            if (!container)
              return container.takeError();
            if (auto e = payload(flow().outputs(op)[0],
                                 layouts.child(*container, 0), false))
              return e;
          } else if (app.contract != "sequence.empty") {
            for (auto [value, type] : zip(flow().outputs(op), d.outputs))
              if (auto e = pin(value, type, index))
                return e;
          }
        } else {
          // Exact definitions, explicit parameters, and dense provider layouts
          // constrain aggregate ports. Observation's inferred payload does not.
          bool observation = descriptor &&
                             descriptor->family == Family::Observation &&
                             !app.valueType;
          for (auto [value, type] : zip(flow().inputs(op), d.inputs))
            if (aggregate(value.getType()) && !observation)
              if (auto e = pin(value, type, index))
                return e;
          for (auto [value, type] : zip(flow().outputs(op), d.outputs))
            if (auto e = pin(value, type, index))
              return e;
        }
      } else if (auto call = dyn_cast<zkc::protocol_ir::LocalCallOp>(op)) {
        auto *callee =
            SymbolTable::lookupNearestSymbolFrom(op, call.getCalleeAttr());
        auto type = plan.operations[indices.lookup(callee)].functionType;
        for (auto [value, target] : zip(flow().inputs(op), type.getInputs()))
          if (aggregate(value.getType()))
            if (auto e = pin(value, target, index))
              return e;
        for (auto [value, target] : zip(flow().outputs(op), type.getResults()))
          if (auto e = pin(value, target, index))
            return e;
      } else if (isa<zkc::exec::VariantOp>(op)) {
        auto container = layouts.get(flow().outputs(op)[0]);
        if (!container)
          return container.takeError();
        auto variant =
            dyn_cast<data::VariantType>(flow().outputs(op)[0].getType());
        if (!variant)
          return error("variant-type");
        auto label = op->getAttrOfType<StringAttr>("alternative").getValue();
        unsigned offset = 0;
        bool found = false;
        for (auto arm : variant.getAlternatives()) {
          if (arm.getLabel().getValue() == label) {
            found = true;
            break;
          }
          offset += arm.getPayload().size();
        }
        if (!found)
          return error("variant-alternative");
        for (auto [i, value] : enumerate(flow().inputs(op)))
          if (auto e =
                  payload(value, layouts.child(*container, offset + i), true))
            return e;
      } else if (isa<zkc::exec::TestOp, zkc::exec::MatchOp, zkc::exec::RangeOp>(
                     op)) {
        bool loop = isa<zkc::exec::RangeOp>(op);
        bool match = isa<zkc::exec::MatchOp>(op);
        unsigned offset = loop ? 2 : 1;
        unsigned payloadOffset = 0;
        for (auto *entry : flow().get(op).bodies) {
          const auto &body = flow().body(entry);
          ArrayRef<Value> args = body.arguments;
          unsigned prefix =
              loop ? 1 : args.size() - (flow().inputs(op).size() - 1);
          if (match) {
            auto container = layouts.get(flow().inputs(op)[0]);
            if (!container)
              return container.takeError();
            for (unsigned i = 0; i < prefix; ++i)
              if (auto e = payload(args[i],
                                   layouts.child(*container, payloadOffset++),
                                   false))
                return e;
          }
          for (auto [argument, captured] :
               zip(args.drop_front(prefix),
                   flow().inputs(op).drop_front(offset)))
            if (auto e = equate(argument, captured))
              return e;
          auto *end = body.instructions.back();
          if (!isa<zkc::exec::RejectOp>(end)) {
            unsigned skip = loop && flow().get(op).step->conditional;
            for (auto [result, yielded] :
                 zip(flow().outputs(op), flow().inputs(end).drop_front(skip)))
              if (aggregate(result.getType()))
                if (auto e = equate(result, yielded))
                  return e;
          }
        }
        if (loop)
          for (auto [result, initial] :
               zip(flow().outputs(op), flow().inputs(op).drop_front(2)))
            if (auto e = equate(result, initial))
              return e;
        if (!loop)
          for (auto [resultIndex, result] : enumerate(flow().outputs(op)))
            if (!aggregate(result.getType())) {
              auto target = layouts.get(result);
              if (!target)
                return target.takeError();
              SmallVector<AggregateLayouts::Id> sources;
              for (auto *entry : flow().get(op).bodies) {
                auto *end = flow().body(entry).instructions.back();
                if (!isa<zkc::exec::RejectOp>(end)) {
                  auto source = layouts.get(flow().inputs(end)[resultIndex]);
                  if (!source)
                    return source.takeError();
                  sources.push_back(*source);
                }
              }
              if (auto e = layouts.join(*target, std::move(sources)))
                return e;
            }
      } else if (isa<zkc::exec::ReturnOp, zkc::exec::CompleteOp,
                     zkc::protocol_ir::FinishOp>(op)) {
        auto type =
            plan.operations[indices.lookup(op->getParentOp())].functionType;
        for (auto [value, target] : zip(flow().inputs(op), type.getResults()))
          if (flow().callers(op->getParentOp()).empty() &&
              aggregate(value.getType()))
            if (auto e = pin(value, target, index))
              return e;
      } else {
        for (auto [value, type] : zip(flow().outputs(op), d.outputs))
          if (auto e = pin(value, type, index))
            return e;
      }
    }
    std::set<std::tuple<std::string, std::string, unsigned>> seeds;
    for (const auto &seed : valueLayouts) {
      if (!seeds.emplace(seed.function, seed.site, seed.result).second)
        return error("binding-duplicate-selection");
      Operation *found = nullptr;
      for (auto *op : operations) {
        auto function = op->getParentOfType<func::FuncOp>();
        auto site = op->getAttrOfType<StringAttr>("site");
        if (flow().get(op).step && function &&
            function.getSymName() == seed.function && site &&
            site.getValue() == seed.site) {
          if (found)
            return error("binding-duplicate-selection");
          found = op;
        }
      }
      if (!found || seed.result >= flow().outputs(found).size())
        return error("binding-unknown-selection");
      Type type = seed.physicalType;
      if (logicalValueType(type) !=
          flow().outputs(found)[seed.result].getType())
        return error("binding-operation-signature");
      if (auto e = pin(flow().outputs(found)[seed.result], type,
                       indices.lookup(found)))
        return e;
      hints[flow().outputs(found)[seed.result]] = type;
    }
    if (auto e = layouts.solve())
      return e;
    for (auto *op : operations)
      for (auto result : flow().outputs(op))
        if (aggregate(result.getType()) ||
            isa<zkc::exec::TestOp, zkc::exec::MatchOp>(op)) {
          locate(failureLocation, op);
          auto id = layouts.get(result);
          if (!id)
            return id.takeError();
          auto type = layouts.physical(*id);
          if (!type)
            return type.takeError();
          hints[result] = *type;
        }
    return Error::success();
  }

  Error ports(PhysicalPlan &plan) {
    // Temporary unresolved slots are logical types, never published. Every
    // final slot is independently admitted as an exact complete physical type.
    auto initial = [&](Type type) -> Type {
      auto selected = defaultPort(type);
      if (selected)
        return *selected;
      consumeError(selected.takeError());
      return type;
    };
    SmallVector<NativeBindingApplication> applications(operations.size());
    llvm::DenseMap<Value, Type> hints;
    std::deque<Operation *> pending;
    llvm::DenseSet<Operation *> queued;
    auto enqueue = [&](Operation *op) {
      if (op && queued.insert(op).second)
        pending.push_back(op);
    };
    auto notify = [&](Value value) {
      for (auto use : flow().uses(value))
        enqueue(use.operation);
    };
    auto assign = [&](Value value, Type type) {
      if (valuePort(value, plan, indices, flow()) == type)
        return;
      const auto &definition = flow().definition(value);
      auto &owner = plan.operations[indices.lookup(definition.owner)];
      if (definition.argument)
        owner.blockArguments[definition.block][definition.port] = type;
      else
        owner.outputs[definition.port] = type;
      notify(value);
    };
    auto aggregate = [&](Type type) {
      auto kind = planTypeConstructor(type);
      return kind == "sequence" || kind == "variant" || kind == "field_array" ||
             kind == "fixed_vector";
    };
    for (auto [index, op] : enumerate(operations)) {
      auto &d = plan.operations[index];
      for (auto *entry : flow().get(op).bodies) {
        const auto &body = flow().body(entry);
        if (body.owner != op)
          continue;
        SmallVector<Type> args;
        for (Value value : body.arguments)
          args.push_back(initial(value.getType()));
        d.blockArguments.push_back(std::move(args));
      }
      if (auto signature = flow().get(op).callable) {
        if (flow().callers(op).empty()) {
          auto selected = selectedFunctionType(op, signature, functionPorts);
          if (!selected)
            return selected.takeError();
          d.functionType = *selected;
        } else {
          // A closed control body's ports follow its owning occurrence. An
          // inactive variant payload can have no default representation; keep
          // its provisional slot until the complete variant layout is solved.
          SmallVector<Type> inputs, outputs;
          for (auto type : signature.getInputs())
            inputs.push_back(initial(type));
          for (auto type : signature.getResults())
            outputs.push_back(initial(type));
          d.functionType =
              FunctionType::get(module.getContext(), inputs, outputs);
        }
        if (!d.blockArguments.empty())
          d.blockArguments[0].assign(d.functionType.getInputs().begin(),
                                     d.functionType.getInputs().end());
      }
      if (d.binding) {
        applications[index] = plan.bindings[*d.binding].binding.application;
        auto initialApplication = applications[index];
        auto descriptor = installedImplementations().find(
            initialApplication.contract, initialApplication.implementation);
        bool deferred =
            descriptor &&
            descriptor->family != ImplementationDescriptor::Family::Exact &&
            !initialApplication.valueType;
        auto signature = resolveNativeApplication(initialApplication, true);
        if (!signature) {
          if (!deferred)
            return signature.takeError();
          consumeError(signature.takeError());
          for (auto type : flow().outputs(op).getTypes())
            d.outputs.push_back(initial(type));
          for (auto type : flow().inputs(op).getTypes())
            d.inputs.push_back(initial(type));
        } else {
          d.inputs.assign(signature->getInputs().begin(),
                          signature->getInputs().end());
          d.outputs.assign(signature->getResults().begin(),
                           signature->getResults().end());
        }
      } else
        for (auto type : flow().outputs(op).getTypes())
          d.outputs.push_back(initial(type));
      enqueue(op);
    }
    if (auto e = aggregatePorts(plan, hints))
      return e;
    while (!pending.empty()) {
      if (!selection.numerical.chargeCatalog())
        return error("finite-analysis-limit");
      auto *op = pending.front();
      pending.pop_front();
      queued.erase(op);
      locate(failureLocation, op);
      auto index = indices.lookup(op);
      auto &d = plan.operations[index];
      if (auto call = dyn_cast<zkc::protocol_ir::LocalCallOp>(op)) {
        auto *callee =
            SymbolTable::lookupNearestSymbolFrom(op, call.getCalleeAttr());
        auto type = plan.operations[indices.lookup(callee)].functionType;
        d.inputs.assign(type.getInputs().begin(), type.getInputs().end());
        for (auto [result, target] : zip(flow().outputs(op), type.getResults()))
          assign(result, target);
        continue;
      }
      if (d.binding) {
        auto app = applications[index];
        auto descriptor =
            installedImplementations().find(app.contract, app.implementation);
        if (descriptor && descriptor->family ==
                              ImplementationDescriptor::Family::Observation) {
          auto payload =
              operationContracts(app.contract)->observation->payloadInput;
          Type layout;
          if (!app.valueType) {
            layout =
                valuePort(flow().inputs(op)[payload], plan, indices, flow());
            if (!isa<runtime::RepresentedType>(layout))
              continue;
          }
          auto signature = resolveNativeApplication(app, true, layout);
          if (!signature)
            return familyFailure(signature.takeError(), plan, index);
          d.inputs.assign(signature->getInputs().begin(),
                          signature->getInputs().end());
          for (auto [result, type] :
               zip(flow().outputs(op), signature->getResults()))
            assign(result, type);
          applications[index] = std::move(app);
          if (plan.bindings[*d.binding].binding.application.valueType ==
              FunctionType{})
            applications[index].valueType = {};
          continue;
        }
        if (descriptor &&
            descriptor->family != ImplementationDescriptor::Family::Exact) {
          Type container;
          StringRef kind =
              descriptor->family == ImplementationDescriptor::Family::Sequence
                  ? "sequence"
              : descriptor->family ==
                      ImplementationDescriptor::Family::FieldArray
                  ? "field_array"
                  : "fixed_vector";
          auto logicalSignature = resolveNativeApplication(app, false);
          if (!logicalSignature)
            return logicalSignature.takeError();
          Type containerLogical;
          for (auto ports :
               {logicalSignature->getInputs(), logicalSignature->getResults()})
            for (Type port : ports)
              if (!containerLogical && planTypeConstructor(port) == kind)
                containerLogical = port;
          if (!containerLogical)
            return error("binding-representation");
          for (auto result : flow().outputs(op))
            if (auto hint = hints.lookup(result)) {
              if (logicalValueType(hint) == containerLogical) {
                container = hint;
                break;
              }
              if (app.contract == "sequence.at") {
                auto formed = formPhysicalType(containerLogical,
                                               "logical.sequence/0", {hint});
                if (!formed)
                  return formed.takeError();
                container = *formed;
              }
            }
          // Actual container inputs determine access and append layouts.
          for (auto operand : flow().inputs(op)) {
            auto actual = valuePort(operand, plan, indices, flow());
            if (isa<runtime::RepresentedType>(actual) &&
                planTypeConstructor(actual) == kind) {
              if (!container)
                container = actual;
              break;
            }
          }
          if (!container)
            for (auto type : d.outputs)
              if (aggregate(type)) {
                container = type;
                break;
              }
          auto signature = resolveNativeApplication(
              app, true, app.valueType ? Type{} : container);
          if (!signature) {
            if (!container || !isa<zkc::runtime::RepresentedType>(container)) {
              consumeError(signature.takeError());
              continue;
            }
            return familyFailure(signature.takeError(), plan, index);
          }
          d.inputs.assign(signature->getInputs().begin(),
                          signature->getInputs().end());
          for (auto [result, type] :
               zip(flow().outputs(op), signature->getResults()))
            assign(result, type);
          applications[index] = std::move(app);
          // Recompute unconstrained source families when their inputs change.
          if (plan.bindings[*d.binding].binding.application.valueType ==
              FunctionType{})
            applications[index].valueType = {};
        }
        continue;
      }
      if (isa<zkc::exec::VariantOp>(op)) {
        auto logical =
            dyn_cast<data::VariantType>(flow().outputs(op)[0].getType());
        if (!logical)
          return error("variant-type");
        auto alternatives = logical.getAlternatives();
        auto label = op->getAttrOfType<StringAttr>("alternative").getValue();
        size_t start = 0;
        unsigned active = 0;
        for (; active < alternatives.size() &&
               alternatives[active].getLabel().getValue() != label;
             ++active)
          start += alternatives[active].getPayload().size();
        if (active == alternatives.size())
          return error("variant-alternative");
        Type selected = hints.lookup(flow().outputs(op)[0]);
        if (!selected) {
          auto schemas = planLogicalChildren(logical);
          if (!schemas)
            return schemas.takeError();
          SmallVector<Type> children;
          bool ready = true;
          for (auto [i, schema] : enumerate(*schemas)) {
            Type child;
            if (i >= start && i < start + flow().inputs(op).size()) {
              child = valuePort(flow().inputs(op)[i - start], plan, indices,
                                flow());
              if (!isa<runtime::RepresentedType>(child)) {
                ready = false;
                break;
              }
            } else {
              auto ordinary = defaultPort(schema);
              if (!ordinary) {
                consumeError(ordinary.takeError());
                ready = false;
                break;
              }
              child = *ordinary;
            }
            children.push_back(child);
          }
          if (!ready)
            continue;
          auto formed =
              formPhysicalType(logical, "logical.variant/0", children);
          if (!formed)
            return formed.takeError();
          selected = *formed;
        }
        assign(flow().outputs(op)[0], selected);
        auto payload = variantPorts(selected, active);
        if (!payload)
          return payload.takeError();
        d.inputs = *payload;
      } else if (isa<zkc::exec::TestOp, zkc::exec::MatchOp, zkc::exec::RangeOp>(
                     op)) {
        auto previousInputs = d.inputs;
        auto previousOutputs = d.outputs;
        bool loop = isa<zkc::exec::RangeOp>(op),
             match = isa<zkc::exec::MatchOp>(op);
        if (match && !isa<zkc::runtime::RepresentedType>(valuePort(
                         flow().inputs(op)[0], plan, indices, flow())))
          continue;
        unsigned offset = loop ? 2 : 1;
        d.inputs.clear();
        for (unsigned i = 0; i < offset; ++i)
          d.inputs.push_back(
              match ? valuePort(flow().inputs(op)[i], plan, indices, flow())
                    : initial(flow().inputs(op)[i].getType()));
        for (auto operand : flow().inputs(op).drop_front(offset))
          d.inputs.push_back(valuePort(operand, plan, indices, flow()));
        for (auto [resultIndex, result] : enumerate(flow().outputs(op))) {
          Type selected =
              loop ? d.inputs[2 + resultIndex] : hints.lookup(result);
          if (!selected) {
            for (auto *entry : flow().get(op).bodies) {
              auto *end = flow().body(entry).instructions.back();
              if (isa<zkc::exec::RejectOp>(end))
                continue;
              auto type = valuePort(flow().inputs(end)[resultIndex], plan,
                                    indices, flow());
              if (selected && selected != type) {
                selected = initial(result.getType());
                break;
              }
              selected = type;
            }
          }
          if (selected)
            assign(result, selected);
        }
        for (auto [regionIndex, entry] : enumerate(flow().get(op).bodies)) {
          const auto &body = flow().body(entry);
          SmallVector<Type> args;
          if (loop)
            args.push_back(d.inputs[0]);
          if (match) {
            auto payload = variantPorts(d.inputs[0], regionIndex);
            if (!payload)
              return payload.takeError();
            args = *payload;
          }
          append_range(args, ArrayRef(d.inputs).drop_front(offset));
          for (auto [arg, type] : zip(body.arguments, args))
            assign(arg, type);
          SmallVector<Type> results;
          if (loop && flow().get(op).step->conditional)
            results.push_back(
                initial(flow().get(body.owner).callable.getResult(0)));
          append_range(results, d.outputs);
          auto &callee = plan.operations[indices.lookup(body.owner)];
          auto signature =
              FunctionType::get(module.getContext(), args, results);
          if (callee.functionType != signature) {
            callee.functionType = signature;
            enqueue(body.instructions.back());
          }
        }
        if (d.inputs != previousInputs || d.outputs != previousOutputs)
          for (auto *entry : flow().get(op).bodies)
            enqueue(flow().body(entry).instructions.back());
      } else if (isa<zkc::exec::ReturnOp, zkc::exec::CompleteOp,
                     zkc::protocol_ir::FinishOp>(op)) {
        Operation *function = op->getParentOp();
        auto type = plan.operations[indices.lookup(function)].functionType;
        d.inputs.assign(type.getResults().begin(), type.getResults().end());
        for (auto *caller : flow().callers(function))
          enqueue(caller);
      } else if (isa<zkc::runtime::ReleaseBindingsOp>(op)) {
        d.inputs.clear();
        for (auto value : flow().inputs(op))
          d.inputs.push_back(valuePort(value, plan, indices, flow()));
      } else {
        d.inputs.clear();
        for (auto type : flow().inputs(op).getTypes())
          d.inputs.push_back(initial(type));
      }
    }
    for (auto [index, op] : enumerate(operations)) {
      auto &d = plan.operations[index];
      for (auto type : d.outputs) {
        if (auto e = checkPhysicalType(type))
          return e;
      }
      for (auto type : d.inputs) {
        if (auto e = checkPhysicalType(type))
          return e;
      }
      for (const auto &args : d.blockArguments)
        for (auto type : args) {
          if (auto e = checkPhysicalType(type))
            return e;
        }
    }
    // Resolve exact specialization declarations after equations have settled.
    std::set<std::string> used = symbols;
    unsigned next = 0;
    for (auto [index, op] : enumerate(operations)) {
      auto &d = plan.operations[index];
      if (!d.binding)
        continue;
      auto app = applications[index];
      app.valueType =
          FunctionType::get(module.getContext(), d.inputs, d.outputs);
      auto signature = resolveNativeApplication(app);
      if (!signature)
        return signature.takeError();
      applications[index] = std::move(app);
    }
    // An unused declaration still needs a complete installed native layout.
    // If no default exists, a reached application can supply its exact family
    // layout; the installation resolver independently admits it below.
    for (auto [origin, binding] : enumerate(plan.bindings))
      if (!binding.binding.application.valueType) {
        auto signature = resolveNativeApplication(binding.binding.application);
        if (!signature) {
          bool found = false;
          for (auto [index, decision] : enumerate(plan.operations))
            if (decision.binding == origin && applications[index].valueType) {
              consumeError(signature.takeError());
              binding.binding.application.valueType =
                  applications[index].valueType;
              found = true;
              break;
            }
          if (!found)
            return signature.takeError();
        } else
          binding.binding.application.valueType = *signature;
      }
    for (auto [index, op] : enumerate(operations)) {
      auto &d = plan.operations[index];
      if (!d.binding)
        continue;
      auto origin = *d.binding;
      auto app = applications[index];
      if (sameApplication(app, plan.bindings[origin].binding.application))
        continue;
      BindingIndex binding = plan.bindings.size();
      for (auto [i, candidate] : enumerate(plan.bindings))
        if (candidate.purpose == BindingPurpose::Specialization &&
            candidate.origin == origin &&
            sameApplication(candidate.binding.application, app)) {
          binding = i;
          break;
        }
      if (binding == plan.bindings.size()) {
        if (binding >= 4096) {
          if (auto e = capacityFailure(plan, {index}))
            return e;
          return error("binding-declaration-limit");
        }
        auto specialized = plan.bindings[origin];
        specialized.binding.name = fresh(used, "specialized_", next);
        specialized.binding.application = std::move(app);
        specialized.purpose = BindingPurpose::Specialization;
        specialized.origin = origin;
        specialized.declaration.reset();
        specialized.location = index;
        plan.bindings.push_back(std::move(specialized));
      }
      d.binding = binding;
    }
    return Error::success();
  }

public:
  Proposer(ModuleOp module, const CandidateCatalog &catalog,
           Location *failureLocation, PhysicalSelection &selection,
           ArrayRef<NativeFunctionPortSelection> functionPorts,
           ArrayRef<NativeValueLayoutSelection> valueLayouts)
      : module(module), root(cast<zkc::protocol_ir::ProtocolModuleOp>(
                            &module.getBody()->front())),
        catalog(catalog), operations(physicalPlanOperations(module)),
        indices(indexOperations(operations)), failureLocation(failureLocation),
        selection(selection), functionPorts(functionPorts),
        valueLayouts(valueLayouts) {}

  Error capacityFailure(const PhysicalPlan &plan,
                        ArrayRef<OperationIndex> affected) {
    auto &failure = selection.failure;
    failure = {};
    failure.kind = PhysicalFailureKind::OptionalProgramCapacity;
    failure.operations.assign(affected.begin(), affected.end());
    // Declaration and escaped-carrier limits concern the complete plan.
    // Decline optional provider choices together instead of reconstructing
    // provenance through scalar joins and aggregate layout equations. Fixed
    // bindings have no cursor; numerical retry retains the reported slice.
    for (auto [index, binding] : enumerate(plan.bindings)) {
      if (!selection.numerical.chargeCatalog())
        return error("finite-analysis-limit");
      if (!binding.fixed && !binding.origin)
        failure.bindings.push_back(index);
    }
    return Error::success();
  }

  Error initialize(ArrayRef<std::pair<std::string, std::string>> requests,
                   bool contractions) {
    auto admitted = ExecutionPorts::read(module);
    if (!admitted)
      return admitted.takeError();
    execution = std::move(*admitted);
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
      if (!isa<zkc::runtime::BindingOp>(op))
        continue;
      auto binding = readPlanBinding(cast<runtime::BindingOp>(&op));
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
      auto facts = [&](Operation *op) -> const OperationContracts * {
        auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
        if (!reference)
          return nullptr;
        auto found = names.find(reference.getValue().str());
        return found == names.end()
                   ? nullptr
                   : operationContracts(
                         originals[found->second].binding.application.contract);
      };
      LinearContractionStats ignored;
      eligible = findExecutionContractions(flow(), operations, indices, facts,
                                           ignored);
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
      } else if (flow().get(op).step && !interfaceOperation(op))
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
          if (auto e = selection.cpuTarget.checkNativeApplication(candidate)) {
            consumeError(std::move(e));
            continue;
          }
          candidate.valueType = *installed;
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
      if (auto function = op->getParentOfType<func::FuncOp>())
        if (auto site = op->getAttrOfType<StringAttr>("site"))
          sites[function].insert(site.getValue().str());
    for (auto [index, op] : enumerate(operations)) {
      locate(failureLocation, op);
      auto &decision = plan.operations[index];
      for (auto [operand, value] : enumerate(flow().inputs(op))) {
        Type from = valuePort(value, plan, indices, flow());
        Type to = decision.inputs[operand];
        if (from == to)
          continue;
        auto application = chooseConversion(
            from, to, catalog, selection.numerical, selection.cpuTarget);
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
          Operation *producer = flow().definition(value).owner;
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
          NativeBindingChoice declaration{fresh(used, "layout_", next),
                                          std::move(*application)};
          plan.bindings.push_back({std::move(declaration),
                                   BindingPurpose::Conversion,
                                   {},
                                   false,
                                   index});
        }
        auto function = op->getParentOfType<func::FuncOp>();
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
  llvm::TimeTraceScope timing("zkc.physical-proposal");
  locate(failureLocation, module);
  if (failed(zkc::admitStage(module)) || module.getBody()->empty() ||
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
  llvm::DenseSet<Operation *> fixedFiniteBindings;
  for (auto declaration :
       root.getBody().front().getOps<zkc::runtime::BindingOp>()) {
    locate(failureLocation, declaration);
    auto binding = readPlanBinding(declaration);
    if (!binding)
      return binding.takeError();
    originalPins.emplace(binding->name, binding->application.implementation);
    auto found = requests.find(binding->name);
    if (found == requests.end())
      continue;
    auto fixed = selectImplementation(binding->application, found->second,
                                      options.cpuTarget);
    if (!fixed)
      return fixed.takeError();
    fixedFiniteBindings.insert(declaration);
    requests.erase(found);
  }
  if (!requests.empty())
    return error("binding-unknown-selection");
  SmallVector<NativeFunctionPortSelection> functionPorts;
  SmallVector<NativeValueLayoutSelection> valueLayouts;
  for (const auto &choice : options.functionPorts) {
    auto bound = parseBoundType(choice.physicalType, true);
    if (!bound)
      return bound.takeError();
    auto type = decodeBoundType(module.getContext(), *bound);
    if (!type)
      return error("binding-type-identity");
    functionPorts.push_back(
        {choice.function, choice.output, choice.port, type});
  }
  for (const auto &choice : options.valueLayouts) {
    auto bound = parseBoundType(choice.physicalType, true);
    if (!bound)
      return bound.takeError();
    auto type = decodeBoundType(module.getContext(), *bound);
    if (!type)
      return error("binding-type-identity");
    valueLayouts.push_back({choice.function, choice.site, choice.result, type});
  }
  auto input = std::make_shared<InputSnapshot>(
      InputSnapshot{module,
                    structure(module),
                    identities(module),
                    protocol::Assignments(selections.begin(), selections.end()),
                    options.linearContractions,
                    options.numericalPolicy,
                    std::move(functionPorts),
                    std::move(valueLayouts),
                    options.cpuTarget,
                    {},
                    {}});
  for (const auto &choice : options.functionPorts) {
    bool found = false;
    for (auto &op : root.getBody().front())
      if ((isa<func::FuncOp>(op) &&
           isScopedExecutionFunction(cast<func::FuncOp>(op)) &&
           !op.hasAttr("runtime.region")) ||
          isa<zkc::protocol_ir::ParticipantOp>(op))
        found |= op.getAttrOfType<StringAttr>("sym_name").getValue() ==
                 choice.function;
    if (!found)
      return error("binding-unknown-selection");
  }
  bool hasNumerical = false, hasFinite = false;
  root.walk([&](Operation *op) {
    hasNumerical |= (mathematical::isComputationUnit(op) ||
                     isa<exec::ComputeOp, data::DomainOp>(op) ||
                     (isa<func::FuncOp>(op) &&
                      !isScopedExecutionFunction(cast<func::FuncOp>(op))));
    hasFinite |= isa<exec::FoldOp, exec::CollectOp>(op);
  });
  hasNumerical |= hasFinite;
  PhysicalSelection selection;
  selection.cpuTarget = options.cpuTarget;
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
  bool firstAttempt = true, requiredEndpoint = false;
  for (;;) {
    auto incomingCopy = selection.numerical.remainingCopy;
    auto incomingBytes = selection.numerical.remainingSiteBytes;
    selection.numerical.allowSpeculation(true);
    mathematical::RecipeConstructionWork construction(selection.numerical.work);
    bool speculative =
        hasNumerical && !requiredEndpoint &&
        selection.numerical.canSpeculate() &&
        (selection.numerical.hasAlternatives() || firstAttempt) &&
        construction.canDiscard(selection.numerical.work);
    firstAttempt = false;
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
    selection.numerical.beginAttempt();
    OwningOpRef<ModuleOp> candidate;
    auto clearOrigins =
        llvm::scope_exit([&] { selection.numerical.origins.clear(); });
    ModuleOp selected = module;
    Error refusal = Error::success();
    std::optional<mathematical::RealizationSubject> capacitySubject;
    mathematical::VerificationDecision numericalOutcome;
    bool constructionCapacity = false;
    OwningOpRef<ModuleOp> prepared;
    ModuleOp numericalSource = module;
    OwningOpRef<ModuleOp> finite;
    std::optional<CapacityCause> preparationCapacity;
    mathematical::VerificationDecision preparationOutcome;
    auto prepare = [&]() -> Error {
      if (hasFinite) {
        finite = protocol::prepareScopedFinite(
            module, selection.numerical.work, selection.numerical.remainingCopy,
            selection.numerical.remainingSiteBytes, preparationCapacity,
            options.numericalPolicy, &fixedFiniteBindings, &selection.numerical,
            &preparationOutcome);
        if (!finite)
          return error("computation-realization", "finite preparation refused");
        numericalSource = *finite;
      }
      if (hasNumerical) {
        prepared = computation::prepareComputationRealization(
            numericalSource, &selection.numerical.remainingCopy,
            &preparationCapacity, &selection.numerical);
        if (!prepared)
          return error("computation-realization",
                       "numerical source preparation");
        // Checked mathematical normalization does not consult executable
        // binding choices. Apply requests to its owned result before any
        // replacement discovery, rather than cloning the complete source just
        // to pin it.
        auto preparedRoot = cast<zkc::protocol_ir::ProtocolModuleOp>(
            prepared->getBody()->front());
        for (auto declaration :
             preparedRoot.getBody().front().getOps<zkc::runtime::BindingOp>())
          for (const auto &[name, implementation] : selections)
            if (declaration.getSymName() == name)
              declaration.setImplementation(implementation);
        // Discover the current immutable prepared closure. Invocation
        // identities remain stable when another finite recipe changes the call
        // count.
        if (failed(computation::discoverComputations(
                *prepared, options.numericalPolicy, selection.numerical)))
          return error("computation-realization",
                       "numerical occurrence discovery");
      }
      return Error::success();
    };
    SmallVector<Diagnostic> preparationDiagnostics;
    if (speculative) {
      zkc::diagnostics::ScopedThreadDiagnosticHandler quiet(
          module.getContext(), [&](Diagnostic &d) {
            preparationDiagnostics.push_back(std::move(d));
            return success();
          });
      refusal = prepare();
    } else
      refusal = prepare();
    bool preparationCheckingCapacity =
        preparationOutcome.outcome ==
        mathematical::VerificationObservation::OptionalCapacity;
    if (refusal && !preparationCapacity && !preparationCheckingCapacity) {
      // Optional attempts stay quiet while ordered preparation can recover.
      // A terminal failure must retain its diagnostic instead of replacing
      // the cause with the enclosing preparation-stage error.
      for (auto &diagnostic : preparationDiagnostics)
        module.getContext()->getDiagEngine().emit(std::move(diagnostic));
      return refusal;
    }
    if (refusal)
      constructionCapacity = speculative;
    if (!refusal && hasNumerical) {
      // Preparation already owns a private checked candidate. Discovery stores
      // owned formula bodies and transient occurrence associations; neither the
      // caller's source nor an independent reader borrows this proposal. Move
      // it into materialization without a second whole-context snapshot. The
      // original numericalSource remains the correspondence authority.
      candidate = std::move(prepared);
      selected = *candidate;
      if (failed(computation::materializeComputations(
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
          return error("computation-realization", numericalOutcome.detail);
        refusal = error("finite-analysis-limit");
      }
      auto candidateRoot =
          cast<zkc::protocol_ir::ProtocolModuleOp>(selected.getBody()->front());
      // Replacement saw fixed requests. Retained declarations keep their
      // original attributes; physical choices carry the requested pins.
      for (auto declaration :
           candidateRoot.getBody().front().getOps<zkc::runtime::BindingOp>()) {
        auto original = originalPins.find(declaration.getSymName().str());
        if (original != originalPins.end())
          declaration.setImplementation(original->second);
      }
      if (!refusal && failed(zkc::admitStage(selected)))
        return error("binding-operation");
    }
    if (auto e = input->check(module))
      return e;
    selection.failure = {};
    selection.bindingCursors.clear();
    PhysicalPlan plan;
    Proposer proposer(selected, catalog, failureLocation, selection,
                      input->functionPorts, input->valueLayouts);
    if (!refusal)
      refusal = proposer.initialize(selections, options.linearContractions);
    size_t groupLimit = 4096;
    while (!refusal) {
      refusal = proposer.populate(plan, groupLimit);
      if (refusal || plan.bindings.size() <= 4096)
        break;
      if (plan.contractions.empty()) {
        SmallVector<OperationIndex> conversions;
        for (const auto &operation : plan.operations)
          if (!operation.conversions.empty())
            conversions.push_back(operation.operation);
        refusal = proposer.capacityFailure(plan, conversions);
        if (!refusal)
          refusal = error("binding-declaration-limit");
        break;
      }
      groupLimit = plan.contractions.size() - 1;
    }
    if (!refusal)
      refusal =
          checkTargetPlan(selected, plan, options.cpuTarget, failureLocation);
    if (!refusal && options.releaseStorage) {
      auto releases =
          proposeStorage(selected, plan.operations, failureLocation);
      if (!releases)
        refusal = releases.takeError();
      else
        plan.releases = std::move(*releases);
    }
    if (!refusal && options.programCapacity) {
      if (!computation::chargeCopy(selected,
                                   selection.numerical.remainingCopy)) {
        constructionCapacity = speculative;
        refusal = error("computation-realization");
      } else {
        OwningOpRef<ModuleOp> preflight(cast<ModuleOp>(selected->clone()));
        auto capacity = options.programCapacity(*preflight, plan);
        if (!capacity)
          refusal = capacity.takeError();
        else if (!capacity->empty()) {
          refusal = proposer.capacityFailure(plan, *capacity);
          if (!refusal)
            refusal = error("source-limit");
        }
      }
    }
    if (!refusal && hasNumerical &&
        failed(mathematical::verifyNumericalLowering(
            numericalSource, selected, options.numericalPolicy, selections,
            &selection.numerical.work, &numericalOutcome))) {
      if (numericalOutcome.outcome !=
          mathematical::VerificationObservation::OptionalCapacity)
        return error("numerical-lowering-correspondence",
                     numericalOutcome.detail);
      capacitySubject = numericalOutcome.subject;
      refusal = error("mathematical-analysis-limit");
    }
    if (!refusal) {
      if (auto e = input->check(module))
        return e;
      selection.numerical.origins.clear();
      input->finite = std::move(finite);
      input->numerical = std::move(candidate);
      plan.input = input;
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
    if (!*advanced && constructionCapacity && speculative) {
      // Construction can stop before discovery reaches any occurrence. The
      // single required endpoint disables optional recipes and consumes the
      // preserved ordinary reserve; it is not an unbounded repeated attempt.
      requiredEndpoint = true;
      *advanced = true;
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
Error checkFixed(const NativeBindingApplication &source,
                 const NativeBindingApplication &selected,
                 std::optional<StringRef> request, bool recordedFixed) {
  if (!sameLogical(source, selected) ||
      (source.valueType && source.valueType != selected.valueType))
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
Error checkLogicalPorts(TypeRange logical, ArrayRef<Type> recorded) {
  if (logical.size() != recorded.size())
    return error("binding-operation-signature");
  for (auto [source, type] : zip(logical, recorded)) {
    if (!type)
      return error("binding-operation-signature");
    if (auto e = checkPhysicalType(type))
      return e;
    if (logicalValueType(type) != source)
      return error("binding-operation-signature");
  }
  return Error::success();
}
Error checkInstalledPorts(TypeRange recorded, TypeRange installed) {
  if (recorded.size() != installed.size())
    return error("binding-operation-signature");
  for (auto [type, expected] : zip(recorded, installed)) {
    if (!type)
      return error("binding-operation-signature");
    if (auto e = checkPhysicalType(type))
      return e;
    if (type != expected)
      return error("binding-operation-signature");
  }
  return Error::success();
}

// This traversal checks all *actual* SSA operand uses. It neither calls the
// opportunity finder nor enumerates uses supplied by a proposed group.
Expected<SmallVector<OperationIndex>>
checkAllUses(Operation *op, const PhysicalPlan &plan, const Indices &indices,
             const ExecutionPorts &flow, Location *failureLocation) {
  locate(failureLocation, op);
  const auto &decision = plan.operations[indices.lookup(op)];
  if (!flow.get(op).step || !decision.binding || !flow.enclosingBody(op))
    return error("binding-contraction");
  const auto &application =
      plan.bindings[*decision.binding].binding.application;
  auto installed = resolveNativeApplication(application, true);
  if (!installed)
    return installed.takeError();
  const auto *facts = operationContracts(application.contract);
  if (!facts || !facts->diagonalMap)
    return error("binding-contraction");
  const auto &production = *facts->diagonalMap;
  auto inputs = flow.inputs(op), outputs = flow.outputs(op);
  if (production.result >= outputs.size() ||
      production.factorsOperand >= inputs.size() ||
      production.valuesOperand >= inputs.size() ||
      production.factorsOperand == production.valuesOperand)
    return error("binding-contraction");
  const auto &view = installed->getResult(production.result);
  auto result = outputs[production.result];
  if (!isDiagonalRepresentation(
          cast<runtime::RepresentedType>(view).getRepresentation()) ||
      flow.uses(result).empty() ||
      inputs[production.valuesOperand].getType() != result.getType())
    return error("binding-contraction");
  // The actual semantic body order, not administrative CFG block adjacency,
  // controls lifetime. Every actual data use must occupy a contraction slot.
  const auto &body = flow.body(flow.enclosingBody(op)).instructions;
  auto producerPosition = llvm::find(body, op);
  SmallVector<OperationIndex> consumers;
  for (auto use : flow.uses(result)) {
    auto *user = use.operation;
    locate(failureLocation, user);
    if (flow.enclosingBody(user) != flow.enclosingBody(op) ||
        llvm::find(body, user) <= producerPosition)
      return error("binding-contraction");
    auto index = indices.lookup(user);
    const auto &selected = plan.operations[index];
    if (!selected.binding ||
        selected.inputs[use.operand] != decision.outputs[production.result])
      return error("binding-contraction");
    const auto &consumerApplication =
        plan.bindings[*selected.binding].binding.application;
    auto consumerInstalled =
        resolveNativeApplication(consumerApplication, true);
    if (!consumerInstalled)
      return consumerInstalled.takeError();
    const auto *consumerFacts =
        operationContracts(consumerApplication.contract);
    if (!consumerFacts || !consumerFacts->linearContraction)
      return error("binding-contraction");
    const auto &roles = *consumerFacts->linearContraction;
    auto consumed = flow.inputs(user);
    if (use.operand != roles.valuesOperand ||
        roles.coefficientsOperand >= consumed.size() ||
        roles.coefficientsOperand == roles.valuesOperand ||
        consumed[roles.coefficientsOperand].getType() !=
            inputs[production.factorsOperand].getType() ||
        !(consumerInstalled->getInput(roles.valuesOperand) == view))
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
  if (!plan.input)
    return error("binding-stale-selection");
  if (auto e = plan.input->check(module))
    return e;
  // Check the original numerical-bearing source independently against the exact
  // retained executable payload, before checking any installed physical
  // choices. This reader does not emit or select numerical recipes.
  if (failed(zkc::admitStage(module)))
    return error("binding-operation");
  ModuleOp selected = module;
  ModuleOp numericalSource = module;
  mathematical::RealizationWork numericalChecking;
  if (plan.input->finite) {
    llvm::DenseSet<Operation *> fixedFiniteBindings;
    auto sourceOwner =
        cast<zkc::protocol_ir::ProtocolModuleOp>(module.getBody()->front());
    for (const auto &[name, implementation] : plan.input->selections) {
      auto binding = dyn_cast_or_null<runtime::BindingOp>(
          SymbolTable::lookupSymbolIn(sourceOwner, name));
      if (!binding)
        return error("binding-unknown-selection");
      auto decoded = readPlanBinding(binding);
      if (!decoded)
        return decoded.takeError();
      auto fixed = selectImplementation(decoded->application, implementation,
                                        plan.input->cpuTarget);
      if (!fixed)
        return fixed.takeError();
      fixedFiniteBindings.insert(binding);
    }
    if (failed(protocol::verifyScopedFinitePreparation(
            module, *plan.input->finite, numericalChecking,
            plan.input->numericalPolicy, nullptr, &fixedFiniteBindings)))
      return error("numerical-lowering-correspondence",
                   "finite preparation differs");
    numericalSource = *plan.input->finite;
  }
  if (plan.input->numerical) {
    selected = *plan.input->numerical;
    if (failed(mathematical::verifyNumericalLowering(
            numericalSource, selected, plan.input->numericalPolicy,
            plan.input->selections, &numericalChecking)))
      return error("numerical-lowering-correspondence");
  }
  auto root =
      cast<zkc::protocol_ir::ProtocolModuleOp>(&selected.getBody()->front());
  auto admitted = ExecutionPorts::read(selected);
  if (!admitted)
    return admitted.takeError();
  const auto &flow = *admitted;
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
  for (const auto &[key, implementation] : plan.input->selections)
    if (!requests.emplace(key, implementation).second)
      return error("binding-duplicate-selection");
  std::set<std::string> symbols;
  for (auto &op : root.getBody().front())
    if (!isa<zkc::runtime::BindingOp>(op))
      if (auto name = op.getAttrOfType<StringAttr>("sym_name"))
        symbols.insert(name.getValue().str());
  std::map<std::string, BindingIndex> originals;
  size_t declarationIndex = 0;
  for (auto declaration :
       root.getBody().front().getOps<zkc::runtime::BindingOp>()) {
    locate(failureLocation, declaration);
    if (declarationIndex >= plan.bindings.size())
      return error("binding-plan-coverage");
    const auto &decision = plan.bindings[declarationIndex];
    auto source = readPlanBinding(declaration);
    if (!source)
      return source.takeError();
    if (decision.purpose != BindingPurpose::Original ||
        decision.declaration != indices.lookup(declaration) ||
        decision.binding.name != source->name ||
        decision.location != indices.lookup(declaration) || decision.origin)
      return error("binding-plan-coverage");
    auto request = requests.find(source->name);
    if (auto e = checkFixed(source->application, decision.binding.application,
                            request == requests.end()
                                ? std::nullopt
                                : std::optional<StringRef>(request->second),
                            decision.fixed))
      return e;
    if (!decision.fixed) {
      auto descriptor = installedImplementations().find(
          decision.binding.application.contract,
          decision.binding.application.implementation);
      if (descriptor && descriptor->requiresExplicitSelection)
        return error("binding-implementation");
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
         (decision.fixed &&
          decision.purpose != BindingPurpose::Specialization)))
      return error("binding-plan-coverage");
    if (decision.purpose != BindingPurpose::Specialization && decision.origin)
      return error("binding-plan-coverage");
    if (!symbols.insert(decision.binding.name).second)
      return error("binding-plan-coverage");
    StringRef name = decision.binding.name;
    if (name.empty() || name.size() > 256 ||
        !(isAlpha(name.front()) || name.front() == '_') ||
        !all_of(name, [](char c) {
          return isAlnum(c) || c == '_' || c == '.' || c == '-';
        }))
      return error("binding-name");
    if (!decision.binding.application.valueType)
      return error("binding-signature");
    auto installed = resolveNativeApplication(decision.binding.application);
    if (!installed)
      return installed.takeError();
  }

  // Check complete definition and use signatures before consulting any ports
  // by SSA index. This makes malformed proposal vectors ordinary refusals.
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.inputs.size() != flow.inputs(op).size() ||
        decision.outputs.size() != flow.outputs(op).size())
      return error("binding-operation-signature");
    size_t blockIndex = 0;
    for (auto *entry : flow.get(op).bodies) {
      const auto &body = flow.body(entry);
      if (body.owner != op)
        continue;
      if (blockIndex >= decision.blockArguments.size())
        return error("binding-operation-signature");
      if (auto e = checkLogicalPorts(ValueRange(body.arguments).getTypes(),
                                     decision.blockArguments[blockIndex++]))
        return e;
    }
    if (blockIndex != decision.blockArguments.size())
      return error("binding-operation-signature");
    if (auto signature = flow.get(op).callable) {
      if (!decision.functionType)
        return error("binding-operation-signature");
      if (auto e = checkLogicalPorts(signature.getInputs(),
                                     decision.functionType.getInputs()))
        return e;
      if (auto e = checkLogicalPorts(signature.getResults(),
                                     decision.functionType.getResults()))
        return e;
      if (flow.callers(op).empty()) {
        auto expected =
            selectedFunctionType(op, signature, plan.input->functionPorts);
        if (!expected)
          return expected.takeError();
        if (decision.functionType != *expected)
          return error("binding-operation-signature");
      }
      if (decision.blockArguments.size() != 1 ||
          TypeRange(decision.blockArguments[0]) !=
              decision.functionType.getInputs())
        return error("binding-operation-signature");
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
      // The admitted source owns exact invocation ports and parameters.
      if (!isa<zkc::exec::ApplyOp>(op))
        return error("binding-operation");
      if (!sameLogical(binding.binding.application, base.binding.application))
        return error("binding-operation");
      if (binding.purpose == BindingPurpose::Specialization) {
        auto descriptor = installedImplementations().find(
            binding.binding.application.contract,
            binding.binding.application.implementation);
        if (binding.origin != original->second || binding.fixed != base.fixed ||
            !descriptor ||
            descriptor->family == ImplementationDescriptor::Family::Exact ||
            binding.binding.application.implementation !=
                base.binding.application.implementation)
          return error("binding-selection-conflict");
      } else if (*decision.binding != original->second &&
                 (binding.purpose != BindingPurpose::Contraction || base.fixed))
        return error(base.fixed ? "binding-selection-conflict"
                                : "binding-plan-coverage");
      if (binding.purpose == BindingPurpose::Contraction &&
          !is_contained(
              catalog.diagonalImplementations(base.binding.application),
              binding.binding.application.implementation))
        return error("binding-implementation");
      auto installed =
          resolveNativeApplication(binding.binding.application, true);
      if (!installed)
        return installed.takeError();
      if (auto e = checkInstalledPorts(decision.inputs, installed->getInputs()))
        return e;
      if (auto e =
              checkInstalledPorts(decision.outputs, installed->getResults()))
        return e;
    } else {
      if (decision.binding || (flow.get(op).step && !interfaceOperation(op)))
        return error("binding-plan-coverage");
      if (auto e =
              checkLogicalPorts(flow.inputs(op).getTypes(), decision.inputs))
        return e;
      if (auto e =
              checkLogicalPorts(flow.outputs(op).getTypes(), decision.outputs))
        return e;
    }
  }

  if (auto e = checkTargetPlan(selected, plan, plan.input->cpuTarget,
                               failureLocation))
    return e;

  // Independently check actual entry/capture/join/backedge/return equations.
  // This reader does not run forward propagation or select a join preference.
  for (auto [i, op] : enumerate(operations)) {
    const auto &d = plan.operations[i];
    if (auto call = dyn_cast<zkc::protocol_ir::LocalCallOp>(op)) {
      auto *callee =
          SymbolTable::lookupNearestSymbolFrom(op, call.getCalleeAttr());
      auto type = plan.operations[indices.lookup(callee)].functionType;
      if (TypeRange(d.inputs) != type.getInputs() ||
          TypeRange(d.outputs) != type.getResults())
        return error("binding-operation-signature");
    } else if (isa<zkc::protocol_ir::FinishOp>(op)) {
      auto function = op->getParentOfType<zkc::protocol_ir::ParticipantOp>();
      if (TypeRange(d.inputs) !=
          plan.operations[indices.lookup(function)].functionType.getResults())
        return error("binding-operation-signature");
    } else if (isa<zkc::exec::ReturnOp, zkc::exec::CompleteOp>(op)) {
      auto function = op->getParentOfType<func::FuncOp>();
      if (TypeRange(d.inputs) !=
          plan.operations[indices.lookup(function)].functionType.getResults())
        return error("binding-operation-signature");
    } else if (isa<zkc::exec::TestOp, zkc::exec::MatchOp, zkc::exec::RangeOp>(
                   op)) {
      bool loop = isa<zkc::exec::RangeOp>(op);
      bool match = isa<zkc::exec::MatchOp>(op);
      unsigned offset = loop ? 2 : 1;
      // Captures and initial state forward without any new reached work.
      for (unsigned operand = match ? 0 : offset;
           operand < flow.inputs(op).size(); ++operand)
        if (d.inputs[operand] !=
            valuePort(flow.inputs(op)[operand], plan, indices, flow))
          return error("binding-operation-signature");
      if (loop && ArrayRef(d.inputs).slice(2, flow.outputs(op).size()) !=
                      ArrayRef(d.outputs))
        return error("binding-operation-signature");
      if (auto e = checkDefaultPorts(
              TypeRange(flow.inputs(op).getTypes())
                  .take_front(match ? 0 : offset),
              ArrayRef(d.inputs).take_front(match ? 0 : offset)))
        return e;
      for (auto [bodyIndex, entry] : enumerate(flow.get(op).bodies)) {
        const auto &body = flow.body(entry);
        const auto &callee = plan.operations[indices.lookup(body.owner)];
        SmallVector<Type> expected;
        if (loop)
          expected.push_back(d.inputs[0]);
        if (match) {
          auto payload = variantPorts(d.inputs[0], bodyIndex);
          if (!payload)
            return payload.takeError();
          expected = *payload;
        }
        append_range(expected, ArrayRef(d.inputs).drop_front(offset));
        if (TypeRange(expected) != callee.functionType.getInputs())
          return error("binding-operation-signature");
        expected.clear();
        if (loop && flow.get(op).step->conditional) {
          auto condition =
              defaultPort(flow.get(body.owner).callable.getResult(0));
          if (!condition)
            return condition.takeError();
          expected.push_back(*condition);
        }
        append_range(expected, d.outputs);
        if (TypeRange(expected) != callee.functionType.getResults())
          return error("binding-operation-signature");
      }
    } else if (isa<zkc::runtime::ReleaseBindingsOp>(op)) {
      for (auto [operand, value] : enumerate(flow.inputs(op)))
        if (d.inputs[operand] != valuePort(value, plan, indices, flow))
          return error("binding-operation-signature");
    } else if (isa<zkc::exec::VariantOp>(op)) {
      auto variant =
          dyn_cast<data::VariantType>(logicalValueType(d.outputs[0]));
      if (!variant)
        return error("variant-type");
      auto label = op->getAttrOfType<StringAttr>("alternative").getValue();
      unsigned arm = 0;
      for (; arm < variant.getAlternatives().size() &&
             variant.getAlternatives()[arm].getLabel().getValue() != label;
           ++arm) {
      }
      auto payload = variantPorts(d.outputs[0], arm);
      if (!payload)
        return payload.takeError();
      if (d.inputs != *payload)
        return error("binding-operation-signature");
    } else if (!d.binding) {
      if (auto e = checkDefaultPorts(flow.inputs(op).getTypes(), d.inputs))
        return e;
      if (auto e = checkDefaultPorts(flow.outputs(op).getTypes(), d.outputs))
        return e;
    }
  }

  for (const auto &seed : plan.input->valueLayouts) {
    bool found = false;
    for (auto [index, op] : enumerate(operations)) {
      auto function = op->getParentOfType<func::FuncOp>();
      auto site = op->getAttrOfType<StringAttr>("site");
      if (flow.get(op).step && function &&
          function.getSymName() == seed.function && site &&
          site.getValue() == seed.site) {
        if (found || seed.result >= plan.operations[index].outputs.size())
          return error("binding-unknown-selection");
        found = true;
        if (plan.operations[index].outputs[seed.result] != seed.physicalType)
          return error("binding-selection-conflict");
      }
    }
    if (!found)
      return error("binding-unknown-selection");
  }

  // Selected Local preorder and operand order determine instruction positions.
  // No sharing, hoisting, path search, or inferred purity is permitted here.
  std::map<Operation *, std::set<std::string>> sites;
  for (auto *op : operations)
    if (auto function = op->getParentOfType<func::FuncOp>())
      if (auto site = op->getAttrOfType<StringAttr>("site"))
        sites[function].insert(site.getValue().str());
  SmallVector<unsigned> references(plan.bindings.size(), 0);
  for (auto [i, op] : enumerate(operations)) {
    locate(failureLocation, op);
    const auto &decision = plan.operations[i];
    if (decision.binding)
      ++references[*decision.binding];
    size_t crossing = 0;
    for (auto [operand, value] : enumerate(flow.inputs(op))) {
      auto from = valuePort(value, plan, indices, flow);
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
      if (binding.purpose != BindingPurpose::Conversion)
        return error("binding-no-conversion");
      if (auto e = checkDirectConversion(binding.binding.application, from, to))
        return e;
      auto available = catalog.conversions(from, to);
      if (none_of(available, [&](const auto &candidate) {
            return sameApplication(candidate, binding.binding.application);
          }))
        return error("binding-no-conversion");
      auto function = op->getParentOfType<func::FuncOp>();
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
    if (!plan.input->linearContractions ||
        group.producer >= operations.size() || group.producer <= previous ||
        group.consumers.empty())
      return error("binding-contraction");
    previous = group.producer;
    auto actual = checkAllUses(operations[group.producer], plan, indices, flow,
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
      if (auto physical = dyn_cast<zkc::runtime::RepresentedType>(type))
        if (isDiagonalRepresentation(physical.getRepresentation())) {
          auto uses = checkAllUses(op, plan, indices, flow, failureLocation);
          if (!uses)
            return uses.takeError();
        }
  }
  for (auto [i, binding] : enumerate(plan.bindings))
    if (binding.purpose != BindingPurpose::Original && references[i] == 0)
      return error("binding-plan-coverage");
  // Opportunity statistics are separate from admission and installed choices.
  if (plan.input->linearContractions)
    (void)findExecutionContractions(
        flow, operations, indices,
        [&](Operation *op) -> const OperationContracts * {
          auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
          if (!reference)
            return nullptr;
          auto original = originals.find(reference.getValue().str());
          return original == originals.end()
                     ? nullptr
                     : operationContracts(plan.bindings[original->second]
                                              .binding.application.contract);
        },
        stats);
  if (auto e = validateStorage(selected, plan.operations, plan.releases,
                               failureLocation))
    return e;
  if (auto e = plan.input->check(module))
    return e;
  return CheckedPhysicalPlan(plan, stats);
}
} // namespace zkc::target
