#include "PhysicalPlan.h"
#include "../Transforms/Kernel/Support.h"
#include "../Transforms/NumericalLowering.h"
#include "../Transforms/NumericalSelection.h"
#include "AggregateLayouts.h"
#include "mlir/IR/RegionKindInterface.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Target/Selection.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
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
struct InputSnapshot {
  ModuleOp subject;
  std::string contents;
  SmallVector<const void *> addresses;
  protocol::Assignments selections;
  bool linearContractions;
  MathematicalSelectionPolicy numericalPolicy;
  SmallVector<FunctionPortSelection> functionPorts;
  SmallVector<ValueLayoutSelection> valueLayouts;
  // This owned payload is the numerical decision, including actual recipes,
  // generated bindings, sites and SSA. Policy flags are not a replay format.
  // Accessible only inside Target; callers can obtain independent clones.
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
Expected<FunctionType>
selectedFunctionType(Operation *op,
                     ArrayRef<FunctionPortSelection> selections) {
  auto logical = cast<FunctionType>(
      op->getAttrOfType<TypeAttr>("function_type").getValue());
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
      const FunctionPortSelection *choice = nullptr;
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
      auto schema = encodeBoundType(source, false);
      if (!schema)
        return schema.takeError();
      auto selected = parseBoundType(choice->physicalType, true);
      if (!selected)
        return selected.takeError();
      if (!(erasePhysicalType(*selected) == *schema))
        return error("binding-operation-signature");
      auto type = decodeBoundType(op->getContext(), *selected);
      if (!type)
        return error("binding-representation");
      ports.push_back(type);
    }
  }
  return FunctionType::get(op->getContext(), inputs, outputs);
}

Expected<SmallVector<Type>> variantPorts(Type type, unsigned alternative) {
  auto bound = encodeBoundType(type, true);
  if (!bound)
    return bound.takeError();
  auto descriptor = decodeVariant(erasePhysicalType(*bound).spelling());
  if (!descriptor || !bound->physicalChildren ||
      alternative >= descriptor->alternatives.size())
    return error("variant-type");
  size_t start = 0;
  for (unsigned i = 0; i < alternative; ++i)
    start += descriptor->alternatives[i].payload.size();
  auto children =
      ArrayRef(*bound->physicalChildren)
          .slice(start, descriptor->alternatives[alternative].payload.size());
  return decodePorts(type.getContext(), children);
}
bool sameApplication(const BindingApplication &a, const BindingApplication &b) {
  return a.contract == b.contract && a.arguments == b.arguments &&
         a.implementation == b.implementation &&
         a.physicalArguments == b.physicalArguments;
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
      auto descriptor = installedImplementations().find(
          selected.contract, selected.implementation);
      // Candidate order never supplies an implementation's explicit premise.
      // Trusted runtime linking permission remains an independent obligation.
      if (descriptor && descriptor->requiresExplicitSelection)
        continue;
      auto installed = descriptor &&
                               descriptor->family !=
                                   ImplementationDescriptor::Family::Exact &&
                               selected.physicalArguments.empty()
                           ? resolveBinding(selected, false)
                           : resolveBinding(selected, true);
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
  ArrayRef<FunctionPortSelection> functionPorts;
  ArrayRef<ValueLayoutSelection> valueLayouts;
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
    if (decision.fixed ||
        !decision.binding.application.physicalArguments.empty())
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
      auto logical = encodeBoundType(type, false);
      if (!logical) {
        consumeError(logical.takeError());
        return false;
      }
      return logical->kind == "sequence" || logical->kind == "variant" ||
             logical->kind == "field_array" || logical->kind == "fixed_vector";
    };
    auto pin = [&](Value value, Type type, OperationIndex owner) -> Error {
      auto id = layouts.get(value);
      if (!id)
        return id.takeError();
      auto bound = encodeBoundType(type, true);
      if (!bound)
        return bound.takeError();
      return layouts.pin(*id, *bound, owner);
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
      if (d.functionType && !op->getRegions().empty())
        for (auto [value, type] : zip(op->getRegion(0).front().getArguments(),
                                      d.functionType.getInputs()))
          if (auto e = pin(value, type, index))
            return e;
      if (d.binding) {
        const auto &app = plan.bindings[*d.binding].binding.application;
        auto descriptor =
            installedImplementations().find(app.contract, app.implementation);
        using Family = ImplementationDescriptor::Family;
        if (descriptor && descriptor->family == Family::Sequence &&
            app.physicalArguments.empty()) {
          if (app.contract == "sequence.append") {
            if (auto e = equate(op->getOperand(0), op->getResult(0)))
              return e;
            auto container = layouts.get(op->getResult(0));
            if (!container)
              return container.takeError();
            if (auto e = payload(op->getOperand(1),
                                 layouts.child(*container, 0), true))
              return e;
          } else if (app.contract == "sequence.at") {
            auto container = layouts.get(op->getOperand(0));
            if (!container)
              return container.takeError();
            if (auto e = payload(op->getResult(0), layouts.child(*container, 0),
                                 false))
              return e;
          } else if (app.contract != "sequence.empty") {
            for (auto [value, type] : zip(op->getResults(), d.outputs))
              if (auto e = pin(value, type, index))
                return e;
          }
        } else {
          // Exact definitions, explicit parameters, and dense provider layouts
          // constrain aggregate ports. Observation's inferred payload does not.
          bool observation = descriptor &&
                             descriptor->family == Family::Observation &&
                             app.physicalArguments.empty();
          for (auto [value, type] : zip(op->getOperands(), d.inputs))
            if (aggregate(value.getType()) && !observation)
              if (auto e = pin(value, type, index))
                return e;
          for (auto [value, type] : zip(op->getResults(), d.outputs))
            if (auto e = pin(value, type, index))
              return e;
        }
      } else if (auto call = dyn_cast<zkc::local::CallOp>(op)) {
        auto *callee =
            SymbolTable::lookupNearestSymbolFrom(op, call.getCalleeAttr());
        auto type = plan.operations[indices.lookup(callee)].functionType;
        for (auto [value, target] : zip(op->getOperands(), type.getInputs()))
          if (aggregate(value.getType()))
            if (auto e = pin(value, target, index))
              return e;
        for (auto [value, target] : zip(op->getResults(), type.getResults()))
          if (auto e = pin(value, target, index))
            return e;
      } else if (isa<zkc::local::VariantInjectOp>(op)) {
        auto container = layouts.get(op->getResult(0));
        if (!container)
          return container.takeError();
        auto logical = encodeBoundType(op->getResult(0).getType(), false);
        if (!logical)
          return logical.takeError();
        auto descriptor = decodeVariant(logical->spelling());
        if (!descriptor)
          return error("variant-type");
        auto label = op->getAttrOfType<StringAttr>("alternative").getValue();
        unsigned offset = 0;
        for (const auto &arm : descriptor->alternatives) {
          if (arm.label == label)
            break;
          offset += arm.payload.size();
        }
        for (auto [i, value] : enumerate(op->getOperands()))
          if (auto e =
                  payload(value, layouts.child(*container, offset + i), true))
            return e;
      } else if (isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp,
                     zkc::local::LocalForOp>(op)) {
        bool loop = isa<zkc::local::LocalForOp>(op);
        bool match = isa<zkc::local::LocalMatchOp>(op);
        unsigned offset = loop ? 2 : 1;
        unsigned payloadOffset = 0;
        for (auto &region : op->getRegions()) {
          auto args = region.front().getArguments();
          unsigned prefix = loop ? 1 : args.size() - (op->getNumOperands() - 1);
          if (match) {
            auto container = layouts.get(op->getOperand(0));
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
                   op->getOperands().drop_front(offset)))
            if (auto e = equate(argument, captured))
              return e;
          auto &end = region.front().back();
          if (!isa<zkc::local::StopOp>(end)) {
            unsigned skip = isa<zkc::local::LocalConditionOp>(end);
            for (auto [result, yielded] :
                 zip(op->getResults(), end.getOperands().drop_front(skip)))
              if (aggregate(result.getType()))
                if (auto e = equate(result, yielded))
                  return e;
            if (loop)
              for (auto [captured, yielded] :
                   zip(op->getOperands().drop_front(2 + op->getNumResults()),
                       end.getOperands().drop_front(skip +
                                                    op->getNumResults())))
                if (aggregate(captured.getType()))
                  if (auto e = equate(captured, yielded))
                    return e;
          }
        }
        if (loop)
          for (auto [result, initial] :
               zip(op->getResults(), op->getOperands().drop_front(2)))
            if (auto e = equate(result, initial))
              return e;
        if (!loop)
          for (auto result : op->getResults())
            if (!aggregate(result.getType())) {
              auto target = layouts.get(result);
              if (!target)
                return target.takeError();
              SmallVector<AggregateLayouts::Id> sources;
              for (auto &region : op->getRegions()) {
                auto &end = region.front().back();
                if (!isa<zkc::local::StopOp>(end)) {
                  auto source =
                      layouts.get(end.getOperand(result.getResultNumber()));
                  if (!source)
                    return source.takeError();
                  sources.push_back(*source);
                }
              }
              if (auto e = layouts.join(*target, std::move(sources)))
                return e;
            }
      } else if (isa<zkc::local::ReturnOp, zkc::protocol_ir::FinishOp>(op)) {
        auto type =
            plan.operations[indices.lookup(op->getParentOp())].functionType;
        for (auto [value, target] : zip(op->getOperands(), type.getResults()))
          if (aggregate(value.getType()))
            if (auto e = pin(value, target, index))
              return e;
      } else {
        for (auto [value, type] : zip(op->getResults(), d.outputs))
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
        auto function = op->getParentOfType<zkc::local::FuncOp>();
        auto site = op->getAttrOfType<StringAttr>("site");
        if (function && function.getSymName() == seed.function && site &&
            site.getValue() == seed.site) {
          if (found)
            return error("binding-duplicate-selection");
          found = op;
        }
      }
      if (!found || seed.result >= found->getNumResults())
        return error("binding-unknown-selection");
      auto selected = parseBoundType(seed.physicalType, true);
      if (!selected)
        return selected.takeError();
      auto logical =
          encodeBoundType(found->getResult(seed.result).getType(), false);
      if (!logical)
        return logical.takeError();
      if (!(erasePhysicalType(*selected) == *logical))
        return error("binding-operation-signature");
      auto type = decodeBoundType(module.getContext(), *selected);
      if (!type)
        return error("binding-representation");
      if (auto e =
              pin(found->getResult(seed.result), type, indices.lookup(found)))
        return e;
      hints[found->getResult(seed.result)] = type;
    }
    if (auto e = layouts.solve())
      return e;
    for (auto *op : operations)
      for (auto result : op->getResults())
        if (aggregate(result.getType()) ||
            isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp>(op)) {
          locate(failureLocation, op);
          auto id = layouts.get(result);
          if (!id)
            return id.takeError();
          auto type = layouts.physical(*id);
          if (!type)
            return type.takeError();
          hints[result] = decodeBoundType(module.getContext(), *type);
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
    SmallVector<BindingApplication> applications(operations.size());
    llvm::DenseMap<Value, Type> hints;
    std::deque<Operation *> pending;
    llvm::DenseSet<Operation *> queued;
    auto enqueue = [&](Operation *op) {
      if (op && queued.insert(op).second)
        pending.push_back(op);
    };
    auto notify = [&](Value value) {
      for (auto *user : value.getUsers())
        enqueue(user);
    };
    auto assign = [&](Value value, Type type) {
      if (valuePort(value, plan, indices) == type)
        return;
      if (auto result = dyn_cast<OpResult>(value))
        plan.operations[indices.lookup(result.getOwner())]
            .outputs[result.getResultNumber()] = type;
      else {
        auto arg = cast<BlockArgument>(value);
        auto *owner = arg.getOwner()->getParentOp();
        size_t blockIndex = 0;
        for (auto &region : owner->getRegions())
          for (auto &block : region) {
            if (&block == arg.getOwner())
              plan.operations[indices.lookup(owner)]
                  .blockArguments[blockIndex][arg.getArgNumber()] = type;
            ++blockIndex;
          }
      }
      notify(value);
    };
    auto aggregate = [&](Type type) {
      auto logical = encodeBoundType(type, isa<zkc::plan::DataType>(type));
      if (!logical) {
        consumeError(logical.takeError());
        return false;
      }
      return logical->kind == "sequence" || logical->kind == "variant" ||
             logical->kind == "field_array" || logical->kind == "fixed_vector";
    };
    for (auto [index, op] : enumerate(operations)) {
      auto &d = plan.operations[index];
      for (auto &region : op->getRegions())
        for (auto &block : region) {
          SmallVector<Type> args;
          for (auto type : block.getArgumentTypes())
            args.push_back(initial(type));
          d.blockArguments.push_back(std::move(args));
        }
      if (op->getAttrOfType<TypeAttr>("function_type")) {
        auto selected = selectedFunctionType(op, functionPorts);
        if (!selected)
          return selected.takeError();
        d.functionType = *selected;
        if (!d.blockArguments.empty())
          d.blockArguments[0].assign(selected->getInputs().begin(),
                                     selected->getInputs().end());
      }
      if (d.binding) {
        applications[index] = plan.bindings[*d.binding].binding.application;
        auto initialApplication = applications[index];
        auto descriptor = installedImplementations().find(
            initialApplication.contract, initialApplication.implementation);
        bool deferred =
            descriptor &&
            descriptor->family != ImplementationDescriptor::Family::Exact &&
            initialApplication.physicalArguments.empty();
        if (deferred) {
          auto parameters = defaultPhysicalArguments(initialApplication);
          if (parameters)
            initialApplication.physicalArguments = *parameters;
          else
            consumeError(parameters.takeError());
        }
        auto signature = resolveBinding(initialApplication, true);
        if (!signature) {
          if (!deferred)
            return signature.takeError();
          consumeError(signature.takeError());
          for (auto type : op->getResultTypes())
            d.outputs.push_back(initial(type));
          for (auto type : op->getOperandTypes())
            d.inputs.push_back(initial(type));
        } else {
          auto inputs = decodePorts(module.getContext(), signature->inputs);
          if (!inputs)
            return inputs.takeError();
          auto outputs = decodePorts(module.getContext(), signature->outputs);
          if (!outputs)
            return outputs.takeError();
          d.inputs = *inputs;
          d.outputs = *outputs;
        }
      } else
        for (auto type : op->getResultTypes())
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
      if (auto call = dyn_cast<zkc::local::CallOp>(op)) {
        auto *callee =
            SymbolTable::lookupNearestSymbolFrom(op, call.getCalleeAttr());
        auto type = plan.operations[indices.lookup(callee)].functionType;
        d.inputs.assign(type.getInputs().begin(), type.getInputs().end());
        for (auto [result, target] : zip(op->getResults(), type.getResults()))
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
          if (app.physicalArguments.empty()) {
            auto selected = encodeBoundType(
                valuePort(op->getOperand(payload), plan, indices), true);
            if (!selected) {
              consumeError(selected.takeError());
              continue;
            }
            app.physicalArguments = {selected->spelling()};
          }
          auto signature = resolveBinding(app, true);
          if (!signature)
            return familyFailure(signature.takeError(), plan, index);
          auto inputs = decodePorts(module.getContext(), signature->inputs);
          if (!inputs)
            return inputs.takeError();
          auto outputs = decodePorts(module.getContext(), signature->outputs);
          if (!outputs)
            return outputs.takeError();
          d.inputs = *inputs;
          for (auto [result, type] : zip(op->getResults(), *outputs))
            assign(result, type);
          applications[index] = std::move(app);
          if (plan.bindings[*d.binding]
                  .binding.application.physicalArguments.empty())
            applications[index].physicalArguments.clear();
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
          auto logicalSignature = resolveLogicalBinding(app);
          if (!logicalSignature)
            return logicalSignature.takeError();
          const BoundType *containerSchema = nullptr;
          for (const auto *ports :
               {&logicalSignature->inputs, &logicalSignature->outputs})
            for (const auto &port : *ports)
              if (!containerSchema && port.kind == kind)
                containerSchema = &port;
          if (!containerSchema)
            return error("binding-representation");
          for (auto result : op->getResults())
            if (auto hint = hints.lookup(result)) {
              auto selected = encodeBoundType(hint, true);
              if (!selected)
                return selected.takeError();
              if (erasePhysicalType(*selected) == *containerSchema) {
                container = hint;
                break;
              }
              if (app.contract == "sequence.at") {
                auto formed = physicalType(*containerSchema,
                                           "logical.sequence/0", {*selected});
                if (!formed)
                  return formed.takeError();
                container = decodeBoundType(module.getContext(), *formed);
              }
            }
          // Actual container inputs determine access and append layouts.
          for (auto operand : op->getOperands()) {
            auto actual = valuePort(operand, plan, indices);
            auto bound = encodeBoundType(actual, true);
            if (!bound) {
              consumeError(bound.takeError());
              continue;
            }
            if (bound->kind == kind) {
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
          if (container && isa<zkc::plan::DataType>(container)) {
            auto selected = encodeBoundType(container, true);
            if (!selected)
              return selected.takeError();
            if (app.physicalArguments.empty())
              app.physicalArguments = {selected->spelling()};
          }
          auto signature = resolveBinding(app, true);
          if (!signature) {
            if (!container || !isa<zkc::plan::DataType>(container)) {
              consumeError(signature.takeError());
              continue;
            }
            return familyFailure(signature.takeError(), plan, index);
          }
          auto inputs = decodePorts(module.getContext(), signature->inputs);
          if (!inputs)
            return inputs.takeError();
          auto outputs = decodePorts(module.getContext(), signature->outputs);
          if (!outputs)
            return outputs.takeError();
          d.inputs = *inputs;
          for (auto [result, type] : zip(op->getResults(), *outputs))
            assign(result, type);
          applications[index] = std::move(app);
          // Recompute unconstrained source families when their inputs change.
          if (plan.bindings[*d.binding]
                  .binding.application.physicalArguments.empty())
            applications[index].physicalArguments.clear();
        }
        continue;
      }
      if (isa<zkc::local::VariantInjectOp>(op)) {
        auto logical = encodeBoundType(op->getResult(0).getType(), false);
        if (!logical)
          return logical.takeError();
        auto descriptor = decodeVariant(logical->spelling());
        if (!descriptor)
          return error("variant-type");
        auto label = op->getAttrOfType<StringAttr>("alternative").getValue();
        size_t start = 0;
        unsigned active = 0;
        for (; active < descriptor->alternatives.size() &&
               descriptor->alternatives[active].label != label;
             ++active)
          start += descriptor->alternatives[active].payload.size();
        if (active == descriptor->alternatives.size())
          return error("variant-alternative");
        Type selected = hints.lookup(op->getResult(0));
        if (!selected) {
          auto schemas = logicalChildren(*logical);
          if (!schemas)
            return schemas.takeError();
          std::vector<BoundType> children;
          bool ready = true;
          for (auto [i, schema] : enumerate(*schemas)) {
            Expected<BoundType> child =
                i >= start && i < start + op->getNumOperands()
                    ? encodeBoundType(
                          valuePort(op->getOperand(i - start), plan, indices),
                          true)
                    : defaultRepresentation(schema);
            if (!child) {
              consumeError(child.takeError());
              ready = false;
              break;
            }
            children.push_back(std::move(*child));
          }
          if (!ready)
            continue;
          auto formed =
              physicalType(*logical, "logical.variant/0", std::move(children));
          if (!formed)
            return formed.takeError();
          selected = decodeBoundType(module.getContext(), *formed);
        }
        assign(op->getResult(0), selected);
        auto payload = variantPorts(selected, active);
        if (!payload)
          return payload.takeError();
        d.inputs = *payload;
      } else if (isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp,
                     zkc::local::LocalForOp>(op)) {
        auto previousInputs = d.inputs;
        auto previousOutputs = d.outputs;
        bool loop = isa<zkc::local::LocalForOp>(op),
             match = isa<zkc::local::LocalMatchOp>(op);
        if (match && !isa<zkc::plan::DataType>(
                         valuePort(op->getOperand(0), plan, indices)))
          continue;
        unsigned offset = loop ? 2 : 1;
        d.inputs.clear();
        for (unsigned i = 0; i < offset; ++i)
          d.inputs.push_back(match ? valuePort(op->getOperand(i), plan, indices)
                                   : initial(op->getOperand(i).getType()));
        for (auto operand : op->getOperands().drop_front(offset))
          d.inputs.push_back(valuePort(operand, plan, indices));
        for (auto [regionIndex, region] : enumerate(op->getRegions())) {
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
          for (auto [arg, type] : zip(region.front().getArguments(), args))
            assign(arg, type);
        }
        for (auto result : op->getResults()) {
          Type selected = loop ? d.inputs[2 + result.getResultNumber()]
                               : hints.lookup(result);
          if (!selected) {
            for (auto &region : op->getRegions()) {
              auto &end = region.front().back();
              if (isa<zkc::local::StopOp>(end))
                continue;
              auto type = valuePort(end.getOperand(result.getResultNumber()),
                                    plan, indices);
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
        if (d.inputs != previousInputs || d.outputs != previousOutputs)
          for (auto &region : op->getRegions())
            enqueue(&region.front().back());
      } else if (isa<zkc::local::ReturnOp, zkc::protocol_ir::FinishOp>(op)) {
        Operation *function = op->getParentOp();
        auto type = plan.operations[indices.lookup(function)].functionType;
        d.inputs.assign(type.getResults().begin(), type.getResults().end());
      } else if (isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                     op)) {
        auto *parent = op->getParentOp();
        const auto &p = plan.operations[indices.lookup(parent)];
        d.inputs.clear();
        if (isa<zkc::local::LocalConditionOp>(op))
          d.inputs.push_back(initial(op->getOperand(0).getType()));
        append_range(d.inputs, p.outputs);
        if (isa<zkc::local::LocalForOp>(parent))
          append_range(d.inputs, ArrayRef(p.blockArguments[0])
                                     .drop_front(1 + parent->getNumResults()));
        enqueue(parent);
      } else {
        d.inputs.clear();
        for (auto type : op->getOperandTypes())
          d.inputs.push_back(initial(type));
      }
    }
    for (auto [index, op] : enumerate(operations)) {
      auto &d = plan.operations[index];
      for (auto type : d.outputs) {
        auto checked = encodeBoundType(type, true);
        if (!checked)
          return checked.takeError();
      }
      for (auto type : d.inputs) {
        auto checked = encodeBoundType(type, true);
        if (!checked)
          return checked.takeError();
      }
      for (const auto &args : d.blockArguments)
        for (auto type : args) {
          auto checked = encodeBoundType(type, true);
          if (!checked)
            return checked.takeError();
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
      auto descriptor =
          installedImplementations().find(app.contract, app.implementation);
      if (descriptor &&
          descriptor->family == ImplementationDescriptor::Family::Observation) {
        auto payload =
            operationContracts(app.contract)->observation->payloadInput;
        auto selected = encodeBoundType(d.inputs[payload], true);
        if (!selected)
          return selected.takeError();
        app.physicalArguments = {selected->spelling()};
      } else if (descriptor && descriptor->family !=
                                   ImplementationDescriptor::Family::Exact) {
        const auto &ports =
            descriptor->family == ImplementationDescriptor::Family::Sequence &&
                    app.contract == "sequence.empty"
                ? d.outputs
                : d.inputs;
        for (auto type : ports) {
          auto bound = encodeBoundType(type, true);
          if (!bound)
            return bound.takeError();
          if (bound->physicalChildren &&
              (bound->kind == "sequence" || bound->kind == "field_array" ||
               bound->kind == "fixed_vector")) {
            app.physicalArguments = {bound->spelling()};
            break;
          }
        }
        if (app.physicalArguments.empty()) {
          auto parameters = defaultPhysicalArguments(app);
          if (!parameters)
            return parameters.takeError();
          app.physicalArguments = *parameters;
        }
      }
      applications[index] = std::move(app);
    }
    // Normalize origins first. A family without a complete default can reuse
    // its first reached application; unused declarations still require an
    // independently admitted complete default.
    for (auto [origin, binding] : enumerate(plan.bindings))
      if (binding.binding.application.physicalArguments.empty()) {
        auto parameters = defaultPhysicalArguments(binding.binding.application);
        if (!parameters) {
          bool found = false;
          for (auto [index, decision] : enumerate(plan.operations))
            if (decision.binding == origin &&
                !applications[index].physicalArguments.empty()) {
              consumeError(parameters.takeError());
              binding.binding.application.physicalArguments =
                  applications[index].physicalArguments;
              found = true;
              break;
            }
          if (!found)
            return parameters.takeError();
        } else
          binding.binding.application.physicalArguments =
              std::move(*parameters);
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
           ArrayRef<FunctionPortSelection> functionPorts,
           ArrayRef<ValueLayoutSelection> valueLayouts)
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
  auto input = std::make_shared<InputSnapshot>(
      InputSnapshot{module,
                    structure(module),
                    identities(module),
                    protocol::Assignments(selections.begin(), selections.end()),
                    options.linearContractions,
                    options.numericalPolicy,
                    options.functionPorts,
                    options.valueLayouts,
                    {}});
  for (const auto &choice : options.functionPorts) {
    bool found = false;
    for (auto &op : root.getBody().front())
      if (isa<zkc::local::FuncOp, zkc::protocol_ir::ParticipantOp>(op))
        found |= op.getAttrOfType<StringAttr>("sym_name").getValue() ==
                 choice.function;
    if (!found)
      return error("binding-unknown-selection");
  }
  bool hasKernels = false, hasMaps = false;
  root.walk([&](Operation *op) {
    hasKernels |=
        (mathematical::isComputationUnit(op) || isa<kernel::CallOp>(op));
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
    if (auto e = input->check(module))
      return e;
    selection.failure = {};
    selection.bindingCursors.clear();
    PhysicalPlan plan;
    Proposer proposer(selected, catalog, failureLocation, selection,
                      options.functionPorts, options.valueLayouts);
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
          refusal = proposer.capacityFailure(plan, *capacity);
          if (!refusal)
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
      if (auto e = input->check(module))
        return e;
      selection.numerical.origins.clear();
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
  if (!sameLogical(source, selected) ||
      (!source.physicalArguments.empty() &&
       source.physicalArguments != selected.physicalArguments))
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
    auto original = encodeBoundType(source, false);
    if (!original)
      return original.takeError();
    if (!type)
      return error("binding-operation-signature");
    auto selected = encodeBoundType(type, true);
    if (!selected)
      return selected.takeError();
    auto erased = erasePhysicalType(*selected);
    if (!(erased == *original))
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
  if (!plan.input)
    return error("binding-stale-selection");
  if (auto e = plan.input->check(module))
    return e;
  // Check the original Kernel-bearing source independently against the exact
  // retained Local payload, before checking any installed physical choices.
  // This reader does not emit or select numerical recipes.
  if (failed(verify(module)))
    return error("binding-operation");
  ModuleOp selected = module;
  if (plan.input->numerical) {
    selected = *plan.input->numerical;
    if (failed(mathematical::verifyNumericalLowering(
            module, selected, plan.input->numericalPolicy,
            plan.input->selections)))
      return error("numerical-lowering-correspondence");
  }
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
  for (const auto &[key, implementation] : plan.input->selections)
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
        bool residentRegion =
            isa<zkc::local::FuncOp, zkc::protocol_ir::ParticipantOp,
                zkc::local::LocalIfOp, zkc::local::LocalMatchOp,
                zkc::local::LocalForOp>(op);
        auto check = residentRegion ? checkLogicalPorts : checkDefaultPorts;
        if (auto e = check(block.getArgumentTypes(),
                           decision.blockArguments[blockIndex++]))
          return e;
      }
    if (blockIndex != decision.blockArguments.size())
      return error("binding-operation-signature");
    if (auto signature = op->getAttrOfType<TypeAttr>("function_type")) {
      auto expected = selectedFunctionType(op, plan.input->functionPorts);
      if (!expected)
        return expected.takeError();
      if (!decision.functionType || decision.functionType != *expected)
        return error("binding-operation-signature");
      if (!decision.blockArguments.empty() &&
          TypeRange(decision.blockArguments[0]) != expected->getInputs())
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
      // The source verifier also checks its ODS association and parameters.
      if (failed(verifyBoundOperation(op, false)))
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
      if (auto e = checkLogicalPorts(op->getOperandTypes(), decision.inputs))
        return e;
      if (auto e = checkLogicalPorts(op->getResultTypes(), decision.outputs))
        return e;
    }
  }

  // Independently check actual entry/capture/join/backedge/return equations.
  // This reader does not run forward propagation or select a join preference.
  for (auto [i, op] : enumerate(operations)) {
    const auto &d = plan.operations[i];
    if (auto call = dyn_cast<zkc::local::CallOp>(op)) {
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
    } else if (isa<zkc::local::ReturnOp>(op)) {
      auto function = op->getParentOfType<zkc::local::FuncOp>();
      if (TypeRange(d.inputs) !=
          plan.operations[indices.lookup(function)].functionType.getResults())
        return error("binding-operation-signature");
    } else if (isa<zkc::local::LocalIfOp, zkc::local::LocalMatchOp,
                   zkc::local::LocalForOp>(op)) {
      bool loop = isa<zkc::local::LocalForOp>(op);
      unsigned offset = loop ? 2 : 1;
      for (unsigned operand = offset; operand < op->getNumOperands();
           ++operand) {
        auto from = valuePort(op->getOperand(operand), plan, indices);
        auto required = from;
        if (d.inputs[operand] != required)
          return error("binding-operation-signature");
      }
      if (loop) {
        if (ArrayRef(d.inputs).slice(2, op->getNumResults()) !=
            ArrayRef(d.outputs))
          return error("binding-operation-signature");
        if (d.blockArguments.size() != 1 ||
            ArrayRef(d.blockArguments[0]).drop_front() !=
                ArrayRef(d.inputs).drop_front(2))
          return error("binding-operation-signature");
      } else {
        for (auto [blockIndex, args] : enumerate(d.blockArguments)) {
          unsigned captures = op->getNumOperands() - 1;
          if (args.size() < captures || ArrayRef(args).take_back(captures) !=
                                            ArrayRef(d.inputs).drop_front())
            return error("binding-operation-signature");
          if (isa<zkc::local::LocalIfOp>(op) && args.size() != captures)
            return error("binding-operation-signature");
          if (isa<zkc::local::LocalMatchOp>(op)) {
            if (d.inputs[0] != valuePort(op->getOperand(0), plan, indices))
              return error("binding-operation-signature");
            auto payload = variantPorts(d.inputs[0], blockIndex);
            if (!payload)
              return payload.takeError();
            if (ArrayRef(args).drop_back(captures) != ArrayRef(*payload))
              return error("binding-operation-signature");
          }
        }
      }
      // Conditions and induction values keep their fixed native contract.
      if (auto e = checkDefaultPorts(
              TypeRange(op->getOperandTypes())
                  .take_front(isa<zkc::local::LocalMatchOp>(op) ? 0 : offset),
              ArrayRef(d.inputs).take_front(
                  isa<zkc::local::LocalMatchOp>(op) ? 0 : offset)))
        return e;
      if (loop && d.blockArguments[0][0] != d.inputs[0])
        return error("binding-operation-signature");
    } else if (isa<zkc::local::LocalYieldOp, zkc::local::LocalConditionOp>(
                   op)) {
      auto *parent = op->getParentOp();
      const auto &p = plan.operations[indices.lookup(parent)];
      unsigned offset = isa<zkc::local::LocalConditionOp>(op) ? 1 : 0;
      SmallVector<Type> expected;
      if (offset)
        expected.push_back(*defaultPort(op->getOperand(0).getType()));
      append_range(expected, p.outputs);
      if (isa<zkc::local::LocalForOp>(parent))
        append_range(expected, ArrayRef(p.blockArguments[0])
                                   .drop_front(1 + parent->getNumResults()));
      if (d.inputs != expected)
        return error("binding-operation-signature");
    } else if (isa<zkc::local::VariantInjectOp>(op)) {
      auto bound = encodeBoundType(d.outputs[0], true);
      if (!bound)
        return bound.takeError();
      auto descriptor = decodeVariant(erasePhysicalType(*bound).spelling());
      if (!descriptor)
        return error("variant-type");
      auto label = op->getAttrOfType<StringAttr>("alternative").getValue();
      unsigned arm = 0;
      for (; arm < descriptor->alternatives.size() &&
             descriptor->alternatives[arm].label != label;
           ++arm) {
      }
      auto payload = variantPorts(d.outputs[0], arm);
      if (!payload)
        return payload.takeError();
      if (d.inputs != *payload)
        return error("binding-operation-signature");
    } else if (!d.binding) {
      if (auto e = checkDefaultPorts(op->getOperandTypes(), d.inputs))
        return e;
      if (auto e = checkDefaultPorts(op->getResultTypes(), d.outputs))
        return e;
    }
  }

  for (const auto &seed : plan.input->valueLayouts) {
    bool found = false;
    auto expected = parseBoundType(seed.physicalType, true);
    if (!expected)
      return expected.takeError();
    for (auto [index, op] : enumerate(operations)) {
      auto function = op->getParentOfType<zkc::local::FuncOp>();
      auto site = op->getAttrOfType<StringAttr>("site");
      if (function && function.getSymName() == seed.function && site &&
          site.getValue() == seed.site) {
        if (found || seed.result >= plan.operations[index].outputs.size())
          return error("binding-unknown-selection");
        found = true;
        auto actual =
            encodeBoundType(plan.operations[index].outputs[seed.result], true);
        if (!actual)
          return actual.takeError();
        if (!(*actual == *expected))
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
    if (!plan.input->linearContractions ||
        group.producer >= operations.size() || group.producer <= previous ||
        group.consumers.empty())
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
  if (plan.input->linearContractions)
    for (auto function : root.getBody().front().getOps<zkc::local::FuncOp>())
      (void)findLinearContractions(function, stats);
  if (auto e = validateStorage(selected, plan.operations, plan.releases,
                               failureLocation))
    return e;
  if (auto e = plan.input->check(module))
    return e;
  return CheckedPhysicalPlan(plan, stats);
}
} // namespace zkc::target
