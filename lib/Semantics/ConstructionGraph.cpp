//===- ConstructionGraph.cpp - typed prover construction routes ---------===//

#include "ConstructionGraph.h"

#include "zkc/Dialect/Pir/KappaView.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"

#include <functional>

using namespace llvm;
using namespace mlir;
using namespace zkc;

bool semantics::isRouteInstanceName(StringRef name) {
  if (name.empty() || !encoding::inEncodingDomain(name) || name.contains(':'))
    return false;
  SmallVector<StringRef> components;
  name.split(components, '.');
  return llvm::all_of(components,
                      [](StringRef component) { return !component.empty(); });
}

Expected<semantics::RouteReference>
semantics::parseRouteReference(StringRef text) {
  RouteReference reference;
  StringRef name = text;
  if (name.consume_front("bind:"))
    reference.kind = RouteReferenceKind::Bind;
  else if (name.consume_front("slot:"))
    reference.kind = RouteReferenceKind::Slot;
  else if (name.consume_front("chal:"))
    reference.kind = RouteReferenceKind::Challenge;
  else if (name.consume_front("const:"))
    reference.kind = RouteReferenceKind::Constant;
  else if (name.consume_front("witness:"))
    reference.kind = RouteReferenceKind::Witness;
  else {
    size_t separator = name.rfind('.');
    if (separator == StringRef::npos || separator == 0 ||
        separator + 1 == name.size())
      return createStringError("'" + text.str() +
                               "' is not a construction-route reference");
    uint64_t output = 0;
    if (name.substr(separator + 1).getAsInteger(10, output))
      return createStringError("'" + text.str() +
                               "' has no decimal result index");
    StringRef instance = name.substr(0, separator);
    if (!isRouteInstanceName(instance))
      return createStringError("route instance reference '" + instance.str() +
                               "' is not a dotted namespace name");
    reference.kind = RouteReferenceKind::InstanceResult;
    reference.name = instance.str();
    reference.output = output;
    return reference;
  }

  if (name.empty() || !encoding::inEncodingDomain(name))
    return createStringError("'" + text.str() +
                             "' has an invalid route-reference name");
  reference.name = name.str();
  return reference;
}

std::string semantics::printRouteReference(const RouteReference &reference) {
  switch (reference.kind) {
  case RouteReferenceKind::Bind:
    return "bind:" + reference.name;
  case RouteReferenceKind::Slot:
    return "slot:" + reference.name;
  case RouteReferenceKind::Challenge:
    return "chal:" + reference.name;
  case RouteReferenceKind::Constant:
    return "const:" + reference.name;
  case RouteReferenceKind::Witness:
    return "witness:" + reference.name;
  case RouteReferenceKind::InstanceResult:
    return reference.name + "." + std::to_string(reference.output);
  }
  llvm_unreachable("closed route-reference kind");
}

namespace zkc::semantics::detail {

struct ValueShape {
  registry::HoleSegmentSort sort = registry::HoleSegmentSort::Value;
  StringRef typeClass;
  StringRef count;
  Operation *source = nullptr;
};

class ConstructionGraphBuilder {
public:
  ConstructionGraphBuilder(Operation *container,
                           const registry::ProtocolEnvironment &environment)
      : container(container), vocabulary(environment.protocolVocabulary()),
        body(container->getRegion(0).front()) {}

  FailureOr<semantics::ConstructionGraph> build() {
    routes = container->getAttrOfType<DictionaryAttr>("routes");
    indexCarrier();
    if (!routes) {
      for (Operation &operation : body)
        if (auto slot = dyn_cast<pir::SlotOp>(operation);
            slot && slot.getBinding())
          return fail("slot '" + slot.getLabel() +
                      "' declares a binding but the protocol declares no "
                      "routes");
      return std::move(graph);
    }

    if (failed(checkTopLevel()) || failed(readWitnesses()) ||
        failed(readInstances()) || failed(readInputs()) ||
        failed(checkAcyclic()) || failed(readSlotBindings()) ||
        failed(checkEventAvailability()))
      return failure();
    return std::move(graph);
  }

private:
  FailureOr<semantics::ConstructionGraph> fail(const Twine &message) {
    container->emitOpError() << "[zkc-E223] " << message;
    return failure();
  }

  LogicalResult reject(const Twine &message) {
    (void)fail(message);
    return failure();
  }

  void indexCarrier() {
    int64_t position = 0;
    for (Operation &operation : body) {
      bodyPositions[&operation] = position++;
      if (auto bind = dyn_cast<pir::BindOp>(operation)) {
        binds[bind.getLabel()].push_back({registry::HoleSegmentSort::Value,
                                          bind.getPayloadClass(), "1",
                                          &operation});
      } else if (auto slot = dyn_cast<pir::SlotOp>(operation)) {
        slots[slot.getLabel()].push_back({registry::HoleSegmentSort::Value,
                                          slot.getPayloadClass(), "1",
                                          &operation});
      } else if (auto challenge = dyn_cast<pir::ChalOp>(operation)) {
        auto capability = cast<pir::ChallengeCapabilityOpInterface>(operation);
        challenges[challenge.getLabel()].push_back(
            {registry::HoleSegmentSort::Value,
             capability.getChallengePayloadClass(),
             capability.getChallengeCount(), &operation});
      }
    }

    auto kappa = container->getAttrOfType<DictionaryAttr>("kappa");
    constants = kappa ? dyn_cast_or_null<DictionaryAttr>(kappa.get("constants"))
                      : DictionaryAttr();
  }

  LogicalResult checkTopLevel() {
    for (NamedAttribute entry : routes)
      if (entry.getName() != "witnesses" && entry.getName() != "instances")
        return reject("routes has unknown section '" +
                      entry.getName().strref() +
                      "' (the closed set is witnesses, instances)");
    instances = dyn_cast_or_null<DictionaryAttr>(routes.get("instances"));
    if (!instances)
      return reject("routes needs an object section 'instances'");
    return success();
  }

  LogicalResult readWitnesses() {
    Attribute authored = routes.get("witnesses");
    if (!authored)
      return success();
    auto list = dyn_cast<ArrayAttr>(authored);
    if (!list)
      return reject(
          "routes witnesses must be an array of [label, class] pairs");
    for (auto [index, entry] : llvm::enumerate(list)) {
      auto pair = dyn_cast<ArrayAttr>(entry);
      if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
          !isa<StringAttr>(pair[1]))
        return reject("routes witness #" + Twine(index) +
                      " must be a [label, class] string pair");
      StringRef label = cast<StringAttr>(pair[0]).getValue();
      StringRef handleClass = cast<StringAttr>(pair[1]).getValue();
      if (label.empty() || handleClass.empty() ||
          !encoding::inEncodingDomain(label) ||
          !encoding::inEncodingDomain(handleClass))
        return reject("routes witness #" + Twine(index) +
                      " label and class must be non-empty printable ASCII");
      if (!witnessNames.insert(label).second)
        return reject("routes witness label '" + label + "' is duplicated");
      witnessClasses[label] = handleClass;
      graph.witnesses_.push_back({label.str(), handleClass.str()});
    }
    return success();
  }

  LogicalResult readInstances() {
    for (NamedAttribute entry : instances) {
      StringRef name = entry.getName().strref();
      if (!semantics::isRouteInstanceName(name))
        return reject("route instance '" + name +
                      "' must be a non-empty printable dotted namespace "
                      "without ':' or empty segments");
      auto authored = dyn_cast<DictionaryAttr>(entry.getValue());
      if (!authored)
        return reject("route instance '" + name + "' must be an object");
      for (NamedAttribute field : authored)
        if (field.getName() != "contract" && field.getName() != "params" &&
            field.getName() != "inputs")
          return reject("route instance '" + name + "' has unknown field '" +
                        field.getName().strref() + "'");

      auto contractId = dyn_cast_or_null<StringAttr>(authored.get("contract"));
      if (!contractId)
        return reject("route instance '" + name +
                      "' needs a string 'contract'");
      const registry::HoleContract *contract =
          vocabulary.lookupHoleContract(contractId.getValue());
      if (!contract)
        return reject("route instance '" + name + "' cites hole contract '" +
                      contractId.getValue() +
                      "' that does not resolve in the protocol vocabulary");

      DictionaryAttr parameters =
          dyn_cast_or_null<DictionaryAttr>(authored.get("params"));
      if (authored.get("params") && !parameters)
        return reject("route instance '" + name +
                      "' params must be an object of string values");
      if (failed(checkParameters(name, parameters, *contract)))
        return failure();

      size_t index = graph.instances_.size();
      instanceIndices[name] = index;
      graph.instances_.push_back({name.str(),
                                  contractId.getValue().str(),
                                  *contract,
                                  parameters,
                                  {},
                                  {}});
    }
    return success();
  }

  LogicalResult checkParameters(StringRef instance, DictionaryAttr parameters,
                                const registry::HoleContract &contract) {
    llvm::StringSet<> expected;
    for (const std::string &name : contract.parameters)
      expected.insert(name);
    for (const std::string &name : contract.semanticParameters)
      expected.insert(name);

    size_t actualSize = parameters ? parameters.size() : 0;
    if (actualSize != expected.size())
      return reject("route instance '" + instance + "' must supply exactly " +
                    Twine(expected.size()) +
                    " declared static and semantic parameter(s)");
    if (!parameters)
      return success();

    llvm::DenseSet<StringRef> semantic(contract.semanticParameters.begin(),
                                       contract.semanticParameters.end());
    for (NamedAttribute parameter : parameters) {
      StringRef name = parameter.getName().strref();
      auto value = dyn_cast<StringAttr>(parameter.getValue());
      if (!expected.contains(name))
        return reject("route instance '" + instance + "' param '" + name +
                      "' is not declared by its contract");
      if (!value || value.getValue().empty() ||
          !encoding::inEncodingDomain(value.getValue()))
        return reject("route instance '" + instance + "' param '" + name +
                      "' must be a non-empty printable string");
      if (semantic.contains(name) && !encoding::isSha256Ref(value.getValue()))
        return reject("route instance '" + instance + "' semantic param '" +
                      name + "' must be a sha256 content reference");
    }
    return success();
  }

  LogicalResult readInputs() {
    for (NamedAttribute authoredEntry : instances) {
      StringRef name = authoredEntry.getName().strref();
      auto authored = cast<DictionaryAttr>(authoredEntry.getValue());
      semantics::ConstructionGraph::Instance &instance =
          graph.instances_[instanceIndices.lookup(name)];
      auto inputs = dyn_cast_or_null<ArrayAttr>(authored.get("inputs"));
      if (!inputs)
        return reject("route instance '" + name + "' needs an array 'inputs'");

      SmallVector<const registry::HoleSegment *> routedOperands;
      for (const registry::HoleSegment &segment : instance.contract.operands)
        if (segment.sort != registry::HoleSegmentSort::Sponge)
          routedOperands.push_back(&segment);
      if (inputs.size() != routedOperands.size())
        return reject("route instance '" + name + "' supplies " +
                      Twine(inputs.size()) + " inputs, its contract '" +
                      instance.contractId + "' declares " +
                      Twine(routedOperands.size()) + " routed operand(s)");

      for (auto [index, input] : llvm::enumerate(inputs)) {
        auto text = dyn_cast<StringAttr>(input);
        std::string where =
            ("route instance '" + name + "' input #" + Twine(index)).str();
        if (!text)
          return reject(where + " must be a reference string");
        auto reference = semantics::parseRouteReference(text.getValue());
        if (!reference)
          return reject(where + ": " + toString(reference.takeError()));
        auto shape = resolveReference(*reference, where);
        if (failed(shape))
          return failure();
        if (failed(matchShape(*shape, *routedOperands[index], where)))
          return failure();
        if (shape->sort == registry::HoleSegmentSort::Handle) {
          std::string handle = semantics::printRouteReference(*reference);
          if (!handleReaders.insert(handle).second)
            return reject(where + " gives handle '" + handle +
                          "' more than one reader");
        }
        if (reference->kind == semantics::RouteReferenceKind::InstanceResult)
          instance.dependencies.push_back(reference->name);
        instance.inputs.push_back(std::move(*reference));
      }
    }
    return success();
  }

  FailureOr<ValueShape>
  resolveReference(const semantics::RouteReference &reference,
                   const Twine &where) {
    auto namedValue = [&](const auto &index,
                          StringRef noun) -> FailureOr<ValueShape> {
      auto found = index.find(reference.name);
      if (found == index.end()) {
        (void)reject(where + " references unknown " + noun + " '" +
                     reference.name + "'");
        return failure();
      }
      if (found->second.size() != 1) {
        (void)reject(where + " references ambiguous " + noun + " '" +
                     reference.name + "'");
        return failure();
      }
      return found->second.front();
    };

    switch (reference.kind) {
    case semantics::RouteReferenceKind::Bind:
      return namedValue(binds, "bind");
    case semantics::RouteReferenceKind::Slot:
      return namedValue(slots, "slot");
    case semantics::RouteReferenceKind::Challenge:
      return namedValue(challenges, "challenge");
    case semantics::RouteReferenceKind::Constant: {
      auto entry =
          constants ? constants.getNamed(reference.name) : std::nullopt;
      auto spec = entry ? dyn_cast<DictionaryAttr>(entry->getValue())
                        : DictionaryAttr();
      auto typeClass =
          spec ? dyn_cast_or_null<StringAttr>(spec.get("class")) : StringAttr();
      if (!typeClass) {
        (void)reject(where + " references unknown or untyped kappa constant '" +
                     reference.name + "'");
        return failure();
      }
      return ValueShape{registry::HoleSegmentSort::Value, typeClass.getValue(),
                        "1", nullptr};
    }
    case semantics::RouteReferenceKind::Witness: {
      auto found = witnessClasses.find(reference.name);
      if (found == witnessClasses.end()) {
        (void)reject(where + " references undeclared witness '" +
                     reference.name + "'");
        return failure();
      }
      return ValueShape{
          registry::HoleSegmentSort::Handle, found->second, {}, nullptr};
    }
    case semantics::RouteReferenceKind::InstanceResult: {
      auto found = instanceIndices.find(reference.name);
      if (found == instanceIndices.end()) {
        (void)reject(where + " references unknown instance '" + reference.name +
                     "'");
        return failure();
      }
      const registry::HoleContract &contract =
          graph.instances_[found->second].contract;
      if (reference.output >= contract.results.size()) {
        (void)reject(where + " output index is out of range for '" +
                     reference.name + "'");
        return failure();
      }
      const registry::HoleSegment &result = contract.results[reference.output];
      if (result.sort == registry::HoleSegmentSort::Sponge) {
        (void)reject(where + " routes a sponge result");
        return failure();
      }
      return ValueShape{result.sort, result.typeClass, result.count, nullptr};
    }
    }
    llvm_unreachable("closed route-reference kind");
  }

  LogicalResult matchShape(const ValueShape &actual,
                           const registry::HoleSegment &expected,
                           const Twine &where) {
    if (actual.sort != expected.sort)
      return reject(where + " sort disagrees with the contract operand");
    if (actual.typeClass != expected.typeClass)
      return reject(where + " class '" + actual.typeClass +
                    "' disagrees with the contract operand class '" +
                    expected.typeClass + "'");
    if (actual.sort == registry::HoleSegmentSort::Value &&
        actual.count != expected.count)
      return reject(where + " count '" + actual.count +
                    "' disagrees with the contract operand count '" +
                    expected.count + "'");
    return success();
  }

  LogicalResult checkAcyclic() {
    enum class Mark { White, Grey, Black };
    StringMap<Mark> marks;
    std::function<bool(StringRef)> hasCycle = [&](StringRef node) {
      Mark &mark = marks[node];
      if (mark == Mark::Grey)
        return true;
      if (mark == Mark::Black)
        return false;
      mark = Mark::Grey;
      const auto &instance = graph.instances_[instanceIndices.lookup(node)];
      for (StringRef dependency : instance.dependencies)
        if (hasCycle(dependency))
          return true;
      mark = Mark::Black;
      return false;
    };
    for (const auto &instance : graph.instances_)
      if (hasCycle(instance.name))
        return reject("route instances form a dataflow cycle through '" +
                      instance.name + "'");
    return success();
  }

  LogicalResult readSlotBindings() {
    for (Operation &operation : body) {
      auto slot = dyn_cast<pir::SlotOp>(operation);
      if (!slot || !slot.getBinding())
        continue;
      std::string where = ("slot '" + slot.getLabel() + "' binding").str();
      auto reference = semantics::parseRouteReference(*slot.getBinding());
      if (!reference)
        return reject(where + ": " + toString(reference.takeError()));
      if (reference->kind == semantics::RouteReferenceKind::Slot ||
          reference->kind == semantics::RouteReferenceKind::Challenge ||
          reference->kind == semantics::RouteReferenceKind::Witness)
        return reject(where + " must be <instance>.<index>, bind:<label>, or "
                              "const:<name>");
      auto shape = resolveReference(*reference, where);
      if (failed(shape))
        return failure();
      if (shape->sort != registry::HoleSegmentSort::Value ||
          shape->typeClass != slot.getPayloadClass() || shape->count != "1") {
        if (reference->kind == RouteReferenceKind::InstanceResult)
          return reject(where +
                        " must name a value result of the slot's payload "
                        "class");
        return reject(where +
                      " must name one value of the slot's payload class");
      }
      int64_t slotPosition = bodyPositions.lookup(slot.getOperation());
      if (reference->kind == RouteReferenceKind::Bind && shape->source &&
          bodyPositions.lookup(shape->source) >= slotPosition)
        return reject(where + " references event '" +
                      semantics::printRouteReference(*reference) +
                      "' that is not earlier than the slot");
      if (reference->kind == RouteReferenceKind::InstanceResult)
        materializationRoots.push_back({reference->name, slotPosition});
      graph.slotBindings_.try_emplace(slot.getOperation(),
                                      std::move(*reference));
    }
    return success();
  }

  Operation *eventSource(const semantics::RouteReference &reference) const {
    auto uniqueSource = [&](const auto &index) -> Operation * {
      auto found = index.find(reference.name);
      return found != index.end() && found->second.size() == 1
                 ? found->second.front().source
                 : nullptr;
    };
    switch (reference.kind) {
    case RouteReferenceKind::Bind:
      return uniqueSource(binds);
    case RouteReferenceKind::Slot:
      return uniqueSource(slots);
    case RouteReferenceKind::Challenge:
      return uniqueSource(challenges);
    case RouteReferenceKind::Constant:
    case RouteReferenceKind::Witness:
    case RouteReferenceKind::InstanceResult:
      return nullptr;
    }
    llvm_unreachable("closed route-reference kind");
  }

  LogicalResult checkEventAvailability() {
    StringMap<int64_t> firstMaterialization;
    std::function<void(StringRef, int64_t)> demand = [&](StringRef name,
                                                         int64_t position) {
      auto found = firstMaterialization.find(name);
      if (found != firstMaterialization.end() && found->second <= position)
        return;
      firstMaterialization[name] = position;
      const auto &instance = graph.instances_[instanceIndices.lookup(name)];
      for (StringRef dependency : instance.dependencies)
        demand(dependency, position);
    };
    for (const auto &[name, position] : materializationRoots)
      demand(name, position);

    for (const auto &instance : graph.instances_) {
      auto demanded = firstMaterialization.find(instance.name);
      if (demanded == firstMaterialization.end())
        continue;
      for (auto [index, input] : llvm::enumerate(instance.inputs)) {
        Operation *source = eventSource(input);
        if (!source)
          continue;
        auto sourcePosition = bodyPositions.find(source);
        if (sourcePosition == bodyPositions.end() ||
            sourcePosition->second >= demanded->second)
          return reject("route instance '" + instance.name + "' input #" +
                        Twine(index) + " references event '" +
                        semantics::printRouteReference(input) +
                        "' that is not earlier than its first "
                        "materialization point");
      }
    }
    return success();
  }

  Operation *container;
  const registry::ProtocolVocabulary &vocabulary;
  Block &body;
  DictionaryAttr routes;
  DictionaryAttr instances;
  DictionaryAttr constants;
  semantics::ConstructionGraph graph;
  StringMap<SmallVector<ValueShape, 1>> binds;
  StringMap<SmallVector<ValueShape, 1>> slots;
  StringMap<SmallVector<ValueShape, 1>> challenges;
  llvm::DenseMap<Operation *, int64_t> bodyPositions;
  llvm::StringSet<> witnessNames;
  StringMap<StringRef> witnessClasses;
  StringMap<size_t> instanceIndices;
  llvm::StringSet<> handleReaders;
  SmallVector<std::pair<std::string, int64_t>> materializationRoots;
};

} // namespace zkc::semantics::detail

FailureOr<semantics::ConstructionGraph> semantics::ConstructionGraph::build(
    Operation *container, const registry::ProtocolEnvironment &environment) {
  if (!container || container->getNumRegions() != 1 ||
      !llvm::hasSingleElement(container->getRegion(0))) {
    if (container)
      container->emitOpError()
          << "[zkc-E223] construction routes require one protocol body";
    return failure();
  }
  return detail::ConstructionGraphBuilder(container, environment).build();
}

const semantics::RouteReference *
semantics::ConstructionGraph::slotBinding(pir::SlotOp slot) const {
  auto found = slotBindings_.find(slot.getOperation());
  return found == slotBindings_.end() ? nullptr : &found->second;
}

DictionaryAttr semantics::ConstructionGraph::resolvedHoleContracts(
    MLIRContext *context) const {
  SmallVector<NamedAttribute> resolved;
  llvm::StringSet<> seen;
  for (const Instance &instance : instances_)
    if (seen.insert(instance.contractId).second)
      resolved.push_back(
          {StringAttr::get(context, instance.contractId),
           StringAttr::get(context, instance.contract.contentDigest())});
  return DictionaryAttr::get(context, resolved);
}
