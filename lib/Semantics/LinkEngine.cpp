//===- LinkEngine.cpp - route-preserving protocol composition -----------===//

#include "zkc/Semantics/LinkEngine.h"

#include "ConstructionGraph.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/TypeSwitch.h"

#include <optional>

using namespace llvm;
using namespace mlir;
using namespace zkc;

namespace {

FailureOr<DictionaryAttr> mergeKappa(pir::ProtocolOp producer,
                                     pir::ProtocolOp consumer) {
  DictionaryAttr left = producer.getKappa().value_or(DictionaryAttr());
  DictionaryAttr right = consumer.getKappa().value_or(DictionaryAttr());
  if (!left)
    return right;
  if (!right)
    return left;

  MLIRContext *context = producer.getContext();
  SmallVector<NamedAttribute> merged(left.begin(), left.end());
  for (NamedAttribute axis : right) {
    auto existing = left.getNamed(axis.getName());
    if (!existing) {
      merged.push_back(axis);
      continue;
    }

    auto leftDictionary = dyn_cast<DictionaryAttr>(existing->getValue());
    auto rightDictionary = dyn_cast<DictionaryAttr>(axis.getValue());
    if (leftDictionary && rightDictionary) {
      SmallVector<NamedAttribute> entries(leftDictionary.begin(),
                                          leftDictionary.end());
      for (NamedAttribute entry : rightDictionary) {
        auto held = leftDictionary.getNamed(entry.getName());
        if (!held) {
          entries.push_back(entry);
          continue;
        }
        if (held->getValue() != entry.getValue()) {
          producer.emitError()
              << "[zkc-E702] kappa axis '" << axis.getName().getValue()
              << "' conflicts at key '" << entry.getName().getValue()
              << "': profiles merge axis-wise and conflicts are ill-typed";
          return failure();
        }
      }
      for (auto [index, entry] : llvm::enumerate(merged))
        if (entry.getName() == axis.getName())
          merged[index] = NamedAttribute(axis.getName(),
                                         DictionaryAttr::get(context, entries));
      continue;
    }
    if (existing->getValue() != axis.getValue()) {
      producer.emitError()
          << "[zkc-E702] kappa axis '" << axis.getName().getValue()
          << "' conflicts: profiles merge axis-wise and conflicts are "
             "ill-typed";
      return failure();
    }
  }
  return DictionaryAttr::get(context, merged);
}

DictionaryAttr claimAnchors(Value claim) {
  if (auto source = claim.getDefiningOp<pir::InstantiateOp>())
    return source.getAnchors();
  if (auto reduce = claim.getDefiningOp<pir::ReduceOp>()) {
    ArrayAttr outAnchors = reduce.getOutAnchors().value_or(ArrayAttr());
    for (auto [index, out] : llvm::enumerate(reduce.getOuts()))
      if (out == claim && outAnchors && index < outAnchors.size())
        return dyn_cast<DictionaryAttr>(outAnchors[index]);
  }
  return DictionaryAttr();
}

semantics::RouteReference qualify(semantics::RouteReference reference,
                                  StringRef prefix) {
  if (reference.kind != semantics::RouteReferenceKind::Constant)
    reference.name = (prefix + "." + reference.name).str();
  return reference;
}

DictionaryAttr buildRoutes(MLIRContext *context, bool authoredRoutes,
                           const semantics::ConstructionGraph &producer,
                           const semantics::ConstructionGraph &consumer,
                           StringRef producerPrefix, StringRef consumerPrefix) {
  if (!authoredRoutes)
    return DictionaryAttr();

  Builder builder(context);
  SmallVector<Attribute> witnesses;
  auto appendWitnesses = [&](const semantics::ConstructionGraph &graph,
                             StringRef prefix) {
    for (const auto &witness : graph.witnesses()) {
      SmallVector<Attribute, 2> pair = {
          builder.getStringAttr((prefix + "." + witness.label).str()),
          builder.getStringAttr(witness.handleClass)};
      witnesses.push_back(builder.getArrayAttr(pair));
    }
  };
  appendWitnesses(producer, producerPrefix);
  appendWitnesses(consumer, consumerPrefix);

  SmallVector<NamedAttribute> instances;
  auto appendInstances = [&](const semantics::ConstructionGraph &graph,
                             StringRef prefix) {
    for (const auto &instance : graph.instances()) {
      SmallVector<Attribute> inputs;
      inputs.reserve(instance.inputs.size());
      for (const semantics::RouteReference &input : instance.inputs)
        inputs.push_back(builder.getStringAttr(
            semantics::printRouteReference(qualify(input, prefix))));

      SmallVector<NamedAttribute> fields = {
          builder.getNamedAttr("contract",
                               builder.getStringAttr(instance.contractId)),
          builder.getNamedAttr("inputs", builder.getArrayAttr(inputs))};
      if (instance.parameters)
        fields.push_back(builder.getNamedAttr("params", instance.parameters));
      instances.push_back(
          builder.getNamedAttr((prefix + "." + instance.name).str(),
                               builder.getDictionaryAttr(fields)));
    }
  };
  appendInstances(producer, producerPrefix);
  appendInstances(consumer, consumerPrefix);

  SmallVector<NamedAttribute> sections = {
      builder.getNamedAttr("instances", builder.getDictionaryAttr(instances))};
  if (!witnesses.empty())
    sections.push_back(
        builder.getNamedAttr("witnesses", builder.getArrayAttr(witnesses)));
  return builder.getDictionaryAttr(sections);
}

void prefixNames(Operation *original, Operation *clone, StringRef prefix,
                 const semantics::ConstructionGraph &routes) {
  auto prefixed = [&](StringRef name) { return (prefix + "." + name).str(); };
  auto prefixChecks = [&](DictionaryAttr selected) {
    SmallVector<NamedAttribute> checks;
    checks.reserve(selected.size());
    for (NamedAttribute check : selected)
      checks.emplace_back(
          check.getName(),
          StringAttr::get(
              clone->getContext(),
              prefixed(cast<StringAttr>(check.getValue()).getValue())));
    return DictionaryAttr::get(clone->getContext(), checks);
  };

  llvm::TypeSwitch<Operation *>(clone)
      .Case<pir::InstantiateOp>(
          [&](auto op) { op.setLabel(prefixed(op.getLabel())); })
      .Case<pir::BindOp>([&](auto op) {
              op.setLabel(prefixed(op.getLabel()));
              // A binding fills a contract role the same way a slot does, so
              // its membership instance is a reduce label and is renamed with
              // the rest of them.
              if (op.getInstance())
                op.setInstance(prefixed(*op.getInstance()));
            })
      .Case<pir::SlotOp>([&](auto op) {
        op.setLabel(prefixed(op.getLabel()));
        if (op.getInstance())
          op.setInstance(prefixed(*op.getInstance()));
        if (const auto *binding =
                routes.slotBinding(cast<pir::SlotOp>(original)))
          op.setBindingAttr(StringAttr::get(
              clone->getContext(),
              semantics::printRouteReference(qualify(*binding, prefix))));
      })
      .Case<pir::ChalOp>([&](auto op) {
        op.setLabel(prefixed(op.getLabel()));
        op.setDomain(prefixed(op.getDomain()));
      })
      .Case<pir::CheckOp>(
          [&](auto op) { op.setLabel(prefixed(op.getLabel())); })
      .Case<pir::ReduceOp>([&](auto op) {
        op.setLabel(prefixed(op.getLabel()));
        op.setChecksAttr(prefixChecks(op.getChecks()));
      })
      .Case<pir::DischargeOp>(
          [&](auto op) { op.setChecksAttr(prefixChecks(op.getChecks())); })
      .Default([](Operation *) {});
}

} // namespace

FailureOr<pir::ProtocolOp>
semantics::LinkEngine::link(pir::ProtocolOp producer, pir::ProtocolOp consumer,
                            StringRef producerPrefix,
                            StringRef consumerPrefix) const {
  auto dottedPrefixOf = [](StringRef prefix, StringRef candidate) {
    return candidate.starts_with((prefix + ".").str());
  };
  if (producerPrefix.empty() || consumerPrefix.empty() ||
      producerPrefix == consumerPrefix ||
      dottedPrefixOf(producerPrefix, consumerPrefix) ||
      dottedPrefixOf(consumerPrefix, producerPrefix)) {
    producer.emitError()
        << "[zkc-E703] face prefixes namespace labels and challenge domains; "
           "they must be non-empty and neither equal nor a dotted prefix of "
           "the other, got '"
        << producerPrefix << "' and '" << consumerPrefix << "'";
    return failure();
  }

  auto producerRoutes = detail::judgeOpenProtocol(producer, environment_);
  auto consumerRoutes = detail::judgeOpenProtocol(consumer, environment_);
  if (failed(producerRoutes) || failed(consumerRoutes))
    return failure();

  encoding::CanonicalIndex producerEventIndex =
      encoding::canonicalEventIndex(producer.getBody().front());
  encoding::CanonicalIndex consumerEventIndex =
      encoding::canonicalEventIndex(consumer.getBody().front());

  auto kappa = mergeKappa(producer, consumer);
  if (failed(kappa))
    return failure();

  llvm::DenseSet<Operation *> fusedExports;
  llvm::DenseMap<Operation *, Value> fusedSources;
  llvm::DenseSet<Operation *> takenSources;
  for (auto exportOp : producer.getBody().front().getOps<pir::ExportOp>()) {
    Value claim = exportOp.getClaim();
    StringRef profile = cast<pir::ClaimType>(claim.getType()).getProfile();
    DictionaryAttr anchors = claimAnchors(claim);
    SmallVector<pir::InstantiateOp> matches;
    for (auto source :
         consumer.getBody().front().getOps<pir::InstantiateOp>()) {
      if (takenSources.contains(source))
        continue;
      StringRef sourceProfile =
          cast<pir::ClaimType>(source.getClaim().getType()).getProfile();
      if (sourceProfile == profile && source.getAnchors() == anchors)
        matches.push_back(source);
    }
    if (matches.empty()) {
      exportOp.emitOpError()
          << "[zkc-E705] exported claim with profile '" << profile
          << "' finds no consumer source with its exact descriptor; the "
             "consumer never declared this producer face";
      return failure();
    }
    if (matches.size() > 1) {
      exportOp.emitOpError()
          << "[zkc-E706] exported claim with profile '" << profile
          << "' matches " << matches.size()
          << " consumer sources with one descriptor; no fact decides which "
             "face receives it";
      return failure();
    }
    fusedExports.insert(exportOp);
    fusedSources[matches.front()] = claim;
    takenSources.insert(matches.front());
  }

  int64_t producerEvents = encoding::canonicalEventCount(producerEventIndex);
  int64_t consumerEvents = encoding::canonicalEventCount(consumerEventIndex);
  SmallVector<int64_t> segments;
  if (auto starts = producer.getSegments())
    segments.assign(starts->begin(), starts->end());
  // Segment starts denote non-empty event runs and must lie strictly inside
  // the composite spine. An operand with no events contributes no run and
  // therefore no splice position.
  if (producerEvents != 0 && consumerEvents != 0)
    segments.push_back(producerEvents);
  if (auto starts = consumer.getSegments())
    for (int64_t start : *starts)
      segments.push_back(start + producerEvents);
  std::optional<ArrayRef<int64_t>> composedSegments;
  if (!segments.empty())
    composedSegments = segments;

  bool hasRoutes =
      producer.getRoutes().has_value() || consumer.getRoutes().has_value();
  DictionaryAttr composedRoutes =
      buildRoutes(producer.getContext(), hasRoutes, *producerRoutes,
                  *consumerRoutes, producerPrefix, consumerPrefix);

  OpBuilder builder(consumer);
  builder.setInsertionPointAfter(consumer);
  auto composite = pir::ProtocolOp::create(
      builder, consumer.getLoc(),
      ("link(" + producer.getProtocolName() + "," + consumer.getProtocolName() +
       ")")
          .str(),
      *kappa, /*vocab=*/DictionaryAttr(), composedRoutes, composedSegments,
      consumer.getPolicy());
  llvm::scope_exit rollback([&] { composite.erase(); });

  Block &body = composite.getBody().emplaceBlock();
  builder.setInsertionPointToStart(&body);
  IRMapping map;
  Value thread;

  auto cloneMembers = [&](pir::ProtocolOp from, StringRef prefix,
                          const ConstructionGraph &routes,
                          llvm::function_ref<bool(Operation &)> take) {
    for (Operation &operation : from.getBody().front()) {
      if (!take(operation))
        continue;
      Operation *clone = builder.clone(operation, map);
      prefixNames(&operation, clone, prefix, routes);
      if (auto member = dyn_cast<pir::ProtocolMemberOpInterface>(clone))
        if (Value out = member.getThreadOut())
          thread = out;
    }
  };
  auto isEvent = [](const encoding::CanonicalIndex &index,
                    Operation &operation) {
    return encoding::canonicalEventPosition(index, &operation).has_value();
  };

  cloneMembers(
      producer, producerPrefix, *producerRoutes,
      [](Operation &operation) { return isa<pir::InstantiateOp>(operation); });
  for (auto source : consumer.getBody().front().getOps<pir::InstantiateOp>()) {
    if (fusedSources.contains(source))
      continue;
    Operation *clone = builder.clone(*source.getOperation(), map);
    prefixNames(source, clone, consumerPrefix, *consumerRoutes);
  }

  auto begin = pir::BeginOp::create(builder, composite.getLoc());
  thread = begin.getOut();
  for (Operation &operation : producer.getBody().front())
    if (auto producerBegin = dyn_cast<pir::BeginOp>(&operation))
      map.map(producerBegin.getOut(), thread);
  cloneMembers(producer, producerPrefix, *producerRoutes,
               [&](Operation &operation) {
                 return isEvent(producerEventIndex, operation);
               });
  for (Operation &operation : consumer.getBody().front())
    if (auto consumerBegin = dyn_cast<pir::BeginOp>(&operation))
      map.map(consumerBegin.getOut(), thread);
  cloneMembers(consumer, consumerPrefix, *consumerRoutes,
               [&](Operation &operation) {
                 return isEvent(consumerEventIndex, operation);
               });
  pir::EndOp::create(builder, composite.getLoc(), thread);

  cloneMembers(
      producer, producerPrefix, *producerRoutes,
      [](Operation &operation) { return isa<pir::ReduceOp>(operation); });
  for (auto &[source, producerClaim] : fusedSources)
    map.map(cast<pir::InstantiateOp>(source).getClaim(),
            map.lookup(producerClaim));
  cloneMembers(
      consumer, consumerPrefix, *consumerRoutes,
      [](Operation &operation) { return isa<pir::ReduceOp>(operation); });

  llvm::DenseMap<StringRef, Value> valueBySemanticRef;
  llvm::DenseMap<Value, StringRef> semanticRefByValue;
  auto cloneMaterialBindings = [&](pir::ProtocolOp from) {
    for (auto binding : from.getBody().front().getOps<pir::MaterialBindOp>()) {
      Value value = map.lookupOrNull(binding.getValue());
      if (!value) {
        binding.emitError()
            << "[zkc-E704] link cannot rewrite the material-binding endpoint";
        return failure();
      }
      StringRef semanticRef = binding.getSemanticRef();
      if (auto held = valueBySemanticRef.find(semanticRef);
          held != valueBySemanticRef.end()) {
        if (held->second != value) {
          binding.emitError()
              << "[zkc-E704] semantic reference '" << semanticRef
              << "' reaches two distinct value endpoints after link";
          return failure();
        }
        continue;
      }
      if (auto held = semanticRefByValue.find(value);
          held != semanticRefByValue.end() && held->second != semanticRef) {
        binding.emitError()
            << "[zkc-E704] one value endpoint is bound to both '"
            << held->second << "' and '" << semanticRef << "'";
        return failure();
      }
      pir::MaterialBindOp::create(builder, binding.getLoc(), value,
                                  semanticRef);
      valueBySemanticRef[semanticRef] = value;
      semanticRefByValue[value] = semanticRef;
    }
    return success();
  };
  if (failed(cloneMaterialBindings(producer)) ||
      failed(cloneMaterialBindings(consumer)))
    return failure();

  cloneMembers(producer, producerPrefix, *producerRoutes,
               [&](Operation &operation) {
                 return isa<pir::DischargeOp, pir::ExportOp, pir::AssumeOp,
                            pir::ResidualOp>(operation) &&
                        !fusedExports.contains(&operation);
               });
  cloneMembers(consumer, consumerPrefix, *consumerRoutes,
               [](Operation &operation) {
                 return isa<pir::DischargeOp, pir::ExportOp, pir::AssumeOp,
                            pir::ResidualOp>(operation);
               });

  if (failed(detail::judgeOpenProtocol(composite, environment_)))
    return failure();

  rollback.release();
  return composite;
}
