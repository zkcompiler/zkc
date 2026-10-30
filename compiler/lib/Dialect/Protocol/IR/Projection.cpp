#include "zkc/Analysis/Finite.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "mathematical-projection",
                           detail);
}
bool keys(DictionaryAttr record, ArrayRef<StringRef> names) {
  return record && record.size() == names.size() &&
         all_of(record, [&](NamedAttribute attr) {
           return is_contained(names, attr.getName().getValue());
         });
}
bool dataType(Type type, NativeTypePolicies &types) {
  return bool(types.get(type));
}
bool portType(Type type, NativeTypePolicies &types) {
  auto policy = types.get(type);
  return policy && policy->protocolPort;
}
Type logicalType(Type type) {
  if (auto physical = dyn_cast<runtime::RepresentedType>(type))
    return physical.getLogical();
  return type;
}
std::optional<unsigned> index(Attribute attr, unsigned size) {
  auto value = dyn_cast_or_null<IntegerAttr>(attr);
  if (!value || !value.getType().isSignlessInteger(64) ||
      value.getValue().isNegative() || value.getValue().uge(size))
    return std::nullopt;
  return static_cast<unsigned>(value.getInt());
}
bool roleSets(ArrayAttr sets, unsigned count, ArrayAttr roles) {
  if (!sets || sets.size() != count)
    return false;
  for (auto item : sets) {
    auto set = dyn_cast<ArrayAttr>(item);
    if (!set || set.empty())
      return false;
    llvm::DenseSet<Attribute> seen;
    for (auto role : set)
      if (!is_contained(roles, role) || !seen.insert(role).second)
        return false;
  }
  return true;
}
struct MetadataVerifier {
  protocol_ir::ProjectionOp record;
  protocol_ir::ProtocolModuleOp unit;
  SymbolTableCollection &tables;
  NativeTypePolicies &types;
  llvm::DenseSet<Attribute> authoredCallees;
  llvm::DenseMap<std::pair<Attribute, Attribute>, StringAttr> queryPorts;
  llvm::DenseSet<Operation *> seenParticipants, entries;
  unsigned remaining = 1000000;
  std::optional<protocol::SourceExecutionClosure> closure;
  using Occurrences =
      llvm::DenseMap<Attribute, std::pair<unsigned, Operation *>>;
  llvm::DenseMap<Operation *, Occurrences> occurrences;
  llvm::DenseSet<std::pair<Operation *, Attribute>> retainedActions;
  llvm::DenseSet<std::pair<Operation *, Attribute>> requiredCalculations;
  MetadataVerifier(protocol_ir::ProjectionOp record,
                   protocol_ir::ProtocolModuleOp unit,
                   SymbolTableCollection &tables, NativeTypePolicies &types)
      : record(record), unit(unit), tables(tables), types(types) {}
  LogicalResult charge(uint64_t work) {
    if (work > remaining)
      return refuse(record, "projection metadata work limit");
    remaining -= work;
    return success();
  }

  LogicalResult execution() {
    if (closure)
      return success();
    auto value = unit.getProfile() == protocol_ir::Profile::Physical
                     ? protocol::readExecutionClosure(unit, true)
                     : protocol::readSourceExecutionClosure(unit);
    if (!value)
      return diagnostics::emit(record.emitOpError(), value.takeError());
    closure = std::move(*value);
    return success();
  }
  LogicalResult checkTranscriptHelper(func::FuncOp function) {
    if (failed(execution()))
      return failure();
    auto found = closure->bodies.find(function.getSymName().str());
    if (found == closure->bodies.end())
      return refuse(record, "invalid inserted transcript helper");
    const auto &body = found->second;
    auto arguments = function.getArguments().drop_front();
    const protocol::SourceExecutionStep *transition = nullptr;
    Value coordinates, bound;
    SmallVector<Value> indices;
    for (const auto &step : body) {
      auto &op = *step.operation;
      ValueRange inputs(step.inputs), outputs(step.outputs);
      if (failed(charge(1)))
        return failure();
      if (isa<runtime::ReleaseBindingsOp>(op)) {
        if (any_of(inputs, [&](Value value) {
              return isa<runtime::CapabilityType>(logicalType(value.getType()));
            }))
          return refuse(record, "invalid inserted transcript helper");
        continue;
      }
      if (isa<exec::ReturnOp, exec::CompleteOp>(op)) {
        if (!transition || &step != &body.back() ||
            !llvm::equal(inputs, transition->outputs))
          return refuse(record, "invalid inserted transcript helper");
        continue;
      }
      auto binding = op.getAttrOfType<FlatSymbolRefAttr>("binding");
      auto declaration =
          binding
              ? tables.lookupNearestSymbolFrom<runtime::BindingOp>(&op, binding)
              : runtime::BindingOp();
      if (transition || !declaration)
        return refuse(record, "invalid inserted transcript helper");
      auto contract = declaration.getContract();
      if (!isa<exec::ApplyOp>(op))
        return refuse(record, "invalid inserted transcript helper");
      // A UniformIndex helper first materializes its static domain.
      if (contract == "index.constant" && !bound && !coordinates &&
          inputs.size() == 0 && outputs.size() == 1) {
        auto parameters = op.getAttrOfType<ArrayAttr>("parameters");
        auto value = parameters && parameters.size() == 1
                         ? dyn_cast<StringAttr>(parameters[0])
                         : StringAttr();
        if (!value || !protocol::parseUniformIndexBound(value.getValue()))
          return refuse(record, "invalid inserted transcript helper");
        bound = outputs[0];
        continue;
      }
      if (contract == "indices.empty" && !coordinates && inputs.size() == 0 &&
          outputs.size() == 1) {
        coordinates = outputs[0];
        continue;
      }
      if (contract == "indices.append" && coordinates && inputs.size() == 2 &&
          inputs[0] == coordinates && outputs.size() == 1) {
        indices.push_back(inputs[1]);
        coordinates = outputs[0];
        continue;
      }
      bool index = contract == "transcript.native.indexed.index";
      if ((contract != "transcript.native.indexed.challenge" &&
           contract != "transcript.native.indexed.observe.data" && !index) ||
          !coordinates || index != bool(bound))
        return refuse(record, "invalid inserted transcript helper");
      unsigned ordinary = contract.ends_with(".observe.data") ? 2 : 1;
      {
        if (inputs.size() != ordinary + unsigned(index) + 1 ||
            (index && inputs[1] != bound) || inputs.back() != coordinates ||
            arguments.size() != ordinary + indices.size() ||
            !llvm::equal(inputs.take_front(ordinary),
                         arguments.take_front(ordinary)) ||
            !llvm::equal(indices, arguments.drop_front(ordinary)) ||
            any_of(indices, [&](Value value) {
              return !logicalType(value.getType()).isUnsignedInteger(64);
            }))
          return refuse(record, "invalid inserted transcript coordinates");
      }
      transition = &step;
    }
    if (!transition || body.empty() ||
        !isa<exec::ReturnOp, exec::CompleteOp>(body.back().operation))
      return refuse(record, "invalid inserted transcript helper");
    return success();
  }

  LogicalResult checkInterface(DictionaryAttr interface) {
    auto construction =
        interface ? interface.getAs<DictionaryAttr>("construction")
                  : DictionaryAttr();
    NamedAttrList original(interface ? interface.getValue()
                                     : ArrayRef<NamedAttribute>{});
    original.erase("construction");
    if ((interface && interface.get("construction") && !construction) ||
        !keys(original.getDictionary(record.getContext()),
              {"source", "entry", "original_type", "roles", "input_roles",
               "output_roles", "statements", "participants", "actions"}))
      return refuse(record, "invalid retained interface fields");
    auto source = interface.getAs<StringAttr>("source");
    auto ref = interface.getAs<FlatSymbolRefAttr>("entry");
    auto entry =
        ref ? tables.lookupNearestSymbolFrom<protocol_ir::ProtocolEntryOp>(
                  record, ref)
            : protocol_ir::ProtocolEntryOp();
    auto typeAttr = interface.getAs<TypeAttr>("original_type");
    auto type =
        typeAttr ? dyn_cast<FunctionType>(typeAttr.getValue()) : FunctionType();
    auto roles = interface.getAs<ArrayAttr>("roles");
    auto inputs = interface.getAs<ArrayAttr>("input_roles");
    auto outputs = interface.getAs<ArrayAttr>("output_roles");
    auto participants = interface.getAs<ArrayAttr>("participants");
    auto statements = interface.getAs<ArrayAttr>("statements");
    auto actions = interface.getAs<ArrayAttr>("actions");
    if (!source || source.getValue().empty() || !entry ||
        !entries.insert(entry).second || !type || !roles || roles.empty() ||
        !participants || participants.size() != roles.size() || !statements ||
        !actions || !roleSets(inputs, type.getNumInputs(), roles) ||
        !roleSets(outputs, type.getNumResults(), roles))
      return refuse(record, "invalid original interface or entry reference");
    if (failed(charge(uint64_t(roles.size()) * (uint64_t(type.getNumInputs()) +
                                                type.getNumResults() + 1))))
      return failure();
    llvm::DenseSet<Attribute> roleNames;
    for (auto role : roles)
      if (!isa<StringAttr>(role) || cast<StringAttr>(role).getValue().empty() ||
          !roleNames.insert(role).second)
        return refuse(record, "invalid original role roster");
    for (auto t : type.getInputs())
      if (!portType(t, types) && !isa<protocol_ir::ServiceReferenceType>(t))
        return refuse(record, "unsupported original input type");
    for (auto t : type.getResults())
      if (!portType(t, types))
        return refuse(record, "unsupported original result type");
    for (auto [t, owners] : zip(type.getInputs(), inputs)) {
      auto policy = types.get(t);
      if ((!policy || !policy->shared) && cast<ArrayAttr>(owners).size() != 1)
        return refuse(record, "owner-local input has multiple roles");
    }
    for (auto [t, owners] : zip(type.getResults(), outputs)) {
      auto policy = types.get(t);
      if ((!policy || !policy->shared) && cast<ArrayAttr>(owners).size() != 1)
        return refuse(record, "owner-local result has multiple roles");
    }
    SmallVector<Type> stateTypes;
    bool hostRoot = false, programmable = false;
    llvm::DenseSet<Attribute> constructionHelpers, codecHelpers;
    StringAttr codecProducer, codecValidator;
    llvm::DenseSet<unsigned> removedServices;
    ArrayAttr constructedActions;
    if (construction) {
      auto format = construction.getAs<StringAttr>("format");
      auto states = construction.getAs<ArrayAttr>("state");
      auto root = construction.getAs<StringAttr>("root");
      auto plan = construction.getAs<StringAttr>("plan");
      auto helpers = construction.getAs<ArrayAttr>("helpers");
      auto removed = construction.getAs<ArrayAttr>("removed_services");
      constructedActions = construction.getAs<ArrayAttr>("actions");
      auto codec = construction.getAs<DictionaryAttr>("codec");
      NamedAttrList core(construction);
      core.erase("codec");
      if ((construction.get("codec") && !codec) ||
          !keys(core.getDictionary(record.getContext()),
                {"format", "state", "root", "plan", "helpers",
                 "removed_services", "actions"}) ||
          !format || format.getValue() != "zkc.native-construction/0" ||
          !states || states.size() > 1024 || !root ||
          (root.getValue() != "host" && root.getValue() != "local") || !plan ||
          !helpers || helpers.size() > 16384 || !removed || removed.empty() ||
          removed.size() > type.getNumInputs() || !constructedActions)
        return refuse(record, "invalid native construction mapping");
      hostRoot = root.getValue() == "host";
      programmable = !plan.empty();
      for (auto item : states) {
        auto state = dyn_cast<TypeAttr>(item);
        if (!state)
          return refuse(record, "invalid construction state slot");
        auto logical = protocol::encodeBoundType(state.getValue(), false);
        if (!logical) {
          consumeError(logical.takeError());
          return refuse(record, "invalid construction state slot");
        }
        if (!hostRoot && (!protocol::duplicable(*logical) ||
                          !protocol::discardable(*logical)))
          return refuse(record,
                        "local construction state requires Copy and Drop");
        stateTypes.push_back(state.getValue());
      }
      if (hostRoot) {
        auto capability =
            stateTypes.size() == 1
                ? dyn_cast<runtime::CapabilityType>(stateTypes.front())
                : runtime::CapabilityType();
        if (!capability ||
            capability.getKind() != runtime::CapabilityKind::Transcript ||
            protocol::nativeChallengeField(capability.getIdentity()).empty())
          return refuse(record, "unsupported constructed transcript type");
      } else if (!programmable) {
        return refuse(record, "local root requires an explicit construction");
      }
      for (auto item : helpers) {
        auto ref = dyn_cast<FlatSymbolRefAttr>(item);
        if (!ref || !constructionHelpers.insert(ref).second ||
            !protocol::scopedDataSignature(
                tables.lookupNearestSymbolFrom<func::FuncOp>(record, ref)))
          return refuse(record, "invalid construction helper selection");
      }
      if (codec) {
        codecProducer = codec.getAs<StringAttr>("producer");
        codecValidator = codec.getAs<StringAttr>("validator");
        auto helpers = codec.getAs<ArrayAttr>("helpers");
        if (!keys(codec, {"producer", "validator", "helpers"}) ||
            !codecProducer || !codecValidator ||
            codecProducer == codecValidator ||
            !is_contained(roles, codecProducer) ||
            !is_contained(roles, codecValidator) || !helpers ||
            helpers.empty() || helpers.size() > 14336 || !programmable)
          return refuse(record, "invalid record codec mapping");
        for (auto helper : helpers)
          if (!constructionHelpers.contains(helper) ||
              !codecHelpers.insert(helper).second)
            return refuse(record, "invalid codec helper selection");
      }
      std::optional<unsigned> previousService;
      for (auto item : removed) {
        auto port = index(item, type.getNumInputs());
        if (!port || (previousService && *previousService >= *port) ||
            !isa<protocol_ir::ServiceReferenceType>(type.getInput(*port)) ||
            !removedServices.insert(*port).second)
          return refuse(record, "invalid removed source service");
        previousService = *port;
      }
      // Original actions remain source records. Only the actual action map is
      // resolved against the transformed body. Source-relative construction
      // checking independently compares the retained original records.
      llvm::StringSet<> sourceSites;
      auto originalActions = [&](auto &&self, ArrayAttr sequence,
                                 unsigned depth) -> LogicalResult {
        if (depth > 64)
          return refuse(record, "projection region depth exceeds 64");
        for (auto item : sequence) {
          if (failed(charge(1)))
            return failure();
          auto action = dyn_cast<DictionaryAttr>(item);
          auto kind = action ? action.getAs<StringAttr>("kind") : StringAttr();
          auto site = action ? action.getAs<StringAttr>("site") : StringAttr();
          auto targets =
              action ? action.getAs<ArrayAttr>("targets") : ArrayAttr();
          bool call = kind && kind.getValue() == "protocol.local_call";
          bool exchange = kind && kind.getValue() == "protocol.exchange";
          bool loop = kind && kind.getValue() == "protocol.repeat";
          bool start = kind && kind.getValue() == "protocol.construction_start";
          if (!kind || !site || site.getValue().empty() ||
              !sourceSites.insert(site.getValue()).second || !targets ||
              (loop ? targets.empty() || targets.size() > 2
                    : targets.size() != (exchange || start ? 2u : 1u)) ||
              (kind.getValue() != "protocol.query" &&
               kind.getValue() != "protocol.guard" &&
               kind.getValue() != "protocol.finish_if" && !call && !exchange &&
               !loop && !start) ||
              !(call   ? keys(action, {"site", "kind", "targets", "callee"})
                : loop ? keys(action,
                              {"site", "kind", "targets", "maximum", "body"})
                : kind.getValue() == "protocol.query"
                    ? keys(action, {"site", "kind", "targets", "service"})
                    : keys(action, {"site", "kind", "targets"})))
            return refuse(record, "invalid original construction action");
          if (kind.getValue() == "protocol.query") {
            auto authority = index(action.get("service"), type.getNumInputs());
            if (!authority || !isa<protocol_ir::ServiceReferenceType>(
                                  type.getInput(*authority)))
              return refuse(record, "invalid original query authority");
            auto owner = cast<ArrayAttr>(inputs[*authority]);
            auto target = dyn_cast<DictionaryAttr>(targets[0]);
            if (!target || owner.size() != 1 ||
                !any_of(participants, [&](Attribute item) {
                  auto port = dyn_cast<DictionaryAttr>(item);
                  return port &&
                         port.get("participant") == target.get("participant") &&
                         port.get("role") == owner[0];
                }))
              return refuse(record, "original query authority owner differs");
          }
          if (loop) {
            auto body = action.getAs<ArrayAttr>("body");
            if (!body || !index(action.get("maximum"), 1048577) ||
                failed(self(self, body, depth + 1)))
              return refuse(record, "invalid original construction loop");
          }
          if (call && !action.getAs<FlatSymbolRefAttr>("callee"))
            return refuse(record, "invalid original local callee");
          llvm::DenseSet<Attribute> owners;
          for (auto item : targets) {
            auto target = dyn_cast<DictionaryAttr>(item);
            auto ref = target ? target.getAs<FlatSymbolRefAttr>("participant")
                              : FlatSymbolRefAttr();
            auto operation =
                target ? target.getAs<StringAttr>("operation") : StringAttr();
            if (!keys(target, {"participant", "operation"}) || !ref ||
                !operation || !owners.insert(ref).second ||
                !any_of(participants,
                        [&](Attribute p) {
                          auto port = dyn_cast<DictionaryAttr>(p);
                          return port && port.get("participant") == ref;
                        }) ||
                (exchange ? operation.getValue() != "protocol.send" &&
                                operation.getValue() != "protocol.receive"
                 : call   ? operation.getValue() != "protocol.local_call"
                 : loop   ? operation.getValue() != "protocol.loop"
                 : start ? operation.getValue() != "protocol.construction_start"
                 : kind.getValue() == "protocol.query"
                     ? operation.getValue() != "protocol.service_query"
                 : kind.getValue() == "protocol.finish_if"
                     ? operation.getValue() != "protocol.finish_if"
                     : operation.getValue() != "protocol.guard"))
              return refuse(record, "invalid original construction target");
          }
        }
        return success();
      };
      if (failed(originalActions(originalActions, actions, 0)))
        return failure();
    }
    Builder builder(record.getContext());
    SmallVector<Attribute> targets;
    llvm::DenseMap<Attribute, protocol_ir::ParticipantOp> byReference;
    for (auto [role, item] : zip(roles, participants)) {
      if (!remaining--)
        return refuse(record, "projection metadata work limit");
      auto port = dyn_cast<DictionaryAttr>(item);
      if (!keys(port, {"participant", "role", "inputs", "service_inputs",
                       "outputs"}) ||
          port.get("role") != role)
        return refuse(record, "invalid participant mapping");
      auto participantRef = port.getAs<FlatSymbolRefAttr>("participant");
      auto participant =
          participantRef
              ? tables.lookupNearestSymbolFrom<protocol_ir::ParticipantOp>(
                    record, participantRef)
              : protocol_ir::ParticipantOp();
      if (!participant || participant->getParentOp() != unit ||
          participant.getRoleAttr() != role ||
          participant.getInstanceAttr() != source ||
          !seenParticipants.insert(participant).second)
        return refuse(record,
                      "participant symbol does not match original role");
      byReference[participantRef] = participant;
      auto &indexed = occurrences[participant];
      unsigned ordinal = 0;
      auto indexedBody =
          participant.walk<WalkOrder::PreOrder>([&](Operation *op) {
            if (op == participant.getOperation())
              return WalkResult::advance();
            if (failed(charge(1)))
              return WalkResult::interrupt();
            ++ordinal;
            if (auto site = op->getAttrOfType<StringAttr>("site"))
              if (!indexed.try_emplace(site, ordinal, op).second) {
                (void)refuse(record, "ambiguous participant occurrence");
                return WalkResult::interrupt();
              }
            return WalkResult::advance();
          });
      if (indexedBody.wasInterrupted())
        return failure();
      targets.push_back(builder.getArrayAttr({role, participantRef}));
      SmallVector<Attribute> dataPorts, servicePorts, results, actualServices;
      SmallVector<Type> inputTypes, resultTypes;
      unsigned ingress = 0, removedBefore = 0;
      for (auto [i, set] : enumerate(inputs)) {
        if (!is_contained(cast<ArrayAttr>(set), role))
          continue;
        if (auto service =
                dyn_cast<protocol_ir::ServiceReferenceType>(type.getInput(i))) {
          if (cast<ArrayAttr>(set).size() != 1 ||
              protocol::randomServiceField(service.getContract()).empty())
            return refuse(record, "invalid service owner or contract");
          servicePorts.push_back(builder.getI64IntegerAttr(i));
          if (!removedServices.contains(i)) {
            auto name =
                builder.getStringAttr("service_" + std::to_string(ingress));
            queryPorts[{participantRef, builder.getI64IntegerAttr(i)}] = name;
            actualServices.push_back(builder.getArrayAttr(
                {name, builder.getStringAttr(service.getContract()),
                 builder.getI64IntegerAttr(ingress - removedBefore)}));
          } else {
            ++removedBefore;
          }
        } else {
          dataPorts.push_back(builder.getI64IntegerAttr(i));
          inputTypes.push_back(type.getInput(i));
        }
        ++ingress;
      }
      for (auto [i, set] : enumerate(outputs))
        if (is_contained(cast<ArrayAttr>(set), role)) {
          results.push_back(builder.getI64IntegerAttr(i));
          resultTypes.push_back(type.getResult(i));
        }
      if (hostRoot)
        append_range(inputTypes, stateTypes);
      append_range(resultTypes, stateTypes);
      if (role == codecProducer || role == codecValidator) {
        auto bytes =
            protocol::decodeBoundType(builder.getContext(), {"bytes", {}, {}});
        if (!bytes)
          return refuse(record, "codec requires an installed Bytes type");
        if (role == codecProducer)
          resultTypes.push_back(bytes);
        else
          inputTypes.push_back(bytes);
      }
      auto participantType = participant.getFunctionType();
      auto matches = [](ArrayRef<Type> expected, ArrayRef<Type> actual) {
        return expected.size() == actual.size() &&
               all_of(zip(expected, actual), [](auto pair) {
                 return std::get<0>(pair) == logicalType(std::get<1>(pair));
               });
      };
      auto installedServices =
          participant->getAttrOfType<ArrayAttr>("service_ports");
      if (port.get("inputs") != builder.getArrayAttr(dataPorts) ||
          port.get("service_inputs") != builder.getArrayAttr(servicePorts) ||
          port.get("outputs") != builder.getArrayAttr(results) ||
          !matches(inputTypes, participantType.getInputs()) ||
          !matches(resultTypes, participantType.getResults()) ||
          (actualServices.empty()
               ? bool(installedServices && !installedServices.empty())
               : installedServices != builder.getArrayAttr(actualServices)))
        return refuse(record,
                      "retained ports do not match participant signature");
    }
    if (entry.getTargets() != builder.getArrayAttr(targets))
      return refuse(record, "entry does not match retained participants");
    for (auto item : statements) {
      if (!remaining--)
        return refuse(record, "projection metadata work limit");
      auto statement = dyn_cast<DictionaryAttr>(item);
      if (!keys(statement,
                {"relation", "relation_type", "relation_kind", "relation_key",
                 "relation_revision", "relation_purposes", "inputs",
                 "selectors", "acceptance"}))
        return refuse(record, "invalid retained statement fields");
      auto relationRef = statement.getAs<FlatSymbolRefAttr>("relation");
      auto declaration =
          relationRef ? tables.lookupNearestSymbolFrom<relation::DeclareOp>(
                            record, relationRef)
                      : relation::DeclareOp();
      auto ports = statement.getAs<ArrayAttr>("inputs");
      auto selectors = statement.getAs<ArrayAttr>("selectors");
      auto acceptance =
          index(statement.get("acceptance"), type.getNumResults());
      if (!declaration || !ports || !selectors ||
          ports.size() != selectors.size() || !acceptance ||
          !type.getResult(*acceptance).isSignlessInteger(1) ||
          statement.get("relation_type") != declaration.getSignatureAttr() ||
          statement.get("relation_kind") != declaration.getKindAttr() ||
          statement.get("relation_key") != declaration.getKeyAttr() ||
          statement.get("relation_revision") != declaration.getRevisionAttr() ||
          statement.get("relation_purposes") != declaration.getPurposes() ||
          ports.size() != declaration.getSignature().getNumInputs())
        return refuse(record,
                      "statement no longer matches its relation or acceptance");
      if (failed(charge(ports.size())))
        return failure();
      for (auto [i, pair] : enumerate(zip(ports, selectors))) {
        auto input = index(std::get<0>(pair), type.getNumInputs());
        if (!input ||
            !is_contained(cast<ArrayAttr>(inputs[*input]), std::get<1>(pair)) ||
            type.getInput(*input) != declaration.getSignature().getInput(i))
          return refuse(record, "invalid statement input component");
      }
    }
    if (construction) {
      if (roles.size() != 2)
        return refuse(record, "construction requires two roles");
      ArrayAttr owners;
      for (auto removed : removedServices) {
        auto selectedOwners = cast<ArrayAttr>(inputs[removed]);
        if (selectedOwners.size() != 1 ||
            (owners && owners != selectedOwners) ||
            (codecValidator && selectedOwners[0] != codecValidator) ||
            protocol::randomServiceField(
                cast<protocol_ir::ServiceReferenceType>(type.getInput(removed))
                    .getContract())
                .empty())
          return refuse(record, "invalid constructed service owner");
        owners = selectedOwners;
      }
      Attribute validator;
      for (auto item : participants) {
        auto port = cast<DictionaryAttr>(item);
        if (port.get("role") == owners[0])
          validator = port.get("participant");
      }
      llvm::DenseSet<std::pair<Attribute, Attribute>> insertedUses;
      llvm::DenseSet<Attribute> insertedCallees;
      SmallVector<Attribute> retainedCallees;
      unsigned totalRemoved = 0;
      auto compare = [&](auto &&self, ArrayAttr source, ArrayAttr constructed,
                         unsigned depth) -> LogicalResult {
        if (depth > 64 || failed(charge(source.size() + constructed.size())))
          return refuse(record, "projection metadata work limit");
        llvm::StringMap<DictionaryAttr> originals;
        SmallVector<Attribute> retained, actualRetained;
        unsigned removedQueries = 0, removedMessages = 0;
        for (auto item : source) {
          auto action = cast<DictionaryAttr>(item);
          originals[action.getAs<StringAttr>("site").getValue()] = action;
          auto targets = action.getAs<ArrayAttr>("targets");
          auto kind = action.getAs<StringAttr>("kind").getValue();
          bool remove = false, codecMessage = false;
          bool start = kind == "protocol.construction_start";
          if (start) {
            if (!programmable)
              return refuse(record,
                            "construction start requires a selected plan");
            remove = true;
          }
          if (kind == "protocol.query")
            remove = removedServices.contains(
                cast<IntegerAttr>(action.get("service")).getInt());
          if (kind == "protocol.exchange") {
            unsigned sends = 0, receives = 0;
            for (auto item : targets) {
              auto target = cast<DictionaryAttr>(item);
              bool send = target.getAs<StringAttr>("operation").getValue() ==
                          "protocol.send";
              sends += send;
              receives += !send;
              remove |= send && target.get("participant") == validator;
            }
            if (sends != 1 || receives != 1)
              return refuse(record, "invalid original exchange directions");
            codecMessage = codecProducer && !remove;
            remove |= codecMessage;
          }
          if (!remove) {
            retained.push_back(action);
            if (auto callee = action.get("callee"))
              retainedCallees.push_back(callee);
          } else if (kind == "protocol.query") {
            ++removedQueries;
          } else if (!codecMessage && !start) {
            ++removedMessages;
          }
        }
        if (removedQueries != removedMessages)
          return refuse(record, "unpaired constructed challenges");
        totalRemoved += removedQueries;
        for (auto item : constructed) {
          auto action = dyn_cast<DictionaryAttr>(item);
          auto site = action ? action.getAs<StringAttr>("site") : StringAttr();
          if (!site)
            return refuse(record, "invalid constructed action");
          auto found = originals.find(site.getValue());
          if (found != originals.end()) {
            auto original = found->second;
            if (!is_contained(retained, original))
              return refuse(record, "changed retained construction action");
            if (auto body = original.getAs<ArrayAttr>("body")) {
              auto editedBody = action.getAs<ArrayAttr>("body");
              NamedAttrList a(action), b(original);
              a.erase("body");
              b.erase("body");
              if (!editedBody || a != b ||
                  failed(self(self, body, editedBody, depth + 1)))
                return refuse(record, "changed retained construction loop");
            } else if (action != original) {
              return refuse(record, "changed retained construction action");
            }
            actualRetained.push_back(original);
            continue;
          }
          if (action.getAs<StringAttr>("kind") !=
              StringAttr::get(record.getContext(), "protocol.local_call"))
            return refuse(record, "unsupported inserted construction action");
          auto ref = action.getAs<FlatSymbolRefAttr>("callee");
          auto function =
              ref ? tables.lookupNearestSymbolFrom<func::FuncOp>(record, ref)
                  : func::FuncOp();
          if (!function || !constructionHelpers.contains(ref))
            return refuse(record, "missing constructed helper");
          if (insertedCallees.insert(ref).second && !programmable &&
              failed(checkTranscriptHelper(function)))
            return failure();
          auto targets = action.getAs<ArrayAttr>("targets");
          if (!targets || failed(charge(targets.size())))
            return refuse(record, "invalid constructed targets");
          for (auto item : targets) {
            auto target = dyn_cast<DictionaryAttr>(item);
            auto participant =
                target ? target.getAs<FlatSymbolRefAttr>("participant")
                       : FlatSymbolRefAttr();
            if (!participant ||
                (!insertedUses.insert({participant, ref}).second &&
                 !codecHelpers.contains(ref)))
              return refuse(record, "repeated inserted transcript helper");
          }
        }
        if (actualRetained != retained)
          return refuse(record,
                        "missing or reordered retained construction action");
        return success();
      };
      if (failed(compare(compare, actions, constructedActions, 0)))
        return failure();
      if (!totalRemoved && !programmable)
        return refuse(record, "unpaired constructed challenges");
      if (insertedCallees != constructionHelpers)
        return refuse(record, "unused construction helper selection");
      for (auto callee : retainedCallees)
        if (!programmable && insertedCallees.contains(callee))
          return refuse(record,
                        "inserted transcript helper used by retained action");
    }
    llvm::DenseMap<Operation *, Operation *> parents;
    for (auto [ref, participant] : byReference)
      parents[participant] = participant;
    return checkActions(constructedActions ? constructedActions : actions,
                        byReference, parents, 0);
  }
  LogicalResult checkActions(
      ArrayAttr actions,
      const llvm::DenseMap<Attribute, protocol_ir::ParticipantOp> &byReference,
      const llvm::DenseMap<Operation *, Operation *> &parents, unsigned depth) {
    if (depth > 64)
      return refuse(record, "projection region depth exceeds 64");
    // Resolve every retained action to its actual participant occurrence, in
    // source order. Generated calculation calls are recorded separately.
    llvm::DenseMap<Operation *, unsigned> previous;
    llvm::StringSet<> sites;
    for (auto item : actions) {
      if (!remaining--)
        return refuse(record, "projection metadata work limit");
      auto action = dyn_cast<DictionaryAttr>(item);
      bool loop =
          action && action.getAs<StringAttr>("kind") ==
                        StringAttr::get(record.getContext(), "protocol.repeat");
      bool localCall = action && action.getAs<StringAttr>("kind") ==
                                     StringAttr::get(record.getContext(),
                                                     "protocol.local_call");
      if (!(loop ? keys(action, {"site", "kind", "targets", "maximum", "body"})
            : localCall ? keys(action, {"site", "kind", "targets", "callee"})
            : action &&
                    action.getAs<StringAttr>("kind") ==
                        StringAttr::get(record.getContext(), "protocol.query")
                ? keys(action, {"site", "kind", "targets", "service"})
                : keys(action, {"site", "kind", "targets"})))
        return refuse(record, "invalid retained action fields");
      auto site = action.getAs<StringAttr>("site");
      auto kind = action.getAs<StringAttr>("kind");
      auto targets = action.getAs<ArrayAttr>("targets");
      bool start = kind && kind.getValue() == "protocol.construction_start";
      if (!site || site.getValue().empty() ||
          !sites.insert(site.getValue()).second || !kind || !targets ||
          targets.empty() ||
          (kind.getValue() != "protocol.exchange" &&
           kind.getValue() != "protocol.guard" &&
           kind.getValue() != "protocol.finish_if" &&
           kind.getValue() != "protocol.query" && !localCall && !loop &&
           !start) ||
          (!loop &&
           targets.size() !=
               (kind.getValue() == "protocol.exchange" || start ? 2u : 1u)))
        return refuse(record, "invalid source action occurrence");
      llvm::DenseSet<Operation *> owners;
      llvm::DenseMap<Operation *, Operation *> children;
      protocol_ir::EmitOp send;
      protocol_ir::AwaitOp receive;
      for (auto targetItem : targets) {
        auto target = dyn_cast<DictionaryAttr>(targetItem);
        if (!keys(target, {"participant", "operation"}))
          return refuse(record, "invalid action target");
        auto participant = byReference.lookup(target.get("participant"));
        auto operation = target.getAs<StringAttr>("operation");
        if (!participant || !operation || !owners.insert(participant).second)
          return refuse(record, "invalid action participant reference");
        bool allowed =
            kind.getValue() == "protocol.exchange"
                ? (operation.getValue() == "protocol.send" ||
                   operation.getValue() == "protocol.receive")
            : loop      ? operation.getValue() == "protocol.loop"
            : localCall ? operation.getValue() == "protocol.local_call"
            : start     ? operation.getValue() == "protocol.construction_start"
            : kind.getValue() == "protocol.query"
                ? operation.getValue() == "protocol.service_query"
            : kind.getValue() == "protocol.finish_if"
                ? operation.getValue() == "protocol.finish_if"
                : operation.getValue() == "protocol.guard";
        if (!allowed)
          return refuse(record, "action target has wrong execution kind");
        // Targets retain their source projection kind. The checked profile
        // determines the executable realization without rewriting source facts.
        StringRef expected = operation.getValue();
        if (kind.getValue() == "protocol.guard" &&
            unit.getProfile() != protocol_ir::Profile::Participant)
          expected = "protocol.local_call";
        auto found = occurrences[participant].find(site);
        if (found == occurrences[participant].end() ||
            found->second.second->getName().getStringRef() != expected ||
            found->second.second->getParentOp() !=
                parents.lookup(participant) ||
            found->second.first <= previous.lookup(participant) ||
            !retainedActions.insert({participant, site}).second)
          return refuse(record,
                        "action occurrence is missing, changed or reordered");
        if (start) {
          auto boundary =
              dyn_cast<protocol_ir::ConstructionStartOp>(found->second.second);
          if (!boundary || boundary.getRoles().size() != targets.size() ||
              !all_of(targets, [&](Attribute item) {
                auto endpoint = byReference.lookup(
                    cast<DictionaryAttr>(item).get("participant"));
                return endpoint && is_contained(boundary.getRoles(),
                                                endpoint.getRoleAttr());
              }))
            return refuse(record, "construction start role boundary differs");
        }
        if (kind.getValue() == "protocol.query") {
          auto authority = action.getAs<IntegerAttr>("service");
          auto query =
              dyn_cast<protocol_ir::ParticipantQueryOp>(found->second.second);
          if (!authority || !query ||
              queryPorts.lookup({target.get("participant"), authority}) !=
                  query.getPortAttr())
            return refuse(record, "query authority differs from original port");
        }
        if (loop) {
          auto projected =
              dyn_cast<protocol_ir::ProtocolLoopOp>(found->second.second);
          auto maximum = action.getAs<IntegerAttr>("maximum");
          if (!projected || !maximum ||
              !maximum.getType().isSignlessInteger(64) ||
              maximum.getInt() < 0 || maximum.getInt() > 1048576 ||
              projected.getMaximumAttr() != maximum ||
              !action.getAs<ArrayAttr>("body"))
            return refuse(record, "repeat bound or body is missing or changed");
          children[participant] = projected;
        }
        if (localCall)
          authoredCallees.insert(action.get("callee"));
        if (localCall &&
            (!action.getAs<FlatSymbolRefAttr>("callee") ||
             found->second.second->getAttr("callee") != action.get("callee")))
          return refuse(record, "authored local call changed its callee");
        previous[participant] = found->second.first;
        if (kind.getValue() == "protocol.guard" &&
            unit.getProfile() != protocol_ir::Profile::Participant)
          requiredCalculations.insert({participant, site});
        if (auto emission = dyn_cast<protocol_ir::EmitOp>(found->second.second))
          send = emission;
        if (auto arrival = dyn_cast<protocol_ir::AwaitOp>(found->second.second))
          receive = arrival;
      }
      if (kind.getValue() == "protocol.exchange" &&
          (!send || !receive || send.getSchemaAttr() != site ||
           receive.getSchemaAttr() != site ||
           send.getPeerAttr() !=
               receive->getParentOfType<protocol_ir::ParticipantOp>()
                   .getRoleAttr() ||
           receive.getPeerAttr() !=
               send->getParentOfType<protocol_ir::ParticipantOp>()
                   .getRoleAttr() ||
           logicalType(send.getInput().getType()) !=
               logicalType(receive.getOutput().getType())))
        return refuse(record,
                      "exchange participant schemas, peers or types disagree");
      if (loop && failed(checkActions(action.getAs<ArrayAttr>("body"),
                                      byReference, children, depth + 1)))
        return failure();
    }
    return success();
  }
  LogicalResult run() {
    if (unit.getProfile() == protocol_ir::Profile::Protocol)
      return refuse(record, "projection metadata requires the 'participant', "
                            "'exec' or 'physical' profile");
    if (record->getAttrs().size() != 2 || record.getInterfaces().empty())
      return refuse(record,
                    "expected retained interfaces and calculation origins");
    for (auto item : record.getInterfaces())
      if (failed(checkInterface(dyn_cast<DictionaryAttr>(item))))
        return failure();
    for (auto &op : unit.getBody().front()) {
      if (isa<protocol_ir::ParticipantOp>(op) && !seenParticipants.count(&op))
        return refuse(record, "participant is missing its retained interface");
      if (isa<protocol_ir::ProtocolEntryOp>(op) && !entries.count(&op))
        return refuse(record, "entry is missing its retained interface");
    }
    llvm::DenseSet<std::pair<Operation *, Attribute>> calculations;
    for (auto item : record.getCalculations()) {
      if (failed(charge(1)))
        return failure();
      auto calculation = dyn_cast<DictionaryAttr>(item);
      if (!keys(calculation, {"participant", "callee", "site"}) ||
          unit.getProfile() == protocol_ir::Profile::Participant)
        return refuse(record, "invalid calculation origin");
      auto ref = calculation.getAs<FlatSymbolRefAttr>("participant");
      auto calleeRef = calculation.getAs<FlatSymbolRefAttr>("callee");
      auto site = calculation.getAs<StringAttr>("site");
      auto participant =
          ref ? tables.lookupNearestSymbolFrom<protocol_ir::ParticipantOp>(
                    record, ref)
              : protocol_ir::ParticipantOp();
      auto callee =
          calleeRef
              ? tables.lookupNearestSymbolFrom<func::FuncOp>(record, calleeRef)
              : func::FuncOp();
      if (!participant || !seenParticipants.count(participant) || !callee ||
          callee.getNumArguments() == 0 || callee.getNumResults() != 1 ||
          !isa<runtime::ScopeType>(callee.getArgumentTypes().front()) ||
          !isa<exec::OutcomeType>(callee.getResultTypes().front()) || !site ||
          !calculations.insert({participant, site}).second)
        return refuse(record, "invalid calculation symbol reference");
      if ((retainedActions.count({participant, site}) &&
           !requiredCalculations.count({participant, site})) ||
          authoredCallees.count(calleeRef))
        return refuse(record, "calculation origin overlaps authored execution");
      for (auto type : callee.getArgumentTypes().drop_front()) {
        auto policy = types.get(logicalType(type));
        if (!policy || !policy->total)
          return refuse(record, "calculation has a non-total input type");
      }
      for (auto type : cast<exec::OutcomeType>(callee.getResultTypes().front())
                           .getPayload()) {
        auto policy = types.get(logicalType(type));
        if (!policy || !policy->total)
          return refuse(record, "calculation has a non-total result type");
      }
      auto found = occurrences[participant].find(site);
      auto call =
          found == occurrences[participant].end()
              ? protocol_ir::LocalCallOp()
              : dyn_cast<protocol_ir::LocalCallOp>(found->second.second);
      if (!call || call.getCalleeAttr() != calleeRef)
        return refuse(record,
                      "calculation origin does not name one invocation");
    }

    if (!requiredCalculations.empty() && failed(execution()))
      return failure();
    for (auto occurrence : requiredCalculations) {
      if (!calculations.count(occurrence))
        return refuse(record,
                      "guard is missing its generated calculation origin");
      auto call = cast<protocol_ir::LocalCallOp>(
          occurrences[occurrence.first].lookup(occurrence.second).second);
      auto found = closure->bodies.find(call.getCallee().str());
      if (found == closure->bodies.end())
        return refuse(record,
                      "guard calculation requires an admitted scoped function");
      SmallVector<const protocol::SourceExecutionStep *> body;
      for (const auto &step : found->second)
        if (!isa<runtime::ReleaseBindingsOp>(step.operation))
          body.push_back(&step);
      auto *guard = body.size() >= 2 ? body[body.size() - 2] : nullptr;
      if (!guard || !isa<exec::TestOp>(guard->operation) ||
          !isa<exec::ReturnOp, exec::CompleteOp>(body.back()->operation) ||
          guard->inputs.size() != 1 || !guard->outputs.empty() ||
          guard->regions.size() != 2)
        return refuse(record,
                      "guard calculation lost its final conditional rejection");
      func::FuncOp yesRegion = guard->regions[0], noRegion = guard->regions[1];
      const auto &yes = closure->bodies.at(yesRegion.getSymName().str());
      const auto &no = closure->bodies.at(noRegion.getSymName().str());
      if (yes.size() != 1 || no.size() != 1 ||
          !isa<exec::CompleteOp>(yes[0].operation) ||
          !isa<exec::RejectOp>(no[0].operation))
        return refuse(record, "guard calculation changed its branch outcomes");
      auto stop = cast<exec::RejectOp>(no[0].operation);
      if (stop.getReason() != "reject" ||
          stop.getSiteAttr() != call.getSiteAttr())
        return refuse(record,
                      "guard calculation lost explicit source-site rejection");
    }
    for (auto &[participant, indexed] : occurrences)
      for (auto &[site, occurrence] : indexed) {
        if (!retainedActions.count({participant, site}) &&
            !calculations.count({participant, site}))
          return refuse(
              record,
              "participant action is missing from retained occurrences");
        if (calculations.count({participant, site}) &&
            !isa<protocol_ir::LocalCallOp>(occurrence.second))
          return refuse(record, "calculation origin names a non-call action");
      }
    return success();
  }
};
} // namespace

LogicalResult verifyProjectionMetadata(protocol_ir::ProtocolModuleOp unit) {
  NativeTypePolicies types(unit);
  return verifyProjectionMetadata(unit, types);
}
LogicalResult verifyProjectionMetadata(Operation *operation,
                                       NativeTypePolicies &types) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(operation);
  if (!llvm::hasSingleElement(unit.getBody()))
    return refuse(unit, "expected one protocol symbol-table block");
  unsigned count = 0;
  SymbolTableCollection tables;
  for (auto record :
       unit.getBody().front().getOps<protocol_ir::ProjectionOp>()) {
    ++count;
    if (failed(MetadataVerifier(record, unit, tables, types).run()))
      return failure();
  }
  if (count > 1 ||
      (unit.getProfile() == protocol_ir::Profile::Participant && count != 1))
    return refuse(
        unit,
        "the 'participant' profile requires one retained projection record");
  if (!count && !unit.getBody().front().getOps<relation::DeclareOp>().empty())
    return refuse(unit,
                  "native relation declarations require projection metadata");
  return relation::verifyDeclarationConsistency({unit.getOperation()});
}

LogicalResult verifyParticipantModule(protocol_ir::ProtocolModuleOp unit) {
  if (!llvm::hasSingleElement(unit.getBody()))
    return refuse(unit, "expected one participant symbol-table block");
  if (unit->getAttrs().size() != 1)
    return refuse(unit, "unexpected attribute in the 'participant' profile");
  if (auto error = protocol::verifySourceExecutionClosure(unit))
    return diagnostics::emit(unit.emitOpError(), std::move(error));
  if (failed(finite::verifyClosure(unit)))
    return failure();
  unsigned operations = 0;
  NativeTypePolicies types(unit);
  for (auto &declaration : unit.getBody().front()) {
    if (auto relation = dyn_cast<relation::DeclareOp>(declaration)) {
      for (auto attr : relation->getAttrs())
        if (!llvm::is_contained(relation.getAttributeNames(),
                                attr.getName().getValue()))
          return refuse(relation, "unsupported retained relation attribute");
      continue;
    }
    if (auto entry = dyn_cast<protocol_ir::ProtocolEntryOp>(declaration)) {
      for (auto attr : entry->getAttrs())
        if (!llvm::is_contained(entry.getAttributeNames(),
                                attr.getName().getValue()))
          return refuse(entry, "unsupported participant entry attribute");
      continue;
    }
    if (isa<data::DomainOp, func::FuncOp, mlir::ModuleOp, runtime::BindingOp>(
            declaration))
      continue;
    if (isa<protocol_ir::ProjectionOp>(declaration))
      continue;
    auto participant = dyn_cast<protocol_ir::ParticipantOp>(declaration);
    if (!participant)
      return refuse(&declaration,
                    "unclassified declaration in the 'participant' profile");
    for (auto attr : participant->getAttrs())
      if (!is_contained(ArrayRef<StringRef>{"sym_name", "function_type",
                                            "instance", "role",
                                            "service_ports"},
                        attr.getName().getValue()))
        return refuse(participant, "unsupported participant attribute");
    auto port = [&](Type type) -> LogicalResult {
      auto policy = types.get(type);
      if (!policy)
        return refuse(participant, "unsupported participant port type");
      if (!policy->protocolPort)
        return diagnostics::emit(participant.emitOpError(), "variant-boundary");
      return success();
    };
    for (auto type : participant.getFunctionType().getInputs())
      if (failed(port(type)))
        return failure();
    for (auto type : participant.getFunctionType().getResults())
      if (failed(port(type)))
        return failure();
    llvm::StringSet<> sites;
    llvm::DenseSet<Value> consumed;
    auto check = [&](auto &&self, Block &block,
                     unsigned depth) -> LogicalResult {
      if (depth > 64)
        return refuse(participant, "participant region depth exceeds 64");
      for (auto &op : block) {
        if (auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(op)) {
          if (!loop.getMaximum() || failed(loop.verifyRegions()))
            return refuse(loop,
                          "native iteration requires a bounded value count");
          for (Value capture :
               loop.getInputs().drop_front(1 + loop.getCarried())) {
            auto policy = types.get(capture.getType());
            if (!policy || policy->affine)
              return refuse(loop,
                            "affine values must be carried, not captured");
          }
          if (failed(self(self, loop.getBody().front(), depth + 1)))
            return failure();
        }
        if (++operations > 100000)
          return refuse(unit, "participant operation work limit");
        if (failed(verifyOperation(&op, Context::Participant)))
          return failure();
        for (auto type : op.getResultTypes())
          if (!dataType(type, types))
            return refuse(&op, "unsupported participant operation result type");
        for (auto input : op.getOperands()) {
          auto policy = types.get(input.getType());
          if (!policy || (isTotal(&op) && !policy->total))
            return refuse(&op,
                          "unsupported participant operation operand type");
          if (policy->affine && !consumed.insert(input).second)
            return refuse(&op, "affine participant value reused");
        }
        if (auto guard = dyn_cast<protocol_ir::GuardOp>(op))
          if (guard.getOwnerAttr() != participant.getRoleAttr())
            return refuse(guard, "guard requires its owning participant");
        if (auto start = dyn_cast<protocol_ir::ConstructionStartOp>(op)) {
          if (start.getRoles().size() != 2 ||
              start.getRoles()[0] == start.getRoles()[1] ||
              !is_contained(start.getRoles(), participant.getRoleAttr()))
            return refuse(
                &op, "construction start requires its selected participant");
          for (Value input : start.getInputs()) {
            auto policy = types.get(input.getType());
            if (!policy || !policy->shared)
              return refuse(&op,
                            "construction start requires shared data operands");
          }
        }
        if (isa<protocol_ir::EmitOp, protocol_ir::AwaitOp>(op)) {
          auto type = isa<protocol_ir::EmitOp>(op) ? op.getOperand(0).getType()
                                                   : op.getResult(0).getType();
          auto policy = types.get(type);
          if (!policy || !policy->wire)
            return refuse(&op, "unsupported participant wire type");
        }
        if (auto site = op.getAttrOfType<StringAttr>("site"))
          if (site.getValue().empty() || !sites.insert(site.getValue()).second)
            return refuse(&op, "duplicate or empty participant occurrence");
        if (auto query = dyn_cast<protocol_ir::ParticipantQueryOp>(op)) {
          auto ports = participant->getAttrOfType<ArrayAttr>("service_ports");
          std::optional<protocol::ServiceMethod> method;
          bool found =
              ports && any_of(ports, [&](Attribute item) {
                auto port = dyn_cast<ArrayAttr>(item);
                if (!port || port.size() != 3 || port[0] != query.getPortAttr())
                  return false;
                auto contract = dyn_cast<StringAttr>(port[1]);
                if (!contract)
                  return false;
                method = protocol::serviceMethod(contract.getValue(),
                                                 query.getMethod());
                return method.has_value();
              });
          auto spelling = [](Type type) {
            auto logical = protocol::encodeBoundType(type, false);
            if (!logical) {
              consumeError(logical.takeError());
              return std::string();
            }
            return logical->spelling();
          };
          if (!found || query.getNumOperands() != method->inputs.size() ||
              query.getNumResults() != 1 ||
              spelling(query.getResult(0).getType()) != method->output ||
              any_of(zip(query.getInputs(), method->inputs), [&](auto pair) {
                return spelling(std::get<0>(pair).getType()) !=
                       std::get<1>(pair);
              }))
            return refuse(query, "unsupported managed service query");
        }
      }
      return success();
    };
    if (failed(check(check, participant.getBody().front(), 0)))
      return failure();
  }
  return verifyProjectionMetadata(unit, types);
}

} // namespace zkc::mathematical

LogicalResult zkc::protocol_ir::ProjectionOp::verifySymbolUses(
    SymbolTableCollection &tables) {
  // Symbol resolution belongs to this interface. Full metadata/profile
  // validation runs once in the enclosing module's region verifier, after
  // its children have been verified. Direct profile APIs also perform it.
  auto uses = SymbolTable::getSymbolUses(getOperation());
  if (!uses)
    return mathematical::refuse(*this,
                                "cannot enumerate projection references");
  unsigned remaining = 1000000;
  std::optional<protocol::SourceExecutionClosure> closure;
  for (const auto &use : *uses) {
    if (!remaining--)
      return mathematical::refuse(*this, "projection symbol work limit");
    if (!tables.lookupNearestSymbolFrom(*this, use.getSymbolRef()))
      return mathematical::refuse(*this, "unresolved projection symbol");
  }
  return success();
}
