#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "zkc/Dialect/Protocol/Semantics.h"
#include "zkc/Dialect/Relation/IR/Declarations.h"
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
  if (auto physical = dyn_cast<plan::DataType>(type))
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
  llvm::DenseSet<Operation *> seenParticipants, entries;
  unsigned remaining = 1000000;
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

  LogicalResult checkTranscriptHelper(local::FuncOp function) {
    if (!function.getBody().hasOneBlock())
      return refuse(record, "invalid inserted transcript helper");
    auto &body = function.getBody().front();
    Operation *transition = nullptr;
    Value coordinates;
    SmallVector<Value> indices;
    for (auto &op : body) {
      if (failed(charge(1)))
        return failure();
      if (auto release = dyn_cast<plan::ReleaseOp>(op)) {
        if (any_of(release.getOperands(), [&](Value value) {
              return isa<local::CapabilityType>(logicalType(value.getType()));
            }))
          return refuse(record, "invalid inserted transcript helper");
        continue;
      }
      if (auto returned = dyn_cast<local::ReturnOp>(op)) {
        if (!transition || &op != &body.back() ||
            !llvm::equal(returned.getOperands(), transition->getResults()))
          return refuse(record, "invalid inserted transcript helper");
        continue;
      }
      auto binding = op.getAttrOfType<FlatSymbolRefAttr>("binding");
      auto declaration =
          binding ? tables.lookupNearestSymbolFrom<local::OperationBindingOp>(
                        &op, binding)
                  : local::OperationBindingOp();
      if (transition || !declaration)
        return refuse(record, "invalid inserted transcript helper");
      auto contract = declaration.getContract();
      if (!isa<plan::ExecuteKernelOp>(op) &&
          op.getName().getStringRef() != protocol::boundOperationName(contract))
        return refuse(record, "invalid inserted transcript helper");
      if (contract == "indices.empty" && !coordinates &&
          op.getNumOperands() == 0 && op.getNumResults() == 1) {
        coordinates = op.getResult(0);
        continue;
      }
      if (contract == "indices.append" && coordinates &&
          op.getNumOperands() == 2 && op.getOperand(0) == coordinates &&
          op.getNumResults() == 1) {
        indices.push_back(op.getOperand(1));
        coordinates = op.getResult(0);
        continue;
      }
      if ((contract != "transcript.native.indexed.challenge" &&
           contract != "transcript.native.indexed.observe.data") ||
          !coordinates)
        return refuse(record, "invalid inserted transcript helper");
      unsigned ordinary = contract.ends_with(".challenge") ? 1 : 2;
      {
        if (op.getNumOperands() != ordinary + 1 ||
            op.getOperands().back() != coordinates ||
            body.getNumArguments() != ordinary + indices.size() ||
            !llvm::equal(op.getOperands().take_front(ordinary),
                         body.getArguments().take_front(ordinary)) ||
            !llvm::equal(indices, body.getArguments().drop_front(ordinary)) ||
            any_of(indices, [&](Value value) {
              return !logicalType(value.getType()).isUnsignedInteger(64);
            }))
          return refuse(record, "invalid inserted transcript coordinates");
      }
      transition = &op;
    }
    if (!transition || body.empty() || !isa<local::ReturnOp>(body.back()))
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
    Type transcript;
    llvm::DenseSet<unsigned> removedServices;
    ArrayAttr constructedActions;
    if (construction) {
      auto format = construction.getAs<StringAttr>("format");
      auto state = construction.getAs<TypeAttr>("transcript");
      auto removed = construction.getAs<ArrayAttr>("removed_services");
      constructedActions = construction.getAs<ArrayAttr>("actions");
      if (!keys(construction,
                {"format", "transcript", "removed_services", "actions"}) ||
          !format || format.getValue() != "zkc.native-construction" || !state ||
          !removed || removed.size() != 1 || !constructedActions)
        return refuse(record, "invalid native construction mapping");
      auto capability = dyn_cast<local::CapabilityType>(state.getValue());
      if (!capability || !capability.getKind().starts_with("transcript:") ||
          protocol::nativeChallengeField(capability.getKind().drop_front(11))
              .empty())
        return refuse(record, "unsupported constructed transcript type");
      transcript = state.getValue();
      for (auto item : removed) {
        auto port = index(item, type.getNumInputs());
        if (!port ||
            !isa<protocol_ir::ServiceReferenceType>(type.getInput(*port)) ||
            !removedServices.insert(*port).second)
          return refuse(record, "invalid removed source service");
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
          if (!kind || !site || site.getValue().empty() ||
              !sourceSites.insert(site.getValue()).second || !targets ||
              (loop ? targets.empty() || targets.size() > 2
                    : targets.size() != (exchange ? 2u : 1u)) ||
              (kind.getValue() != "protocol.query" &&
               kind.getValue() != "protocol.guard" &&
               kind.getValue() != "protocol.finish_if" && !call && !exchange &&
               !loop) ||
              !(call   ? keys(action, {"site", "kind", "targets", "callee"})
                : loop ? keys(action,
                              {"site", "kind", "targets", "maximum", "body"})
                       : keys(action, {"site", "kind", "targets"})))
            return refuse(record, "invalid original construction action");
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
                 : call   ? operation.getValue() != "local.call"
                 : loop   ? operation.getValue() != "protocol.loop"
                 : kind.getValue() == "protocol.query"
                     ? operation.getValue() != "protocol.service_query"
                 : kind.getValue() == "protocol.finish_if"
                     ? operation.getValue() != "protocol.finish_if"
                     : operation.getValue() != "local.guard"))
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
      unsigned ingress = 0;
      for (auto [i, set] : enumerate(inputs)) {
        if (!is_contained(cast<ArrayAttr>(set), role))
          continue;
        if (auto service =
                dyn_cast<protocol_ir::ServiceReferenceType>(type.getInput(i))) {
          if (cast<ArrayAttr>(set).size() != 1 ||
              protocol::randomServiceField(service.getContract()).empty())
            return refuse(record, "invalid service owner or contract");
          servicePorts.push_back(builder.getI64IntegerAttr(i));
          if (!removedServices.contains(i))
            actualServices.push_back(builder.getArrayAttr(
                {builder.getStringAttr("service_" + std::to_string(ingress)),
                 builder.getStringAttr(service.getContract()),
                 builder.getI64IntegerAttr(ingress)}));
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
      if (transcript) {
        inputTypes.push_back(transcript);
        resultTypes.push_back(transcript);
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
      unsigned removed = *removedServices.begin();
      auto owners = cast<ArrayAttr>(inputs[removed]);
      if (owners.size() != 1 ||
          protocol::randomServiceField(
              cast<protocol_ir::ServiceReferenceType>(type.getInput(removed))
                  .getContract())
              .empty())
        return refuse(record, "invalid constructed service owner");
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
          bool remove = false;
          if (kind == "protocol.query")
            remove = cast<DictionaryAttr>(targets[0]).get("participant") ==
                     validator;
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
          }
          if (!remove) {
            retained.push_back(action);
            if (auto callee = action.get("callee"))
              retainedCallees.push_back(callee);
          } else if (kind == "protocol.query") {
            ++removedQueries;
          } else {
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
              ref ? tables.lookupNearestSymbolFrom<local::FuncOp>(record, ref)
                  : local::FuncOp();
          if (!function)
            return refuse(record, "missing constructed helper");
          if (insertedCallees.insert(ref).second &&
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
            if (!participant || !insertedUses.insert({participant, ref}).second)
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
      if (!totalRemoved)
        return refuse(record, "unpaired constructed challenges");
      for (auto callee : retainedCallees)
        if (insertedCallees.contains(callee))
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
                        : keys(action, {"site", "kind", "targets"})))
        return refuse(record, "invalid retained action fields");
      auto site = action.getAs<StringAttr>("site");
      auto kind = action.getAs<StringAttr>("kind");
      auto targets = action.getAs<ArrayAttr>("targets");
      if (!site || site.getValue().empty() ||
          !sites.insert(site.getValue()).second || !kind || !targets ||
          targets.empty() ||
          (kind.getValue() != "protocol.exchange" &&
           kind.getValue() != "protocol.guard" &&
           kind.getValue() != "protocol.finish_if" &&
           kind.getValue() != "protocol.query" && !localCall && !loop) ||
          (!loop && targets.size() !=
                        (kind.getValue() == "protocol.exchange" ? 2u : 1u)))
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
        bool allowed = kind.getValue() == "protocol.exchange"
                           ? (operation.getValue() == "protocol.send" ||
                              operation.getValue() == "protocol.receive")
                       : loop      ? operation.getValue() == "protocol.loop"
                       : localCall ? operation.getValue() == "local.call"
                       : kind.getValue() == "protocol.query"
                           ? operation.getValue() == "protocol.service_query"
                       : kind.getValue() == "protocol.finish_if"
                           ? operation.getValue() == "protocol.finish_if"
                           : operation.getValue() == "local.guard";
        if (!allowed)
          return refuse(record, "action target has wrong execution kind");
        // Targets retain their source projection kind. The checked profile
        // determines the executable realization without rewriting source facts.
        StringRef expected = operation.getValue();
        if (kind.getValue() == "protocol.guard" &&
            unit.getProfile() != protocol_ir::Profile::Participant)
          expected = "local.call";
        auto found = occurrences[participant].find(site);
        if (found == occurrences[participant].end() ||
            found->second.second->getName().getStringRef() != expected ||
            found->second.second->getParentOp() !=
                parents.lookup(participant) ||
            found->second.first <= previous.lookup(participant) ||
            !retainedActions.insert({participant, site}).second)
          return refuse(record,
                        "action occurrence is missing, changed or reordered");
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
              ? tables.lookupNearestSymbolFrom<local::FuncOp>(record, calleeRef)
              : local::FuncOp();
      if (!participant || !seenParticipants.count(participant) || !callee ||
          !site || !calculations.insert({participant, site}).second)
        return refuse(record, "invalid calculation symbol reference");
      if ((retainedActions.count({participant, site}) &&
           !requiredCalculations.count({participant, site})) ||
          authoredCallees.count(calleeRef))
        return refuse(record, "calculation origin overlaps authored execution");
      for (auto type : callee.getArgumentTypes()) {
        auto policy = types.get(logicalType(type));
        if (!policy || !policy->total)
          return refuse(record, "calculation has a non-total input type");
      }
      for (auto type : callee.getResultTypes()) {
        auto policy = types.get(logicalType(type));
        if (!policy || !policy->total)
          return refuse(record, "calculation has a non-total result type");
      }
      auto found = occurrences[participant].find(site);
      auto call = found == occurrences[participant].end()
                      ? local::CallOp()
                      : dyn_cast<local::CallOp>(found->second.second);
      if (!call || call.getCalleeAttr() != calleeRef)
        return refuse(record,
                      "calculation origin does not name one invocation");
    }
    for (auto occurrence : requiredCalculations) {
      if (!calculations.count(occurrence))
        return refuse(record,
                      "guard is missing its generated calculation origin");
      auto call = cast<local::CallOp>(
          occurrences[occurrence.first].lookup(occurrence.second).second);
      auto function = tables.lookupNearestSymbolFrom<local::FuncOp>(
          call, call.getCalleeAttr());
      if (!function || !hasSingleElement(function.getBody()))
        return refuse(record,
                      "guard calculation requires an executable function");
      SmallVector<Operation *> body;
      for (auto &op : function.getBody().front())
        if (!isa<plan::ReleaseOp>(op))
          body.push_back(&op);
      auto guard = body.size() >= 2
                       ? dyn_cast<local::LocalIfOp>(body[body.size() - 2])
                       : local::LocalIfOp();
      if (!guard || !isa<local::ReturnOp>(body.back()) ||
          guard.getNumOperands() != 1 || guard.getNumResults() ||
          !hasSingleElement(guard.getThenRegion()) ||
          !hasSingleElement(guard.getElseRegion()))
        return refuse(record,
                      "guard calculation lost its final conditional rejection");
      auto &yes = guard.getThenRegion().front(),
           &no = guard.getElseRegion().front();
      if (!hasSingleElement(yes) || !hasSingleElement(no) ||
          !isa<local::LocalYieldOp>(yes.front()) ||
          !isa<local::StopOp>(no.front()))
        return refuse(record, "guard calculation changed its branch outcomes");
      auto stop = cast<local::StopOp>(no.front());
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
            !isa<local::CallOp>(occurrence.second))
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
    if (isa<local::FuncOp, local::OperationBindingOp>(declaration))
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
          StringRef field;
          bool found =
              ports && any_of(ports, [&](Attribute item) {
                auto port = dyn_cast<ArrayAttr>(item);
                if (!port || port.size() != 3 || port[0] != query.getPortAttr())
                  return false;
                auto contract = dyn_cast<StringAttr>(port[1]);
                if (!contract)
                  return false;
                field = protocol::randomServiceField(contract.getValue());
                return !field.empty();
              });
          if (!found || query.getMethod() != "draw" || query.getNumOperands() ||
              query.getNumResults() != 1 ||
              query.getResult(0).getType() !=
                  algebra::FieldType::get(unit.getContext(), field))
            return refuse(query, "unsupported managed service query");
        }
      }
      return success();
    };
    if (failed(check(check, participant.getBody().front(), 0)))
      return failure();
  }
  if (failed(verifyNativeLocals(unit, false, types)))
    return failure();
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
  for (const auto &use : *uses) {
    if (!remaining--)
      return mathematical::refuse(*this, "projection symbol work limit");
    if (!tables.lookupNearestSymbolFrom(*this, use.getSymbolRef()))
      return mathematical::refuse(*this, "unresolved projection symbol");
  }
  return success();
}
