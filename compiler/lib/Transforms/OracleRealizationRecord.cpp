#include "OracleCommonPlan.h"
#include "OracleVerificationContext.h"
#include "zkc/Contracts/OracleKinds.h"
#include "zkc/Dialect/Protocol/Contracts.h"
#include "zkc/Dialect/Protocol/OraclePorts.h"
#include "zkc/Dialect/StructuredData.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/JSON.h"
#include <limits>
using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
constexpr size_t byteLimit = 32 * 1024 * 1024;
Error refuse() { return error("oracle-realization-record"); }
// The record also describes original oracle interfaces, while executable
// helper types remain ordinary data. Do not grant oracle types ordinary value
// formation merely because their descriptors share this intern table.
LogicalResult verifyRecordedType(Type type) {
  auto emit = [&] {
    auto diagnostic = emitError(UnknownLoc::get(type.getContext()));
    diagnostic.abandon();
    return diagnostic;
  };
  if (auto handle = dyn_cast<protocol_ir::OracleHandleType>(type))
    return protocol_ir::OracleHandleType::verify(emit, handle.getKind());
  if (auto sequence = dyn_cast<protocol_ir::OracleSequenceType>(type))
    return protocol_ir::OracleSequenceType::verify(emit, sequence.getKind(),
                                                   sequence.getMaximum());
  return verifyLogicalType(emit, type);
}
// A closed schema, with one canonical intern table for complete source types.
// The visitor only reads metadata. Actual body checking remains independent.
struct Codec {
  bool reading, valid = true;
  unsigned remaining = 1000000;
  ModuleOp candidate;
  std::vector<Type> types;
  llvm::DenseMap<Type, unsigned> typeIDs;
  explicit Codec(bool reading, ModuleOp candidate)
      : reading(reading), candidate(candidate) {}
  struct Object {
    Codec &codec;
    json::Object &value;
    unsigned fields = 0;
    template <class T> void field(StringRef name, T &item) {
      ++fields;
      if (!codec.valid)
        return;
      if (codec.reading) {
        auto *node = value.get(name);
        if (!node) {
          codec.valid = false;
          return;
        }
        codec.item(*node, item);
      } else {
        json::Value node(nullptr);
        codec.item(node, item);
        value[name] = std::move(node);
      }
    }
    // Derived fields are compared against the original after actual-body
    // checking. They are never accepted as input to the source derivation.
    void derived(StringRef name) {
      ++fields;
      if (codec.reading && !value.get(name))
        codec.valid = false;
    }
  };
  template <class F> void object(json::Value &node, F fields) {
    if (!valid || !remaining) {
      valid = false;
      return;
    }
    --remaining;
    if (!reading)
      node = json::Object{};
    auto *value = node.getAsObject();
    if (!value) {
      valid = false;
      return;
    }
    Object visitor{*this, *value};
    fields(visitor);
    if (reading && value->size() != visitor.fields)
      valid = false;
  }
  template <class T> void item(json::Value &node, std::vector<T> &items) {
    if (!valid)
      return;
    if (!reading)
      node = json::Array{};
    auto *array = node.getAsArray();
    size_t count = reading && array ? array->size() : items.size();
    if (!array || count > remaining) {
      valid = false;
      return;
    }
    remaining -= count;
    if (reading) {
      items.resize(count);
      for (auto [value, element] : zip(*array, items))
        item(value, element);
    } else {
      for (auto &element : items) {
        json::Value value(nullptr);
        item(value, element);
        array->push_back(std::move(value));
      }
    }
  }
  void item(json::Value &node, uint64_t &value) {
    if (reading) {
      auto number = node.getAsUINT64();
      if (!number)
        valid = false;
      else
        value = *number;
    } else
      node = value;
  }
  void item(json::Value &node, unsigned &value) {
    uint64_t number = value;
    item(node, number);
    if (number > std::numeric_limits<unsigned>::max())
      valid = false;
    else
      value = number;
  }
  void item(json::Value &node, std::string &value) {
    if (reading) {
      auto text = node.getAsString();
      if (!text)
        valid = false;
      else
        value = text->str();
    } else
      node = value;
  }
  void item(json::Value &node, Type &type) {
    unsigned id = 0;
    if (!reading) {
      if (!type) {
        valid = false;
        return;
      }
      auto found = typeIDs.try_emplace(type, types.size());
      id = found.first->second;
      if (found.second) {
        if (types.size() == 4096) {
          valid = false;
          return;
        }
        types.push_back(type);
      }
    }
    item(node, id);
    if (reading) {
      if (id >= types.size())
        valid = false;
      else
        type = types[id];
    }
  }
  void item(json::Value &node, func::FuncOp &function) {
    if (reading && node.kind() == json::Value::Null) {
      function = {};
      return;
    }
    if (!reading && !function) {
      node = nullptr;
      return;
    }
    std::string name = function ? function.getSymName().str() : "";
    item(node, name);
    if (!valid)
      return;
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
    if (reading) {
      function = dyn_cast_or_null<func::FuncOp>(
          SymbolTable::lookupSymbolIn(unit, name));
      valid &= bool(function);
    } else
      valid &= function->getParentOp() == unit;
  }
  void item(json::Value &node, OracleControllerAccess &access) {
    std::string name;
    if (!reading)
      name =
          access == OracleControllerAccess::Available ? "available" : "holder";
    item(node, name);
    if (name == "available")
      access = OracleControllerAccess::Available;
    else if (name == "holder")
      access = OracleControllerAccess::Holder;
    else
      valid = false;
  }
  struct Argument {
    std::string tag;
    unsigned type = 0;
    uint64_t natural = 0;
  };
  void item(json::Value &node, Argument &argument) {
    object(node, [&](Object &object) {
      object.field("kind", argument.tag);
      if (argument.tag == "type")
        object.field("value", argument.type);
      else if (argument.tag == "nat")
        object.field("value", argument.natural);
      else
        valid = false;
    });
  }
  void item(json::Value &node, protocol_ir::OracleKindAttr &kind) {
    std::string identity;
    std::vector<Argument> arguments;
    if (!reading) {
      if (!kind) {
        valid = false;
        return;
      }
      identity = kind.getIdentity().str();
      for (Attribute arg : kind.getArguments()) {
        if (auto typed = dyn_cast<TypeAttr>(arg)) {
          Type type = typed.getValue();
          json::Value reference(nullptr);
          item(reference, type);
          if (!valid)
            return;
          arguments.push_back({"type", unsigned(*reference.getAsUINT64()), 0});
        } else if (auto number = dyn_cast<IntegerAttr>(arg))
          arguments.push_back({"nat", 0, number.getValue().getZExtValue()});
        else {
          valid = false;
          return;
        }
      }
    }
    object(node, [&](Object &object) {
      object.field("kind", identity);
      object.field("arguments", arguments);
    });
    if (!reading || !valid)
      return;
    SmallVector<Attribute> attrs;
    for (const auto &arg : arguments) {
      if (arg.tag == "type") {
        if (arg.type >= types.size()) {
          valid = false;
          return;
        }
        Type type = types[arg.type];
        attrs.push_back(TypeAttr::get(type));
      } else {
        attrs.push_back(IntegerAttr::get(
            IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned),
            arg.natural));
      }
    }
    kind = protocol_ir::OracleKindAttr::getChecked(
        [&] {
          auto diagnostic = emitError(UnknownLoc::get(candidate.getContext()));
          diagnostic.abandon();
          return diagnostic;
        },
        candidate.getContext(), StringRef(identity),
        ArrayAttr::get(candidate.getContext(), attrs));
    valid &= bool(kind);
  }
  void item(json::Value &node, OracleQuerySize &value) {
    object(node, [&](Object &object) {
      object.field("leaves", value.leaves);
      object.field("nodes", value.nodes);
    });
  }
  void item(json::Value &node, OracleQueryContinuation &value) {
    object(node, [&](Object &object) {
      object.field("constructor", value.constructor);
      object.field("query", value.query);
      object.field("record", value.record);
      object.field("sequence", value.sequence);
      object.field("previous_kinds", value.previousKinds);
    });
  }
  void item(json::Value &node, OracleVirtualQueryFunction &value) {
    object(node, [&](Object &object) {
      object.field("source", value.source);
      object.field("site", value.site);
      object.field("kind", value.kind);
      object.field("position", value.position);
    });
  }
  void item(json::Value &node, OracleVirtualFunctions &value) {
    object(node, [&](Object &object) {
      object.field("queries", value.queries);
      object.field("answer", value.answer);
    });
  }
  void item(json::Value &node, OracleQueryControllerConstructor &value) {
    object(node, [&](Object &object) {
      object.field("source", value.source);
      object.field("role", value.role);
      object.field("kind", value.kind);
      object.field("first_continuation", value.firstContinuation);
      object.field("lookup", value.lookup);
      object.field("functions", value.functions);
    });
  }
  void item(json::Value &node, OracleQueryController &value) {
    object(node, [&](Object &object) {
      object.field("role", value.role);
      object.field("access", value.access);
      object.field("capacity", value.capacity);
      object.field("kinds", value.kinds);
      object.field("answers", value.answers);
      object.field("state", value.state);
      object.field("stores", value.stores);
      object.field("constructors", value.constructors);
      object.field("continuations", value.continuations);
      object.field("leaf_counts", value.leafCounts);
      object.field("row_counts", value.rowCounts);
      object.field("construction_counts", value.constructionCounts);
      object.field("initialize", value.initialize);
      object.field("advance", value.advance);
      object.field("finish", value.finish);
      object.field("resume", value.resume);
      object.field("evaluate", value.evaluate);
      object.field("contents", value.contents);
    });
  }
  void item(json::Value &node, OracleCommonController &value) {
    object(node, [&](Object &object) {
      object.field("role", value.role);
      object.field("kind", value.kind);
      object.field("access", value.access);
      object.field("body", value.body);
    });
  }
  void item(json::Value &node, OracleQueryDemand &value) {
    object(node, [&](Object &object) {
      object.field("frame", value.frame);
      object.field("sequence", value.sequence);
      object.field("state", value.state);
      object.field("initialize", value.initialize);
      object.field("advance", value.advance);
      object.field("consume", value.consume);
    });
  }
  void item(json::Value &node, OracleQueryResponse &value) {
    object(node, [&](Object &object) {
      object.field("answer", value.answer);
      object.field("authenticate", value.authenticate);
      object.field("resume", value.resume);
    });
  }
  void item(json::Value &node, OracleQueryPacket &value) {
    object(node, [&](Object &object) {
      object.field("request_sequence", value.requestSequence);
      object.field("response_sequence", value.responseSequence);
      object.field("answer_sequence", value.answerSequence);
      object.field("groups_sequence", value.groupsSequence);
      object.field("key", value.key);
      object.field("key_sequence", value.keySequence);
      object.field("group", value.group);
      object.field("open", value.open);
      object.field("authenticate", value.authenticate);
    });
  }
  void item(json::Value &node, OracleQueryWindow &value) {
    object(node, [&](Object &object) {
      object.field("request_sequence", value.requestSequence);
      object.field("answer_sequence", value.answerSequence);
      object.field("capacity", value.capacity);
      object.field("collect", value.collect);
      object.field("replay", value.replay);
      object.field("finish", value.finish);
    });
  }
  void item(json::Value &node, OracleQueryBatch &value) {
    object(node, [&](Object &object) {
      object.field("demand_state", value.demandState);
      object.field("evaluator_state", value.evaluatorState);
      object.field("request_sequence", value.requestSequence);
      object.field("answer_sequence", value.answerSequence);
      object.field("collect", value.collect);
      object.field("check_available", value.checkAvailable);
      object.field("replay", value.replay);
      object.field("finish", value.finish);
    });
  }
  void item(json::Value &node, OracleCommonRemote &value) {
    object(node, [&](Object &object) {
      object.field("receiver", value.receiver);
      object.field("holder", value.holder);
      object.field("demand", value.demand);
      object.field("response", value.response);
      object.field("open", value.open);
      object.field("packet", value.packet);
      object.field("window", value.window);
    });
  }
  void item(json::Value &node, OracleCommonBatch &value) {
    object(node, [&](Object &object) {
      object.field("remotes", value.remotes);
      object.field("body", value.body);
    });
  }
  void item(json::Value &node, OracleResultStore &value) {
    object(node, [&](Object &object) {
      object.field("constructor", value.constructor);
      object.field("role", value.role);
      object.field("port", value.port);
    });
  }
  void item(json::Value &node, OracleResultReference &value) {
    object(node, [&](Object &object) {
      object.field("result", value.result);
      object.field("role", value.role);
      object.field("stores", value.storePorts);
    });
  }
  void item(json::Value &node, OracleMerkleFunctions &value) {
    object(node, [&](Object &object) {
      object.field("position", value.position);
      object.field("commit", value.commit);
      object.field("open", value.open);
      object.field("authenticate", value.authenticate);
    });
  }
  void item(json::Value &node, OracleInputShape &value) {
    object(node, [&](Object &object) {
      object.field("anchor", value.anchor);
      object.field("port", value.port);
    });
  }
  void item(json::Value &node, OracleCommonEntryRealization &value) {
    object(node, [&](Object &object) {
      object.field("entry", value.entry);
      object.field("merkle", value.merkle);
      object.field("input_shapes", value.inputShapes);
      object.field("controllers", value.controllers);
      object.field("allocators", value.allocators);
      object.field("locals", value.locals);
      object.field("remotes", value.remotes);
      object.field("batches", value.batches);
      object.field("result_stores", value.resultStores);
      object.field("result_references", value.resultReferences);
      object.derived("constructors");
      object.derived("occurrences");
      object.derived("query_blocks");
      object.derived("interface");
      object.derived("logical_interface");
      object.derived("contracts");
    });
  }
  json::Value type(Type value) {
    json::Value node(nullptr);
    item(node, value);
    return node;
  }
  // Service ports are participant-local capabilities, not logical data or
  // native binding operands. Keep their installed identity outside the data
  // type intern table; actual signatures and role ownership are rederived.
  json::Value port(Type value) {
    if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(value))
      return json::Object{{"service", service.getContract()}};
    return type(value);
  }
  json::Value kind(protocol_ir::OracleKindAttr value) {
    json::Value node(nullptr);
    item(node, value);
    return node;
  }
};
json::Array numbers(ArrayRef<unsigned> values) {
  json::Array result;
  for (unsigned value : values)
    result.push_back(value);
  return result;
}
json::Array roles(ArrayAttr values) {
  json::Array result;
  for (Attribute value : values) {
    json::Array names;
    for (Attribute role : cast<ArrayAttr>(value))
      names.push_back(cast<StringAttr>(role).getValue());
    result.push_back(std::move(names));
  }
  return result;
}
Expected<json::Value> contracts(Codec &codec,
                                protocol_ir::MathematicalOp program,
                                const mathematical::OraclePortLayout &layout,
                                SymbolTableCollection &symbols) {
  auto inventory = protocol_ir::readContracts(program, symbols);
  if (failed(inventory))
    return refuse();
  auto component = [&](const protocol_ir::ContractComponent &value) {
    return json::Object{{"direction", value.port.output ? "output" : "input"},
                        {"port", value.port.index},
                        {"role", value.role.getValue()},
                        {"type", codec.type(value.type)}};
  };
  auto selector =
      [&](const protocol_ir::ContractSelector &value) -> Expected<json::Value> {
    if (auto *local = std::get_if<protocol_ir::ContractComponent>(&value))
      return json::Object{{"component", component(*local)}};
    const auto &anchor = std::get<protocol_ir::ContractAnchor>(value);
    const auto &pairs = anchor.port.output ? layout.outputs : layout.inputs;
    auto pair = find_if(pairs, [&](const auto &pair) {
      return pair.anchor == anchor.port.index &&
             pair.type == protocol_ir::OracleHandleType::get(
                              anchor.kind.getContext(), anchor.kind);
    });
    if (pair == pairs.end())
      return refuse();
    return json::Object{
        {"anchor",
         json::Object{{"direction", anchor.port.output ? "output" : "input"},
                      {"port", anchor.port.index},
                      {"pair", unsigned(pair - pairs.begin())},
                      {"kind", codec.kind(anchor.kind)}}}};
  };
  auto application = [&](const protocol_ir::ContractApplication &value)
      -> Expected<json::Value> {
    json::Array operands;
    for (const auto &operand : value.operands) {
      auto actual = selector(operand);
      if (!actual)
        return actual.takeError();
      operands.push_back(std::move(*actual));
    }
    return json::Object{{"relation", value.relation.getValue()},
                        {"operands", std::move(operands)}};
  };
  json::Array clauses, statements;
  for (const auto &clause : inventory->clauses) {
    auto subject = application(clause.subject);
    if (!subject)
      return subject.takeError();
    json::Value residual(nullptr), decision(nullptr);
    if (clause.residual) {
      auto actual = application(*clause.residual);
      if (!actual)
        return actual.takeError();
      residual = std::move(*actual);
    }
    if (clause.decision)
      decision = component(*clause.decision);
    clauses.push_back(json::Object{{"kind", clause.kind.getValue()},
                                   {"name", clause.name.getValue()},
                                   {"subject", std::move(*subject)},
                                   {"residual", std::move(residual)},
                                   {"decision", std::move(decision)}});
  }
  llvm::DenseMap<Operation *, unsigned> positions;
  for (auto [i, operation] : enumerate(program.getBody().front()))
    positions[&operation] = i;
  for (const auto &selection : inventory->statements) {
    json::Value target(nullptr);
    if (selection.clause)
      target = *selection.clause;
    statements.push_back(
        json::Object{{"operation", positions.lookup(selection.statement)},
                     {"target", std::move(target)}});
  }
  return json::Object{{"clauses", std::move(clauses)},
                      {"statements", std::move(statements)}};
}
Expected<json::Object> derived(Codec &codec, ModuleOp prepared,
                               const OracleCommonEntryRealization &entry,
                               ArrayRef<OracleRootSelection> selections,
                               OracleAuthentication authentication) {
  auto requirements = oracleRequirements(prepared, entry.entry, selections);
  if (!requirements)
    return requirements.takeError();
  auto plan = planOracleCommon(
      prepared, entry.entry, *requirements, entry.controllers, entry.allocators,
      entry.merkle, authentication, entry.remotes, entry.batches);
  if (!plan)
    return plan.takeError();
  auto unit = cast<protocol_ir::ProtocolModuleOp>(prepared.getBody()->front());
  auto program = cast<protocol_ir::MathematicalOp>(
      SymbolTable::lookupSymbolIn(unit, entry.entry));
  SymbolTableCollection symbols;
  unsigned remaining = 100000;
  auto logical =
      mathematical::readOraclePortLayout(program, symbols, remaining);
  if (failed(logical))
    return refuse();
  auto pairs = [&](ArrayRef<mathematical::OraclePortPair> layout) {
    json::Array result;
    for (const auto &pair : layout) {
      json::Array receivers;
      for (Attribute role : pair.receivers)
        receivers.push_back(cast<StringAttr>(role).getValue());
      result.push_back(json::Object{{"data", pair.data},
                                    {"anchor", pair.anchor},
                                    {"type", codec.type(pair.type)},
                                    {"holder", pair.holder.getValue()},
                                    {"receivers", std::move(receivers)}});
    }
    return result;
  };
  auto logicalInputs = pairs(logical->inputs);
  auto logicalOutputs = pairs(logical->outputs);
  auto logicalContracts = contracts(codec, program, *logical, symbols);
  if (!logicalContracts)
    return logicalContracts.takeError();
  json::Array constructors;
  for (const auto &item : requirements->storage.constructors) {
    json::Array owners, receivers;
    for (const auto &receiver : item.receivers)
      receivers.push_back(receiver);
    for (const auto &owner : item.roles) {
      json::Array fields;
      for (const auto &field : owner.fields)
        fields.push_back(json::Object{{"name", field.name},
                                      {"type", codec.type(field.type)}});
      owners.push_back(json::Object{{"role", owner.role},
                                    {"fields", std::move(fields)},
                                    {"record", codec.type(owner.record)},
                                    {"store", codec.type(owner.sequence)}});
    }
    StringRef constructor =
        item.constructor == OracleAnchorConstructor::Kind::Input  ? "input"
        : item.constructor == OracleAnchorConstructor::Kind::Send ? "send"
                                                                  : "virtual";
    constructors.push_back(
        json::Object{{"constructor", constructor},
                     {"path", numbers(item.path)},
                     {"kind", codec.kind(item.kind)},
                     {"holder", item.holder},
                     {"receivers", std::move(receivers)},
                     {"site", item.site},
                     {"declaration", item.declaration},
                     {"scheme", item.scheme},
                     {"maximum_instances", item.maximumInstances},
                     {"roles", std::move(owners)}});
  }
  json::Array occurrences;
  for (const auto &item : plan->occurrences)
    occurrences.push_back(json::Object{{"site", item.site},
                                       {"purpose", item.purpose},
                                       {"role", item.role},
                                       {"path", numbers(item.sourcePath)}});
  json::Array blocks;
  for (const auto &block : plan->queryBlocks) {
    json::Array queries;
    for (const auto &path : block.queries)
      queries.push_back(numbers(path));
    json::Value capacity(nullptr);
    if (block.packetCapacity)
      capacity = *block.packetCapacity;
    blocks.push_back(json::Object{{"queries", std::move(queries)},
                                  {"packet_capacity", std::move(capacity)}});
  }
  auto signature = cast<FunctionType>(
      plan->attributes.getAs<TypeAttr>("function_type").getValue());
  json::Array inputs, outputs;
  for (Type value : signature.getInputs())
    inputs.push_back(codec.port(value));
  for (Type value : signature.getResults())
    outputs.push_back(codec.port(value));
  return json::Object{
      {"contracts", std::move(*logicalContracts)},
      {"constructors", std::move(constructors)},
      {"occurrences", std::move(occurrences)},
      {"query_blocks", std::move(blocks)},
      {"logical_interface",
       json::Object{{"inputs", std::move(logicalInputs)},
                    {"outputs", std::move(logicalOutputs)}}},
      {"interface",
       json::Object{{"inputs", std::move(inputs)},
                    {"outputs", std::move(outputs)},
                    {"input_roles",
                     roles(plan->attributes.getAs<ArrayAttr>("input_roles"))},
                    {"output_roles", roles(plan->attributes.getAs<ArrayAttr>(
                                         "output_roles"))}}}};
}
// Bind all declaration names and symbolic generation slots, including helpers
// outlined inside another helper and binding names selected at actual uses.
// No opcode, executable operand, literal or body can be supplied by this table.
json::Array declarations(ModuleOp candidate) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  json::Array result;
  for (auto &declaration : unit.getBody().front()) {
    json::Array references;
    unsigned ordinal = 0;
    declaration.walk<WalkOrder::PreOrder>([&](Operation *op) {
      unsigned current = ordinal++;
      for (auto attribute : op->getAttrs()) {
        json::Array symbols;
        attribute.getValue().walk([&](SymbolRefAttr reference) {
          json::Array parts{reference.getRootReference().getValue()};
          for (auto nested : reference.getNestedReferences())
            parts.push_back(nested.getValue());
          symbols.push_back(std::move(parts));
        });
        if (!symbols.empty())
          references.push_back(json::Array{
              current, attribute.getName().getValue(), std::move(symbols)});
      }
    });
    result.push_back(
        json::Array{SymbolTable::getSymbolName(&declaration).getValue(),
                    std::move(references)});
  }
  return result;
}
Expected<json::Value> encode(ModuleOp prepared, ModuleOp candidate,
                             ArrayRef<OracleCommonEntryRealization> entries,
                             ArrayRef<OracleRootSelection> selections,
                             const OracleRealizationPolicy &policy) {
  if (!prepared || !candidate ||
      !hasSingleElement(candidate.getBody()->getOperations()) ||
      !isa<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front()))
    return refuse();
  Codec codec(false, candidate);
  auto values =
      std::vector<OracleCommonEntryRealization>(entries.begin(), entries.end());
  json::Value encoded(nullptr);
  codec.item(encoded, values);
  if (!codec.valid)
    return refuse();
  for (auto [node, entry] : zip(*encoded.getAsArray(), entries)) {
    auto fields =
        derived(codec, prepared, entry, selections, policy.authentication);
    if (!fields)
      return fields.takeError();
    for (auto &field : *fields)
      (*node.getAsObject())[field.first] = std::move(field.second);
  }
  if (!codec.valid)
    return refuse();
  for (Type type : codec.types) {
    if (failed(verifyRecordedType(type)))
      return refuse();
  }
  auto types = exportLogicalTypesData(TypeRange(codec.types));
  if (!types)
    return types.takeError();
  json::Array roots;
  for (const auto &selection : selections) {
    const auto &choice = selection.realization;
    roots.push_back(json::Object{
        {"entry", selection.entry},
        {"path", numbers(selection.path)},
        {"scheme", choice.scheme},
        {"grouping", choice.grouping == OracleLeafGrouping::Individual
                         ? "individual"
                         : "antipodal-pairs"},
        {"order", choice.order == OracleLeafOrder::Natural ? "natural"
                                                           : "bit-reversed"}});
  }
  return json::Object{
      {"format", "zkc.oracle-realization/0"},
      {"selection",
       json::Object{{"order", policy.order == OracleQueryOrder::Unrestricted
                                  ? "unrestricted"
                                  : "after-final-draw"},
                    {"authentication",
                     policy.authentication == OracleAuthentication::PerQuery
                         ? "per-query"
                         : "atomic-blocks"},
                    {"roots", std::move(roots)}}},
      {"types", std::move(*types)},
      {"entries", std::move(encoded)},
      {"declarations", declarations(candidate)}};
}
} // namespace
Expected<OracleRealizationPublication>
exportOracleRealization(ModuleOp prepared,
                        const OracleCommonRealization &actual,
                        const OracleRealizationPolicy &policy) {
  auto selections = resolveOracleRealizationSelection(prepared, policy);
  if (!selections)
    return selections.takeError();
  auto record = encode(prepared, actual.module.get(), actual.entries,
                       *selections, policy);
  if (!record)
    return record.takeError();
  std::string text;
  BoundedStream out(text, byteLimit);
  out << *record;
  // The closed encoder already constrains object keys and natural values.
  // Check the wire envelope without allocating a second parsed record. Its
  // lexical container depth differs from the native type depth.
  if (out.overflow() || !mlirNestingWithinLimit(text, 64))
    return error("oracle-realization-record-limit");
  ownJsonStrings(*record);
  return OracleRealizationPublication{std::move(*record), std::move(text)};
}
Expected<std::string>
serializeOracleRealization(ModuleOp prepared,
                           const OracleCommonRealization &actual,
                           const OracleRealizationPolicy &policy) {
  auto publication = exportOracleRealization(prepared, actual, policy);
  if (!publication)
    return publication.takeError();
  return std::move(publication->bytes);
}
Error checkOracleRealization(ModuleOp prepared, ModuleOp candidate,
                             StringRef text,
                             const OracleRealizationPolicy &policy) {
  auto selections = resolveOracleRealizationSelection(prepared, policy);
  if (!selections)
    return selections.takeError();
  auto parsed =
      parseNaturalJson(text, byteLimit, 64, "oracle-realization-record",
                       "oracle-realization-record-limit");
  if (!parsed)
    return parsed.takeError();
  auto *record = parsed->getAsObject();
  if (!record || record->size() != 5 ||
      record->getString("format") != "zkc.oracle-realization/0" ||
      !record->getObject("selection") || !record->getArray("types") ||
      !record->getArray("entries") || !record->getArray("declarations") ||
      !candidate || !hasSingleElement(candidate.getBody()->getOperations()) ||
      !isa<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front()))
    return refuse();
  auto sourceContext = OracleVerificationContext::read(prepared);
  if (!sourceContext)
    return sourceContext.takeError();
  auto targetContext = OracleVerificationContext::read(candidate);
  if (!targetContext) {
    consumeError(targetContext.takeError());
    return error("oracle-common-body");
  }
  Codec codec(true, candidate);
  auto *types = record->getArray("types");
  if (types->size() > 4096)
    return error("oracle-realization-record-limit");
  llvm::DenseSet<Type> seen;
  auto decoded = importLogicalTypesData(candidate.getContext(), *types);
  if (!decoded) {
    consumeError(decoded.takeError());
    return refuse();
  }
  for (Type type : *decoded) {
    if (!seen.insert(type).second || failed(verifyRecordedType(type)))
      return refuse();
    codec.types.push_back(type);
  }
  std::vector<OracleCommonEntryRealization> entries;
  codec.item(*record->get("entries"), entries);
  if (!codec.valid)
    return refuse();
  if (auto e =
          checkOracleRealizationModel(*sourceContext, *targetContext, entries,
                                      *selections, policy.authentication))
    return e;
  auto expected = encode(prepared, candidate, entries, *selections, policy);
  if (!expected)
    return expected.takeError();
  if (!zkc::equalNaturalJson(*expected, *parsed))
    return refuse();
  return Error::success();
}
} // namespace zkc::protocol
