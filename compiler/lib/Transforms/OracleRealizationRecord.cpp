#include "OracleAccounting.h"
#include "OracleCommonPlan.h"
#include "OracleNativeCommon.h"
#include "OracleOwnedRealization.h"
#include "OraclePublication.h"
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
  bool reading, valid = true, canonicalTypes = true,
                canonicalDescriptors = true, detachNative = true;
  unsigned remaining = 1000000;
  ModuleOp candidate;
  OracleNativeWork &work;
  SymbolTableCollection &symbols;
  std::vector<Type> types;
  llvm::DenseMap<Type, unsigned> typeIDs;
  unsigned usedTypes = 0;
  explicit Codec(bool reading, ModuleOp candidate, OracleNativeWork &work,
                 const OracleNativeSourcePreflight &preflight)
      : reading(reading), candidate(candidate), work(work),
        symbols(preflight.getSymbols()) {}
  bool spend(uint64_t amount = 1) {
    if (!valid || !work.charge(amount)) {
      valid = false;
      return false;
    }
    return true;
  }
  struct Object {
    Codec &codec;
    json::Object &value;
    unsigned fields = 0;
    template <class T> void field(StringRef name, T &item) {
      ++fields;
      if (!codec.spend(2 + name.size()))
        return;
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
      if (!codec.spend(2 + name.size()))
        return;
      if ((codec.reading) && !value.get(name))
        codec.valid = false;
    }
  };
  template <class F> void object(json::Value &node, F fields) {
    if (!spend() || !remaining) {
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
  template <class T> void writeItems(json::Value &node, ArrayRef<T> items) {
    assert(!reading);
    if (!valid || items.size() > remaining || !spend(1 + items.size())) {
      valid = false;
      return;
    }
    remaining -= items.size();
    node = json::Array{};
    for (const auto &element : items) {
      json::Value value(nullptr);
      item(value, element);
      node.getAsArray()->push_back(std::move(value));
      if (!valid)
        return;
    }
  }
  template <class T> void item(json::Value &node, const std::vector<T> &items) {
    writeItems(node, ArrayRef<T>(items));
  }
  template <class T> void item(json::Value &node, std::vector<T> &items) {
    if (!reading) {
      writeItems(node, ArrayRef<T>(items));
      return;
    }
    auto *array = node.getAsArray();
    if (!valid || !array || array->size() > remaining ||
        !spend(1 + array->size())) {
      valid = false;
      return;
    }
    remaining -= array->size();
    items.resize(array->size());
    for (auto [value, element] : zip(*array, items))
      item(value, element);
  }
  // Writing borrows the checked model. Only scalar handles need local values;
  // nested vectors and strings are never copied into an intermediate model.
  void item(json::Value &node, const std::string &value) {
    assert(!reading);
    if (spend(1 + 2 * value.size()))
      node = value;
  }
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<T, uint64_t> || std::is_same_v<T, unsigned> ||
              std::is_same_v<T, Type> || std::is_same_v<T, func::FuncOp> ||
              std::is_same_v<T, OracleControllerAccess> ||
              std::is_same_v<T, protocol_ir::OracleKindAttr>,
          int> = 0>
  void item(json::Value &node, const T &value) {
    assert(!reading);
    T local = value;
    item(node, local);
  }
  void item(json::Value &node, uint64_t &value) {
    if (!spend())
      return;
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
      else if (spend(1 + text->size()))
        value = text->str();
    } else
      item(node, static_cast<const std::string &>(value));
  }
  unsigned intern(Type type) {
    if (!type || !spend(2)) {
      valid = false;
      return 0;
    }
    auto found = typeIDs.try_emplace(type, types.size());
    if (found.second) {
      if (types.size() == 4096) {
        valid = false;
        return 0;
      }
      types.push_back(type);
    }
    return found.first->second;
  }
  bool useType(unsigned id) {
    if (id >= types.size() || !spend(2))
      return valid = false;
    auto inserted = typeIDs.try_emplace(types[id], id);
    if (inserted.second) {
      if (id != usedTypes)
        canonicalTypes = false;
      ++usedTypes;
    } else if (inserted.first->second != id)
      canonicalTypes = false;
    return true;
  }
  void item(json::Value &node, Type &type) {
    unsigned id = 0;
    if (!reading)
      id = intern(type);
    if (!valid)
      return;
    item(node, id);
    if (reading) {
      if (useType(id))
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
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
    if (reading) {
      auto name = node.getAsString();
      if (!name || !spend(1 + name->size())) {
        valid = false;
        return;
      }
      function = dyn_cast_or_null<func::FuncOp>(
          symbols.getSymbolTable(unit).lookup(*name));
      valid &= bool(function);
    } else {
      auto name = function.getSymName();
      if (!spend(1 + (detachNative ? 2 : 1) * name.size()))
        return;
      // Construct the owned JSON spelling directly from the native name;
      // no intermediate std::string is copied into a second string.
      node = detachNative ? json::Value(name.str()) : json::Value(name);
      valid &= function->getParentOp() == unit;
    }
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
  template <class T,
            std::enable_if_t<std::is_same_v<std::remove_const_t<T>, Argument>,
                             int> = 0>
  void item(json::Value &node, T &argument) {
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
      if (!spend(2 + kind.getIdentity().size() + kind.getArguments().size()))
        return;
      identity = kind.getIdentity().str();
      for (Attribute arg : kind.getArguments()) {
        if (auto typed = dyn_cast<TypeAttr>(arg)) {
          Type type = typed.getValue();
          unsigned id = intern(type);
          if (!valid)
            return;
          arguments.push_back({"type", id, 0});
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
    if (!spend(1 + arguments.size()))
      return;
    SmallVector<Attribute> attrs;
    for (const auto &arg : arguments) {
      if (arg.tag == "type") {
        if (!useType(arg.type))
          return;
        Type type = types[arg.type];
        attrs.push_back(TypeAttr::get(type));
      } else {
        attrs.push_back(IntegerAttr::get(
            IntegerType::get(candidate.getContext(), 64, IntegerType::Unsigned),
            arg.natural));
      }
    }
    // Kind policy and type construction use the active native debit scope.
    // These interned handles are not recursively exported or copied here.
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
  template <
      class T,
      std::enable_if_t<std::is_same_v<std::remove_const_t<T>, OracleQuerySize>,
                       int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("leaves", value.leaves);
      object.field("nodes", value.nodes);
    });
  }
  template <class T, std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                                     OracleQueryContinuation>,
                                      int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("constructor", value.constructor);
      object.field("query", value.query);
      object.field("record", value.record);
      object.field("sequence", value.sequence);
      object.field("previous_kinds", value.previousKinds);
    });
  }
  template <class T,
            std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                            OracleVirtualQueryFunction>,
                             int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("source", value.source);
      object.field("site", value.site);
      object.field("kind", value.kind);
      object.field("position", value.position);
    });
  }
  template <class T, std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                                     OracleVirtualFunctions>,
                                      int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("queries", value.queries);
      object.field("answer", value.answer);
    });
  }
  template <class T,
            std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                            OracleQueryControllerConstructor>,
                             int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("source", value.source);
      object.field("role", value.role);
      object.field("kind", value.kind);
      object.field("first_continuation", value.firstContinuation);
      object.field("lookup", value.lookup);
      object.field("functions", value.functions);
    });
  }
  template <class T, std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                                     OracleQueryController>,
                                      int> = 0>
  void item(json::Value &node, T &value) {
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
  template <class T, std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                                     OracleCommonController>,
                                      int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("role", value.role);
      object.field("kind", value.kind);
      object.field("access", value.access);
      object.field("body", value.body);
    });
  }
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleQueryDemand>, int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("frame", value.frame);
      object.field("sequence", value.sequence);
      object.field("state", value.state);
      object.field("initialize", value.initialize);
      object.field("advance", value.advance);
      object.field("consume", value.consume);
    });
  }
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleQueryResponse>, int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("answer", value.answer);
      object.field("authenticate", value.authenticate);
      object.field("resume", value.resume);
    });
  }
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleQueryPacket>, int> = 0>
  void item(json::Value &node, T &value) {
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
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleQueryWindow>, int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("request_sequence", value.requestSequence);
      object.field("answer_sequence", value.answerSequence);
      object.field("capacity", value.capacity);
      object.field("collect", value.collect);
      object.field("replay", value.replay);
      object.field("finish", value.finish);
    });
  }
  template <
      class T,
      std::enable_if_t<std::is_same_v<std::remove_const_t<T>, OracleQueryBatch>,
                       int> = 0>
  void item(json::Value &node, T &value) {
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
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleCommonRemote>, int> = 0>
  void item(json::Value &node, T &value) {
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
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleCommonBatch>, int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("remotes", value.remotes);
      object.field("body", value.body);
    });
  }
  template <
      class T,
      std::enable_if_t<
          std::is_same_v<std::remove_const_t<T>, OracleResultStore>, int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("constructor", value.constructor);
      object.field("role", value.role);
      object.field("port", value.port);
    });
  }
  template <class T, std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                                     OracleResultReference>,
                                      int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("result", value.result);
      object.field("role", value.role);
      object.field("stores", value.storePorts);
    });
  }
  template <class T, std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                                     OracleMerkleFunctions>,
                                      int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("position", value.position);
      object.field("commit", value.commit);
      object.field("open", value.open);
      object.field("authenticate", value.authenticate);
    });
  }
  template <
      class T,
      std::enable_if_t<std::is_same_v<std::remove_const_t<T>, OracleInputShape>,
                       int> = 0>
  void item(json::Value &node, T &value) {
    object(node, [&](Object &object) {
      object.field("anchor", value.anchor);
      object.field("port", value.port);
    });
  }
  template <class T,
            std::enable_if_t<std::is_same_v<std::remove_const_t<T>,
                                            OracleCommonEntryRealization>,
                             int> = 0>
  void item(json::Value &node, T &value) {
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
    if (auto service = dyn_cast<protocol_ir::ServiceReferenceType>(value)) {
      if (!spend(16 + 2 * service.getContract().size()))
        return nullptr;
      return json::Object{{"service", service.getContract().str()}};
    }
    return type(value);
  }
  json::Value kind(protocol_ir::OracleKindAttr value) {
    json::Value node(nullptr);
    item(node, value);
    return node;
  }
};
json::Array numbers(Codec &codec, ArrayRef<unsigned> values) {
  json::Array result;
  if (!codec.spend(1 + values.size()))
    return result;
  for (unsigned value : values)
    result.push_back(value);
  return result;
}
json::Array roles(Codec &codec, ArrayAttr values) {
  json::Array result;
  for (Attribute value : values) {
    if (!codec.spend(1 + cast<ArrayAttr>(value).size()))
      return {};
    json::Array names;
    for (Attribute role : cast<ArrayAttr>(value)) {
      if (!codec.spend(2 * cast<StringAttr>(role).getValue().size()))
        return {};
      names.push_back(cast<StringAttr>(role).getValue().str());
    }
    result.push_back(std::move(names));
  }
  return result;
}
Expected<json::Value> contracts(Codec &codec,
                                protocol_ir::MathematicalOp program,
                                const mathematical::OraclePortLayout &layout,
                                SymbolTableCollection &symbols) {
  // The native reader debits its actual selector/role/inventory work. It
  // borrows interned type handles rather than expanding unrelated descriptors.
  auto inventory = protocol_ir::readContracts(program, symbols);
  if (failed(inventory))
    return refuse();
  auto component = [&](const protocol_ir::ContractComponent &value) {
    if (!codec.spend(48 + 2 * value.role.getValue().size()))
      return json::Object{};
    return json::Object{{"direction", value.port.output ? "output" : "input"},
                        {"port", value.port.index},
                        {"role", value.role.getValue().str()},
                        {"type", codec.type(value.type)}};
  };
  auto selector =
      [&](const protocol_ir::ContractSelector &value) -> Expected<json::Value> {
    if (!codec.spend(32))
      return error("oracle-common-limit");
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
    if (!codec.spend(24 + 2 * value.relation.getValue().size() +
                     value.operands.size()))
      return error("oracle-common-limit");
    json::Array operands;
    for (const auto &operand : value.operands) {
      auto actual = selector(operand);
      if (!actual)
        return actual.takeError();
      operands.push_back(std::move(*actual));
    }
    return json::Object{{"relation", value.relation.getValue().str()},
                        {"operands", std::move(operands)}};
  };
  json::Array clauses, statements;
  for (const auto &clause : inventory->clauses) {
    if (!codec.spend(64 + 2 * clause.kind.getValue().size() +
                     2 * clause.name.getValue().size()))
      return error("oracle-common-limit");
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
    clauses.push_back(json::Object{{"kind", clause.kind.getValue().str()},
                                   {"name", clause.name.getValue().str()},
                                   {"subject", std::move(*subject)},
                                   {"residual", std::move(residual)},
                                   {"decision", std::move(decision)}});
  }
  llvm::DenseMap<Operation *, unsigned> positions;
  for (auto [i, operation] : enumerate(program.getBody().front())) {
    if (!codec.spend())
      return error("oracle-common-limit");
    positions[&operation] = i;
  }
  for (const auto &selection : inventory->statements) {
    if (!codec.spend(24))
      return error("oracle-common-limit");
    json::Value target(nullptr);
    if (selection.clause)
      target = *selection.clause;
    statements.push_back(
        json::Object{{"operation", positions.lookup(selection.statement)},
                     {"target", std::move(target)}});
  }
  if (!codec.spend(24))
    return error("oracle-common-limit");
  return json::Object{{"clauses", std::move(clauses)},
                      {"statements", std::move(statements)}};
}
Expected<json::Object>
derived(Codec &codec, ModuleOp prepared,
        const OracleCommonEntryRealization &entry,
        const OracleCommonAnalysis &plan, OracleNativeWork &,
        const OracleNativeSourcePreflight &sourcePreflight) {
  // The complete independent checker derived this exact immutable layout.
  // It is retained only with the checked pair, never accepted from wire data
  // or attached to a mutable inspection snapshot.
  const auto *requirements = plan.requirements.get();
  if (!requirements)
    return refuse();
  auto unit = cast<protocol_ir::ProtocolModuleOp>(prepared.getBody()->front());
  auto &symbols = sourcePreflight.getSymbols();
  auto program = cast<protocol_ir::MathematicalOp>(
      symbols.getSymbolTable(unit).lookup(entry.entry));
  if (!sourcePreflight.reserveTraversal(program))
    return error("oracle-common-limit");
  // Port extraction retains its local ceiling and debits actual visits and
  // copied pair rows through the same native scope. Nested logical types are
  // borrowed handles here; their descriptor expansion occurs in the codec.
  unsigned remaining = 100000;
  auto logical =
      mathematical::readOraclePortLayout(program, symbols, remaining);
  if (failed(logical))
    return refuse();
  auto pairs = [&](ArrayRef<mathematical::OraclePortPair> layout) {
    json::Array result;
    for (const auto &pair : layout) {
      if (!codec.spend(48 + 2 * pair.holder.getValue().size() +
                       pair.receivers.size()))
        return json::Array{};
      json::Array receivers;
      for (Attribute role : pair.receivers) {
        if (!codec.spend(2 * cast<StringAttr>(role).getValue().size()))
          return json::Array{};
        receivers.push_back(cast<StringAttr>(role).getValue().str());
      }
      result.push_back(json::Object{{"data", pair.data},
                                    {"anchor", pair.anchor},
                                    {"type", codec.type(pair.type)},
                                    {"holder", pair.holder.getValue().str()},
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
    if (!codec.spend(192 + item.holder.size() + item.site.size() +
                     item.declaration.size() + item.scheme.size() +
                     item.roles.size() + item.receivers.size()))
      return error("oracle-common-limit");
    json::Array owners, receivers;
    for (const auto &receiver : item.receivers) {
      if (!codec.spend(1 + receiver.size()))
        return error("oracle-common-limit");
      receivers.push_back(receiver);
    }
    for (const auto &owner : item.roles) {
      if (!codec.spend(40 + owner.role.size() + owner.fields.size()))
        return error("oracle-common-limit");
      json::Array fields;
      for (const auto &field : owner.fields) {
        if (!codec.spend(16 + field.name.size()))
          return error("oracle-common-limit");
        fields.push_back(json::Object{{"name", field.name},
                                      {"type", codec.type(field.type)}});
      }
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
                     {"path", numbers(codec, item.path)},
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
  for (const auto &item : plan.occurrences) {
    if (!codec.spend(32 + 2 * item.site.size() + 2 * item.purpose.size() +
                     2 * item.role.size()))
      return error("oracle-common-limit");
    occurrences.push_back(
        json::Object{{"site", item.site},
                     {"purpose", item.purpose},
                     {"role", item.role},
                     {"path", numbers(codec, item.sourcePath)}});
  }
  json::Array blocks;
  for (const auto &block : plan.queryBlocks) {
    if (!codec.spend(32 + block.queries.size()))
      return error("oracle-common-limit");
    json::Array queries;
    for (const auto &path : block.queries)
      queries.push_back(numbers(codec, path));
    json::Value capacity(nullptr);
    if (block.packetCapacity)
      capacity = *block.packetCapacity;
    blocks.push_back(json::Object{{"queries", std::move(queries)},
                                  {"packet_capacity", std::move(capacity)}});
  }
  auto signature = cast<FunctionType>(
      plan.attributes.getAs<TypeAttr>("function_type").getValue());
  if (!codec.spend(128 + signature.getNumInputs() + signature.getNumResults()))
    return error("oracle-common-limit");
  json::Array inputs, outputs;
  for (Type value : signature.getInputs())
    inputs.push_back(codec.port(value));
  for (Type value : signature.getResults())
    outputs.push_back(codec.port(value));
  if (!codec.valid)
    return error("oracle-common-limit");
  return json::Object{
      {"contracts", std::move(*logicalContracts)},
      {"constructors", std::move(constructors)},
      {"occurrences", std::move(occurrences)},
      {"query_blocks", std::move(blocks)},
      {"logical_interface",
       json::Object{{"inputs", std::move(logicalInputs)},
                    {"outputs", std::move(logicalOutputs)}}},
      {"interface",
       json::Object{
           {"inputs", std::move(inputs)},
           {"outputs", std::move(outputs)},
           {"input_roles",
            roles(codec, plan.attributes.getAs<ArrayAttr>("input_roles"))},
           {"output_roles",
            roles(codec, plan.attributes.getAs<ArrayAttr>("output_roles"))}}}};
}
// Bind all declaration names and symbolic generation slots, including helpers
// outlined inside another helper and binding names selected at actual uses.
// No opcode, executable operand, literal or body can be supplied by this table.
Expected<json::Array> declarations(ModuleOp candidate,
                                   const OracleNativeSourcePreflight &preflight,
                                   OracleNativeWork &work,
                                   const json::Array *match = nullptr,
                                   bool detachNative = true) {
  auto unit = cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  json::Array result;
  size_t declarationIndex = 0;
  bool mismatch = false;
  auto spelling = [&](StringRef text) {
    return detachNative ? json::Value(text.str()) : json::Value(text);
  };
  unsigned width = match || !detachNative ? 1 : 2;
  auto textMatches = [&](const json::Value &node, StringRef expected) {
    auto text = node.getAsString();
    return text && *text == expected;
  };
  for (auto &declaration : unit.getBody().front()) {
    auto name = SymbolTable::getSymbolName(&declaration).getValue();
    if (!work.charge(8 + width * name.size()))
      return error("oracle-common-limit");
    const json::Array *expectedReferences = nullptr;
    if (match) {
      if (declarationIndex >= match->size())
        return refuse();
      auto *row = (*match)[declarationIndex++].getAsArray();
      if (!row || row->size() != 2 || !textMatches((*row)[0], name) ||
          !(expectedReferences = (*row)[1].getAsArray()))
        return refuse();
    }
    json::Array references;
    size_t referenceIndex = 0;
    unsigned ordinal = 0;
    auto walked = declaration.walk<WalkOrder::PreOrder>([&](Operation *op) {
      if (!work.charge(1 + op->getAttrs().size()))
        return WalkResult::interrupt();
      unsigned current = ordinal++;
      for (auto attribute : op->getAttrs()) {
        auto leaves = preflight.borrowReferences(attribute.getValue());
        if (!leaves) {
          consumeError(leaves.takeError());
          return WalkResult::interrupt();
        }
        if (leaves->empty())
          continue;
        auto attributeName = attribute.getName().getValue();
        if (!work.charge(8 + width * attributeName.size()))
          return WalkResult::interrupt();
        const json::Array *expectedSymbols = nullptr;
        if (match) {
          auto *row = referenceIndex < expectedReferences->size()
                          ? (*expectedReferences)[referenceIndex++].getAsArray()
                          : nullptr;
          if (!row || row->size() != 3 || (*row)[0].getAsUINT64() != current ||
              !textMatches((*row)[1], attributeName) ||
              !(expectedSymbols = (*row)[2].getAsArray()) ||
              expectedSymbols->size() != leaves->size()) {
            mismatch = true;
            return WalkResult::interrupt();
          }
        }
        json::Array symbols;
        for (auto [i, reference] : enumerate(*leaves)) {
          auto root = reference.getRootReference().getValue();
          auto nested = reference.getNestedReferences();
          if (!work.charge(8 + width * root.size() + nested.size()))
            return WalkResult::interrupt();
          const json::Array *expectedParts =
              match ? (*expectedSymbols)[i].getAsArray() : nullptr;
          if (match &&
              (!expectedParts || expectedParts->size() != 1 + nested.size() ||
               !textMatches((*expectedParts)[0], root))) {
            mismatch = true;
            return WalkResult::interrupt();
          }
          json::Array parts;
          if (!match)
            parts.push_back(spelling(root));
          for (auto [j, part] : enumerate(nested)) {
            if (!work.charge(width * part.getValue().size()))
              return WalkResult::interrupt();
            if (match) {
              if (!textMatches((*expectedParts)[j + 1], part.getValue())) {
                mismatch = true;
                return WalkResult::interrupt();
              }
            } else
              parts.push_back(spelling(part.getValue()));
          }
          if (!match)
            symbols.push_back(std::move(parts));
        }
        if (!match) {
          json::Array row;
          row.push_back(current);
          row.push_back(spelling(attributeName));
          row.push_back(std::move(symbols));
          references.push_back(std::move(row));
        }
      }
      return WalkResult::advance();
    });
    if (walked.wasInterrupted())
      return mismatch ? refuse() : error("oracle-common-limit");
    if (match) {
      if (referenceIndex != expectedReferences->size())
        return refuse();
    } else {
      json::Array row;
      row.push_back(spelling(name));
      row.push_back(std::move(references));
      result.push_back(std::move(row));
    }
  }
  if (match && declarationIndex != match->size())
    return refuse();
  return result;
}
Expected<json::Value>
encode(ModuleOp prepared, ModuleOp candidate,
       ArrayRef<OracleCommonEntryRealization> entries,
       ArrayRef<OracleCommonAnalysis> analyses,
       ArrayRef<OracleRootSelection> selections,
       const OracleRealizationPolicy &policy, OracleNativeWork &work,
       const OracleNativeSourcePreflight &sourcePreflight,
       const OracleNativeSourcePreflight &candidatePreflight,
       json::Value *match = nullptr, Codec *decoded = nullptr,
       bool detachNative = true) {
  if (!prepared || !candidate || entries.size() != analyses.size() ||
      !hasSingleElement(candidate.getBody()->getOperations()) ||
      !isa<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front()))
    return refuse();
  if (auto e = checkOracleNativePreflight(prepared, work, &sourcePreflight))
    return std::move(e);
  if (auto e = checkOracleNativePreflight(candidate, work, &candidatePreflight))
    return std::move(e);
  // The codec borrows the checked model. It debits each field/container before
  // constructing JSON; declarations separately debit their actual native walk.
  // There is no whole-IR clone or traversal to reserve at this boundary.
  Codec codec(false, candidate, work, candidatePreflight);
  codec.detachNative = detachNative;
  json::Value encoded(nullptr);
  auto *entryNodes = match ? match->getAsObject()->get("entries") : &encoded;
  if (match) {
    assert(decoded && decoded->valid);
    if (!work.charge(1 + decoded->usedTypes))
      return error("oracle-common-limit");
    codec.types.assign(decoded->types.begin(),
                       decoded->types.begin() + decoded->usedTypes);
    codec.typeIDs = std::move(decoded->typeIDs);
    // Decoding already checked every metadata field's closed schema, spelling,
    // exact live symbol and canonical first-use type ID. The full independent
    // body check validated that decoded model. Only derived fields remain to
    // compare; rebuilding the same metadata cannot add independent evidence.
  } else
    codec.writeItems(*entryNodes, entries);
  if (!codec.valid)
    return work.exhausted ? error("oracle-common-limit") : refuse();
  for (auto [node, entry, plan] :
       zip(*entryNodes->getAsArray(), entries, analyses)) {
    auto fields = derived(codec, prepared, entry, plan, work, sourcePreflight);
    if (!fields)
      return fields.takeError();
    for (auto &field : *fields) {
      if (match) {
        auto *actual = node.getAsObject()->get(field.first);
        if (!actual)
          return refuse();
        auto equal = equalOracleRecordWithWork(field.second, *actual, work);
        if (!equal)
          return equal.takeError();
        if (!*equal)
          return refuse();
      } else
        (*node.getAsObject())[field.first] = std::move(field.second);
    }
  }
  if (!codec.valid)
    return work.exhausted ? error("oracle-common-limit") : refuse();
  json::Array types;
  if (match) {
    // Every parsed descriptor occurrence was independently decoded, formed and
    // checked for canonical spelling. Metadata and derived fields establish
    // canonical first use against the actual model. Compare the entire native
    // inventory, including unused/extra rows, without rebuilding that tree.
    if (!work.charge(1 + codec.types.size()))
      return error("oracle-common-limit");
    if (!equal(codec.types, decoded->types))
      return refuse();
  } else {
    auto written =
        writeOracleRecordedTypesWithWork(TypeRange(codec.types), work);
    if (!written)
      return written.takeError();
    types = std::move(*written);
  }
  json::Array roots;
  for (const auto &selection : selections) {
    const auto &choice = selection.realization;
    if (!codec.spend(96 + 2 * selection.entry.size() +
                     2 * choice.scheme.size()))
      return error("oracle-common-limit");
    roots.push_back(json::Object{
        {"entry", selection.entry},
        {"path", numbers(codec, selection.path)},
        {"scheme", choice.scheme},
        {"grouping", choice.grouping == OracleLeafGrouping::Individual
                         ? "individual"
                         : "antipodal-pairs"},
        {"order", choice.order == OracleLeafOrder::Natural ? "natural"
                                                           : "bit-reversed"}});
  }
  auto declarationInventory = declarations(
      candidate, candidatePreflight, work,
      match ? match->getAsObject()->getArray("declarations") : nullptr,
      detachNative);
  if (!declarationInventory)
    return declarationInventory.takeError();
  if (!codec.spend(128))
    return error("oracle-common-limit");
  json::Value selection = json::Object{
      {"order", policy.order == OracleQueryOrder::Unrestricted
                    ? "unrestricted"
                    : "after-final-draw"},
      {"authentication", policy.authentication == OracleAuthentication::PerQuery
                             ? "per-query"
                             : "atomic-blocks"},
      {"roots", std::move(roots)}};
  if (match) {
    // Closed-schema decoding and the complete independent check validated
    // metadata. Compare only independently derived fields and inventories.
    auto equalField = [&](StringRef key, const json::Value &expected) -> Error {
      auto *actual = match->getAsObject()->get(key);
      if (!actual)
        return refuse();
      auto equal = equalOracleRecordWithWork(expected, *actual, work);
      if (!equal)
        return equal.takeError();
      return *equal ? Error::success() : refuse();
    };
    if (auto e = equalField("selection", selection))
      return std::move(e);
    // The declaration walk compared exact rows directly without allocating a
    // duplicate inventory and traversing it again for equality.
    return json::Value(nullptr);
  }
  return json::Object{{"format", "zkc.oracle-realization/0"},
                      {"selection", std::move(selection)},
                      {"types", std::move(types)},
                      {"entries", std::move(encoded)},
                      {"declarations", std::move(*declarationInventory)}};
}
Expected<OracleRealizationPublication>
publishOracleRecord(ModuleOp prepared, ModuleOp candidate,
                    ArrayRef<OracleCommonEntryRealization> entries,
                    ArrayRef<OracleCommonAnalysis> analyses,
                    ArrayRef<OracleRootSelection> selections,
                    const OracleRealizationPolicy &policy,
                    OracleNativeWork &work,
                    const OracleNativeSourcePreflight &sourcePreflight,
                    const OracleNativeSourcePreflight &candidatePreflight,
                    bool detachNative = true) {

  auto record = encode(prepared, candidate, entries, analyses, selections,
                       policy, work, sourcePreflight, candidatePreflight,
                       nullptr, nullptr, detachNative);
  if (!record)
    return record.takeError();
  // The closed encoder detaches every dynamic spelling at construction. Its
  // other StringRefs are permanent schema/catalog literals. No caller-supplied
  // ownership claim or second string-copy traversal enters this boundary.

  auto bytes = serializeOraclePublication(*record, work);

  if (!bytes)
    return bytes.takeError();
  return OracleRealizationPublication{std::move(*record), std::move(*bytes)};
}

} // namespace
// Private production codec phases. The wire reader and publisher both call
// these before any recursive type conversion or formation allocation.
Expected<json::Array> writeOracleRecordedTypesWithWork(TypeRange types,
                                                       OracleNativeWork &work) {
  return oracleExpectedWithWork(work, [&]() -> Expected<json::Array> {
    if (types.size() > 4096)
      return error("oracle-realization-record-limit");
    if (!work.charge(1 + types.size()))
      return error("oracle-common-limit");
    for (Type type : types)
      if (failed(verifyRecordedType(type)))
        return refuse();
    // The codec debits every actual expanded occurrence before allocating its
    // tagged rows. Native verification/construction uses the same allowance.
    // No separate depth-weighted simulation or second tree walk is needed.
    return exportLogicalTypesData(types);
  });
}
Expected<SmallVector<Type>>
readOracleRecordedTypesWithWork(MLIRContext *context, const json::Array &types,
                                OracleNativeWork &work, bool *canonical) {
  return oracleExpectedWithWork(work, [&]() -> Expected<SmallVector<Type>> {
    if (types.size() > 4096)
      return error("oracle-realization-record-limit");
    if (!work.charge(1 + types.size()))
      return error("oracle-common-limit");
    auto decoded = importLogicalTypesData(context, types, canonical);
    if (!decoded) {
      consumeError(decoded.takeError());
      return refuse();
    }
    llvm::DenseSet<Type> seen;
    for (Type type : *decoded) {
      if (!work.charge(2))
        return error("oracle-common-limit");
      if (!seen.insert(type).second || failed(verifyRecordedType(type)))
        return refuse();
    }
    return std::move(*decoded);
  });
}
Expected<OracleRealizationPublication>
exportOracleRealization(ModuleOp prepared,
                        const OracleCommonRealization &actual,
                        const OracleRealizationPolicy &policy) {
  OracleNativeWork work;
  return exportOracleRealizationWithWork(prepared, actual, policy, work);
}
Expected<OracleRealizationPublication> exportOracleRealizationWithWork(
    ModuleOp prepared, const OracleCommonRealization &actual,
    const OracleRealizationPolicy &policy, OracleNativeWork &work) {
  return oracleExpectedWithWork(
      work, [&]() -> Expected<OracleRealizationPublication> {
        auto sourcePreflight =
            OracleNativeSourcePreflight::read(prepared, work);
        if (!sourcePreflight)
          return sourcePreflight.takeError();
        auto candidatePreflight =
            OracleNativeSourcePreflight::read(actual.module.get(), work);
        if (!candidatePreflight)
          return candidatePreflight.takeError();
        std::vector<OracleCommonAnalysis> analyses;
        std::vector<OracleRootSelection> selections;
        auto checked = checkOracleRealizationWithWork(
            prepared, actual, policy, work, &*sourcePreflight,
            &*candidatePreflight, &analyses, &selections);
        if (!checked)
          return checked.takeError();
        return publishOracleRecord(prepared, actual.module.get(),
                                   actual.entries, analyses, selections, policy,
                                   work, *sourcePreflight, *candidatePreflight);
      });
}

Expected<OracleRealizationPublication>
OracleOwnedRealization::publish(OracleNativeWork &work) const {
  return oracleExpectedWithWork(
      work, [&]() -> Expected<OracleRealizationPublication> {
        // Only the private creator can reach this method; its two subjects,
        // policy, associations and independent analyses have never escaped or
        // been mutated.
        return publishOracleRecord(actual.original.get(), actual.module.get(),
                                   actual.entries, analyses, selections, policy,
                                   work, sourcePreflight, candidatePreflight);
      });
}

Expected<std::string>
serializeOracleRealization(ModuleOp prepared,
                           const OracleCommonRealization &actual,
                           const OracleRealizationPolicy &policy) {
  OracleNativeWork work;
  return oracleExpectedWithWork(work, [&]() -> Expected<std::string> {
    auto sourcePreflight = OracleNativeSourcePreflight::read(prepared, work);
    if (!sourcePreflight)
      return sourcePreflight.takeError();
    auto candidatePreflight =
        OracleNativeSourcePreflight::read(actual.module.get(), work);
    if (!candidatePreflight)
      return candidatePreflight.takeError();
    std::vector<OracleCommonAnalysis> analyses;
    std::vector<OracleRootSelection> selections;
    auto checked = checkOracleRealizationWithWork(
        prepared, actual, policy, work, &*sourcePreflight, &*candidatePreflight,
        &analyses, &selections);
    if (!checked)
      return checked.takeError();
    // Only bytes escape. Native names can borrow the exact immutable checked
    // modules through this serialization, instead of creating an owned JSON
    // string tree that would immediately be discarded. Public data export
    // and persistent owned publication keep their detached spellings.
    auto publication = publishOracleRecord(
        prepared, actual.module.get(), actual.entries, analyses, selections,
        policy, work, *sourcePreflight, *candidatePreflight, false);
    if (!publication)
      return publication.takeError();
    return std::move(publication->bytes);
  });
}
Error checkOracleRealization(ModuleOp prepared, ModuleOp candidate,
                             StringRef text,
                             const OracleRealizationPolicy &policy) {
  OracleNativeWork work;
  return checkOracleRealizationRecordWithWork(prepared, candidate, text, policy,
                                              work);
}
Error checkOracleRealizationRecordWithWork(
    ModuleOp prepared, ModuleOp candidate, StringRef text,
    const OracleRealizationPolicy &policy, OracleNativeWork &preflight) {
  return oracleVerificationWithWork(preflight, [&]() -> Error {
    auto sourcePreflight =
        OracleNativeSourcePreflight::read(prepared, preflight);
    if (!sourcePreflight)
      return sourcePreflight.takeError();
    auto candidatePreflight =
        OracleNativeSourcePreflight::read(candidate, preflight);
    if (!candidatePreflight)
      return candidatePreflight.takeError();
    auto selections = resolveOracleRealizationSelectionWithWork(
        prepared, policy, preflight, *sourcePreflight);
    if (!selections)
      return selections.takeError();

    auto parsed = parseOracleRecordWithWork(text, preflight);

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
    auto sourceContext =
        OracleVerificationContext::read(prepared, preflight, *sourcePreflight);
    if (!sourceContext)
      return sourceContext.takeError();
    auto targetContext = OracleVerificationContext::readCandidate(
        candidate, preflight, *candidatePreflight);
    if (!targetContext) {
      if (preflight.exhausted)
        return targetContext.takeError();
      consumeError(targetContext.takeError());
      return error("oracle-common-body");
    }

    Codec codec(true, candidate, preflight, *candidatePreflight);
    auto *types = record->getArray("types");
    if (types->size() > 4096)
      return error("oracle-realization-record-limit");
    auto decoded = readOracleRecordedTypesWithWork(
        candidate.getContext(), *types, preflight, &codec.canonicalDescriptors);
    if (!decoded)
      return decoded.takeError();
    codec.types.assign(decoded->begin(), decoded->end());
    std::vector<OracleCommonEntryRealization> entries;
    codec.item(*record->get("entries"), entries);
    if (!codec.valid)
      return preflight.exhausted ? error("oracle-common-limit") : refuse();
    std::vector<OracleCommonAnalysis> analyses;

    if (auto e = checkOracleRealizationModel(
            *sourceContext, *targetContext, entries, *selections,
            policy.authentication, nullptr, &preflight, &*sourcePreflight,
            &*candidatePreflight, &analyses))
      return e;
    // Preserve semantic body refusal precedence for a decoded model. A
    // removed earlier row may also change canonical first-use type ordering.
    if (!codec.canonicalTypes || !codec.canonicalDescriptors)
      return refuse();

    auto expected = encode(prepared, candidate, entries, analyses, *selections,
                           policy, preflight, *sourcePreflight,
                           *candidatePreflight, &*parsed, &codec);
    if (!expected)
      return expected.takeError();

    return Error::success();
  });
}
} // namespace zkc::protocol
