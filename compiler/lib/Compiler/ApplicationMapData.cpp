#include "ApplicationMapData.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/STLExtras.h"
#include <functional>

using namespace llvm;
using namespace mlir;
namespace zkc::protocol::application_map {
const Definition *View::find(StringRef name) const {
  auto found = names.find(name.str());
  return found == names.end() ? nullptr : &definitions[found->second];
}
Error chargeTree(const json::Value &value, Budget &budget) {
  if (!budget.charge())
    return error("application-map-limit");
  if (const auto *array = value.getAsArray()) {
    for (const auto &item : *array)
      if (auto e = chargeTree(item, budget))
        return e;
  } else if (const auto *object = value.getAsObject()) {
    for (const auto &item : *object) {
      if (!budget.charge())
        return error("application-map-limit");
      if (auto e = chargeTree(item.second, budget))
        return e;
    }
  }
  return Error::success();
}
Expected<json::Value> parseRecord(StringRef bytes) {
  if (bytes.size() > byteLimit)
    return error("application-map-limit");
  // Bound allocation and metadata traversal before LLVM builds the tree. The
  // shared reader below additionally owns grammar, Unicode, duplicate decoded
  // keys, numeric tokens and lexical depth. Delimiters cost no metadata unit.
  unsigned tokens = 0;
  for (size_t i = 0; i < bytes.size();) {
    char c = bytes[i++];
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == ',' ||
        c == ':' || c == ']' || c == '}')
      continue;
    if (++tokens > 1000000)
      return error("application-map-limit");
    if (c == '"') {
      while (i < bytes.size()) {
        char next = bytes[i++];
        if (next == '\\' && i < bytes.size())
          ++i;
        else if (next == '"')
          break;
      }
    } else if (c != '[' && c != '{') {
      while (i < bytes.size() && bytes[i] != ',' && bytes[i] != ']' &&
             bytes[i] != '}' && bytes[i] != ':' && bytes[i] != ' ' &&
             bytes[i] != '\t' && bytes[i] != '\r' && bytes[i] != '\n')
        ++i;
    }
  }
  return parseNaturalJson(bytes, byteLimit, 64, "application-map-json",
                          "application-map-limit");
}
Expected<View> readView(StringRef bytes, StringRef entry, MLIRContext &context,
                        Budget &budget, StructuredSourceProfile profile) {
  auto source = readSourceView(bytes, entry, context, profile);
  if (!source)
    return source.takeError();
  View result;
  result.native = std::move(source->native);
  result.identity = std::move(source->identity);
  result.entry = std::move(source->entry);
  result.names = std::move(source->names);
  auto unit =
      cast<protocol_ir::ProtocolModuleOp>(result.native->getBody()->front());
  mathematical::NativeTypePolicies policies(unit);
  for (auto &value : source->definitions) {
    if (!budget.charge())
      return error("application-map-limit");
    Definition definition;
    static_cast<SourceDefinition &>(definition) = std::move(value);
    if (definition.kind == "protocol") {
      auto restricts = [&](Type type) -> Expected<bool> {
        if (isa<protocol_ir::ServiceReferenceType>(type))
          return false;
        if (isa<protocol_ir::OracleHandleType, protocol_ir::OracleSequenceType>(
                type))
          return true;
        auto policy = policies.get(type);
        if (!policy)
          return error("application-map-unsupported", "port type policy");
        return policy->shared;
      };
      for (Type type : definition.body.inputs) {
        auto needed = restricts(type);
        if (!needed)
          return needed.takeError();
        definition.restrictInputs.push_back(*needed);
      }
      for (Type type : definition.body.outputs) {
        auto needed = restricts(type);
        if (!needed)
          return needed.takeError();
        definition.restrictOutputs.push_back(*needed);
      }
    }
    result.definitions.push_back(std::move(definition));
  }
  return result;
}
Error compareInventory(const View &source, const View &candidate) {
  if (source.entry != candidate.entry ||
      source.native.get()->getAttrDictionary() !=
          candidate.native.get()->getAttrDictionary() ||
      source.definitions.size() != candidate.definitions.size())
    return error("application-map-correspondence", "definition inventory");
  for (auto [left, right] : zip(source.definitions, candidate.definitions)) {
    if (left.name != right.name || left.kind != right.kind ||
        left.hasBody != right.hasBody ||
        left.operation->getName() != right.operation->getName() ||
        left.operation->getAttrDictionary() !=
            right.operation->getAttrDictionary())
      return error("application-map-correspondence", "definition interface");
  }
  return Error::success();
}
Error compareNative(View &source, View &candidate) {
  auto before =
      cast<protocol_ir::ProtocolModuleOp>(source.native->getBody()->front());
  auto after =
      cast<protocol_ir::ProtocolModuleOp>(candidate.native->getBody()->front());
  auto &a = before.getBody().front();
  auto &b = after.getBody().front();
  if (before->getAttrDictionary() != after->getAttrDictionary() ||
      a.getOperations().size() != b.getOperations().size())
    return error("application-map-correspondence", "native inventory");
  for (auto [x, y] : zip(a, b)) {
    if (isa<protocol_ir::MathematicalOp>(x) &&
        isa<protocol_ir::MathematicalOp>(y)) {
      if (x.getAttrDictionary() != y.getAttrDictionary())
        return error("application-map-correspondence", "native interface");
      continue;
    }
    // In particular, inspect dormant scoped CFG plumbing that does not itself
    // have a logical row. No Location, symbol name or exported row authorizes
    // it.
    if (!OperationEquivalence::isEquivalentTo(
            &x, &y, OperationEquivalence::IgnoreLocations))
      return error("application-map-correspondence", "retained native body");
  }
  // This public comparison always reaches verifyPreparedValues, including when
  // no application is present. It reads actual native SSA independently of the
  // logical row comparison and never invokes expansion or a map producer.
  if (failed(mathematical::verifyProtocolPreparationPreserved(before, after)))
    return error("application-map-correspondence", "native prepared values");
  return Error::success();
}
json::Array encodePath(ArrayRef<unsigned> path) {
  json::Array result;
  for (unsigned item : path)
    result.push_back(std::to_string(item));
  return result;
}
json::Value encodeValue(const Value &value) {
  json::Array producer;
  if (value.argument)
    producer = json::Array{"argument", std::to_string(value.port)};
  else
    producer = json::Array{"result", std::to_string(value.instruction),
                           std::to_string(value.port)};
  return json::Object{{"definition", value.definition},
                      {"region", encodePath(value.region)},
                      {"producer", std::move(producer)},
                      {"components", json::Array{}}};
}
Path instructionPath(const Path &region, unsigned instruction) {
  Path result = region;
  result.push_back(instruction);
  return result;
}
Path regionPath(const Path &region, unsigned instruction, unsigned nested) {
  Path result = instructionPath(region, instruction);
  result.push_back(nested);
  return result;
}
ValueContext arguments(StringRef definition, const Path &region,
                       unsigned count) {
  ValueContext result;
  for (unsigned i = 0; i < count; ++i)
    result.push_back({definition.str(), region, true, 0, i});
  return result;
}
void prependResults(ValueContext &context, StringRef definition,
                    const Path &region, unsigned instruction, unsigned count) {
  for (unsigned i = count; i > 0; --i)
    context.push_front({definition.str(), region, false, instruction, i - 1});
}
StringRef opcode(const Instruction &instruction) {
  auto *op = instruction.operation;
  if (isa<protocol_ir::ApplyOp>(op))
    return "protocol_apply";
  if (isa<func::CallOp>(op) && !op->hasAttr("runtime.site"))
    return "call";
  if (isa<protocol_ir::RestrictRolesOp>(op))
    return "restrict";
  return op->getName().getStringRef();
}
StringRef callee(const Instruction &instruction) {
  return instruction.operation->getAttrOfType<FlatSymbolRefAttr>("callee")
      .getValue();
}
ArrayAttr applicationRoles(const Instruction &instruction) {
  return instruction.operation->getAttrOfType<ArrayAttr>("roles");
}
bool sameDescriptor(const Instruction &source, const Instruction &candidate,
                    const Roles &roles) {
  if (source.operation->getName() != candidate.operation->getName())
    return false;
  auto attributes = [&](Operation *op, bool map) {
    NamedAttrList result(op->getAttrs());
    result.erase("site");
    result.erase("runtime.site");
    std::function<Attribute(Attribute)> substitute = [&](Attribute attr) {
      if (auto name = dyn_cast<StringAttr>(attr)) {
        auto found = roles.find(name.str());
        if (found != roles.end())
          return Attribute(StringAttr::get(op->getContext(), found->second));
      } else if (auto array = dyn_cast<ArrayAttr>(attr)) {
        SmallVector<Attribute> values;
        for (Attribute value : array)
          values.push_back(substitute(value));
        return Attribute(ArrayAttr::get(op->getContext(), values));
      }
      return attr;
    };
    if (map)
      for (StringRef key : {"roles", "carried_roles", "receivers", "holder",
                            "sender", "receiver", "owner", "role"})
        if (auto attr = result.get(key))
          result.set(key, substitute(attr));
    return result.getDictionary(op->getContext());
  };
  return attributes(source.operation, true) ==
         attributes(candidate.operation, false);
}
Error chargeTypes(ArrayRef<Type> types, Budget &budget) {
  bool bounded = true;
  for (Type type : types)
    type.walk([&](Type) { bounded &= budget.charge(); },
              [&](Attribute) { bounded &= budget.charge(); });
  return bounded ? Error::success() : error("application-map-limit");
}
Error chargeInstruction(const Instruction &instruction, Budget &budget) {
  bool bounded = true;
  instruction.operation->getAttrDictionary().walk(
      [&](Attribute) { bounded &= budget.charge(); },
      [&](Type) { bounded &= budget.charge(); });
  if (!bounded)
    return error("application-map-limit");
  return chargeTypes(instruction.results, budget);
}
} // namespace zkc::protocol::application_map
