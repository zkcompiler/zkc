#include "ApplicationMapData.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
using namespace mlir;
namespace zkc::protocol::application_map {
namespace {
Expected<std::vector<unsigned>> indices(const json::Value &value) {
  auto *array = value.getAsArray();
  if (!array)
    return error("application-map-carrier");
  std::vector<unsigned> result;
  for (const auto &item : *array) {
    auto number = item.getAsUINT64();
    if (!number || *number > rowLimit)
      return error("application-map-carrier");
    result.push_back(*number);
  }
  return result;
}
std::vector<json::Value> types(const json::Value &value) {
  const auto &array = *value.getAsArray();
  return {array.begin(), array.end()};
}
std::vector<std::string> strings(const json::Value &value) {
  std::vector<std::string> result;
  for (const auto &item : *value.getAsArray())
    result.push_back(item.getAsString()->str());
  return result;
}
Expected<Block> readBlock(const json::Value &value,
                          std::vector<json::Value> inputs,
                          std::vector<json::Value> outputs, Budget &budget,
                          unsigned depth = 0) {
  auto *row = value.getAsArray();
  if (!row || row->size() != 3 || (*row)[0].getAsString() != "block")
    return error("application-map-carrier");
  if (depth > 32 || !budget.charge())
    return error("application-map-limit");
  Block result;
  result.inputs = std::move(inputs);
  result.outputs = std::move(outputs);
  for (const auto &item : *(*row)[1].getAsArray()) {
    const auto &instruction = *item.getAsArray();
    if (instruction.size() != 5)
      return error("application-map-carrier");
    if (!budget.charge())
      return error("application-map-limit");
    auto operands = indices(instruction[1]);
    if (!operands)
      return operands.takeError();
    Instruction next;
    next.descriptor = instruction[0];
    next.operands = std::move(*operands);
    next.results = types(instruction[2]);
    next.site = instruction[4].getAsString()->str();
    for (const auto &region : *instruction[3].getAsArray()) {
      const auto &nested = *region.getAsArray();
      auto body = readBlock(nested[2], types(nested[0]), types(nested[1]),
                            budget, depth + 1);
      if (!body)
        return body.takeError();
      next.regions.push_back(std::move(*body));
    }
    result.instructions.push_back(std::move(next));
  }
  result.terminator = (*row)[2];
  const auto &terminal = *result.terminator.getAsArray();
  if (terminal[0].getAsString() != "stop") {
    auto returned = indices(terminal[1]);
    if (!returned)
      return returned.takeError();
    result.returned = std::move(*returned);
  }
  return result;
}
} // namespace

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
  auto exported = exportStructuredSource(bytes, entry, context, profile);
  if (!exported)
    return exported.takeError();
  // This is exporter-owned JSON, never an untrusted substitute for the input.
  auto parsed = json::parse(exported->bytes);
  if (!parsed)
    return parsed.takeError();
  if (auto e = chargeTree(*parsed, budget))
    return std::move(e);
  View result;
  result.wire = std::move(*parsed);
  result.native = parseSourceString<ModuleOp>(bytes, &context);
  if (!result.native)
    return error("application-map-carrier");
  auto unit =
      cast<protocol_ir::ProtocolModuleOp>(result.native->getBody()->front());
  mathematical::NativeTypePolicies policies(unit);
  SymbolTable symbols(unit);
  const auto &slots = *result.wire.getAsArray();
  for (const auto &value : *slots[7].getAsArray()) {
    const auto &row = *value.getAsArray();
    Definition definition;
    definition.name = row[1].getAsString()->str();
    definition.declaration = value;
    unsigned bodySlot = 0;
    std::vector<json::Value> inputs, outputs;
    if (row[0].getAsString() == "function") {
      definition.kind = row[2].getAsString()->str();
      inputs = types(row[4]);
      outputs = types(row[5]);
      bodySlot = 9;
      if (definition.kind == "protocol") {
        const auto &interface = *row[6].getAsArray();
        definition.roles = strings(interface[1]);
        for (const auto &scope : *interface[2].getAsArray())
          definition.inputRoles.push_back(strings(scope));
        for (const auto &scope : *interface[3].getAsArray())
          definition.outputRoles.push_back(strings(scope));
        auto native =
            cast<protocol_ir::MathematicalOp>(symbols.lookup(definition.name));
        auto restricts = [&](Type type) -> Expected<bool> {
          if (isa<protocol_ir::ServiceReferenceType>(type))
            return false;
          if (isa<protocol_ir::OracleHandleType,
                  protocol_ir::OracleSequenceType>(type))
            return true;
          auto policy = policies.get(type);
          if (!policy)
            return error("application-map-unsupported", "port type policy");
          return policy->shared;
        };
        for (auto type : native.getFunctionType().getInputs()) {
          auto needed = restricts(type);
          if (!needed)
            return needed.takeError();
          definition.restrictInputs.push_back(*needed);
        }
        for (auto type : native.getFunctionType().getResults()) {
          auto needed = restricts(type);
          if (!needed)
            return needed.takeError();
          definition.restrictOutputs.push_back(*needed);
        }
      }
    } else if (row[0].getAsString() == "oracle") {
      definition.kind = "oracle";
      inputs = types(row[2]);
      bodySlot = 7;
    }
    if (bodySlot) {
      auto block = readBlock(row[bodySlot], std::move(inputs),
                             std::move(outputs), budget);
      if (!block)
        return block.takeError();
      definition.hasBody = true;
      definition.body = std::move(*block);
    }
    result.names.emplace(definition.name, result.definitions.size());
    result.definitions.push_back(std::move(definition));
  }
  return result;
}
Error compareInventory(const View &source, const View &candidate) {
  const auto &a = *source.wire.getAsArray();
  const auto &b = *candidate.wire.getAsArray();
  // Only actual definition bodies can change at this edge. Derived declaration
  // identities are retained because scoped helpers are retained exactly.
  for (unsigned slot : {0, 1, 3, 4, 5, 6, 8, 9, 10})
    if (!equalNaturalJson(a[slot], b[slot]))
      return error("application-map-correspondence", "declaration inventory");
  if (source.definitions.size() != candidate.definitions.size())
    return error("application-map-correspondence", "definition inventory");
  for (auto [left, right] : zip(source.definitions, candidate.definitions)) {
    auto x = *left.declaration.getAsArray();
    auto y = *right.declaration.getAsArray();
    if (left.kind != right.kind || left.hasBody != right.hasBody ||
        x.size() != y.size())
      return error("application-map-correspondence", "definition kind");
    if (left.hasBody && right.hasBody) {
      unsigned slot = left.kind == "oracle" ? 7 : 9;
      x[slot] = nullptr;
      y[slot] = nullptr;
    }
    if (!equalNaturalJson(json::Value(std::move(x)), json::Value(std::move(y))))
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
  return *(*instruction.descriptor.getAsArray())[0].getAsString();
}
StringRef callee(const Instruction &instruction) {
  return *(*instruction.descriptor.getAsArray())[1].getAsString();
}
} // namespace zkc::protocol::application_map
