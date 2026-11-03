#include "ApplicationMapData.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Compiler/SourceCorrespondence.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Protocol/IR/RoleAttributes.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
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
  result.publication = std::move(source->publication);
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
namespace {
std::string sha256(StringRef bytes) {
  return "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
bool exact(const json::Object *object,
           std::initializer_list<StringRef> fields) {
  return object && object->size() == fields.size() &&
         all_of(fields, [&](StringRef field) { return object->get(field); });
}
} // namespace
Expected<WrittenLinks> WrittenLinks::read(StringRef bytes, const View &source,
                                          StringRef originalBytes) {
  auto refuse = [](const Twine &detail) {
    return error("application-map-written", detail.str());
  };
  // The correspondence has its own publication ceiling and traversal budget.
  if (!source.publication.getAsArray() ||
      source.publication.getAsArray()->size() != 11)
    return refuse("original has no structured export");
  auto parsed =
      parseNaturalJson(bytes, 8 * 1024 * 1024, 4 * 64 + 32,
                       "application-map-written", "application-map-limit");
  if (!parsed)
    return parsed.takeError();
  Budget budget{8 * 1024 * 1024};
  if (auto e = chargeTree(*parsed, budget))
    return std::move(e);
  const auto *root = parsed->getAsObject();
  if (!exact(root, {"format", "admission", "source_ast", "bindings",
                    "instances", "instance_rows", "generated", "generated_rows",
                    "occurrences", "snapshot", "rows"}) ||
      root->getString("format") != "zkc.source-correspondence/0")
    return refuse("correspondence members differ");
  const auto *admission = root->getObject("admission");
  if (!exact(admission, {"format", "original_sha256", "protocol_symbol",
                         "interface_sha256", "capture", "installation"}) ||
      admission->getString("format") != "zkc.structured-source/0" ||
      !admission->getString("capture") || !admission->getString("installation"))
    return refuse("correspondence admission differs");
  if (admission->getString("original_sha256") != sha256(originalBytes) ||
      admission->getString("protocol_symbol") != source.entry)
    return refuse("correspondence names another original or entry");
  if (!equalNaturalJson(*root->get("snapshot"), source.publication))
    return refuse("correspondence snapshot is not this original's export");
  if (auto e = language::checkCorrespondenceInventory(*parsed))
    return refuse(toString(std::move(e)));
  WrittenLinks result;
  result.digest = sha256(bytes);
  result.subject = json::Object{
      {"capture", admission->getString("capture")->str()},
      {"installation", admission->getString("installation")->str()}};
  // Every written node an occurrence names must exist in the exported syntax.
  const auto *ast = root->getObject("source_ast");
  const auto *declarations = ast ? ast->getArray("declarations") : nullptr;
  if (!declarations)
    return refuse("correspondence syntax differs");
  std::set<std::string> written;
  for (const auto &item : *declarations) {
    const auto *declaration = item.getAsObject();
    auto owner = declaration ? declaration->getString("owner") : std::nullopt;
    const auto *list = declaration ? declaration->getArray("nodes") : nullptr;
    if (!owner || !list)
      return refuse("correspondence syntax differs");
    for (const auto &node : *list) {
      const auto *path =
          node.getAsObject() ? node.getAsObject()->get("path") : nullptr;
      if (!path)
        return refuse("correspondence syntax differs");
      written.insert(printJson(json::Array{*owner, *path}));
    }
  }
  for (const auto &item : *root->getArray("occurrences")) {
    const auto &occurrence = *item.getAsObject();
    if (!exact(&occurrence, {"definition", "site", "nodes"}))
      return refuse("occurrence members differ");
    json::Array nodes;
    for (const auto &node : *occurrence.getArray("nodes")) {
      const auto *address = node.getAsObject();
      if (!exact(address, {"owner", "path"}) || !address->getString("owner") ||
          !written.count(printJson(
              json::Array{*address->get("owner"), *address->get("path")})))
        return refuse("occurrence node does not resolve in the syntax");
      nodes.push_back(node);
    }
    result.nodes[{occurrence.getString("definition")->str(),
                  occurrence.getString("site")->str()}] = std::move(nodes);
  }
  // Inventory symbols resolve to exactly their snapshot rows.
  std::map<std::string, json::Array> rows;
  const auto &tables = *source.publication.getAsArray();
  for (unsigned table : {4, 5, 6, 7})
    for (unsigned i = 0; i < tables[table].getAsArray()->size(); ++i) {
      const auto &row = *(*tables[table].getAsArray())[i].getAsArray();
      rows[row[1].getAsString()->str()].push_back(json::Array{table, i});
    }
  auto resolve = [&](StringRef table, StringRef key,
                     const json::Array &entries) -> Error {
    const auto *associations = root->getArray(table);
    if (!associations || associations->size() != entries.size())
      return refuse(table + " differ");
    for (unsigned i = 0; i < entries.size(); ++i) {
      const auto *association = (*associations)[i].getAsObject();
      if (!exact(association, {key, "rows"}) ||
          association->getInteger(key) != int64_t(i))
        return refuse(table + " differ");
      auto symbol = entries[i].getAsObject()->getString("symbol");
      auto found = rows.find(symbol->str());
      json::Array expected =
          found == rows.end() ? json::Array{} : found->second;
      if (!equalNaturalJson(*association->get("rows"),
                            json::Value(std::move(expected))))
        return refuse(table + " do not resolve to snapshot rows");
    }
    return Error::success();
  };
  const auto *instances = root->getObject("instances");
  const auto *closed = instances ? instances->getArray("instances") : nullptr;
  if (!closed)
    return refuse("correspondence instances differ");
  for (const auto &item : *closed) {
    const auto &instance = *item.getAsObject();
    const auto *origin = instance.getObject("template");
    auto owner = origin ? origin->getString("owner") : std::nullopt;
    if (!owner)
      return refuse("correspondence instance template differs");
    result.instances[instance.getString("symbol")->str()] = owner->str();
  }
  for (const auto &item : *root->getArray("generated")) {
    const auto &entry = *item.getAsObject();
    if (!exact(&entry, {"symbol", "purpose", "part", "origins"}))
      return refuse("generated members differ");
    auto &origins = result.generated[entry.getString("symbol")->str()];
    for (const auto &origin : *entry.getArray("origins")) {
      if (!exact(origin.getAsObject(), {"definition", "site"}))
        return refuse("generated origin members differ");
      origins.emplace(origin.getAsObject()->getString("definition")->str(),
                      origin.getAsObject()->getString("site")->str());
    }
  }
  if (auto e = resolve("instance_rows", "instance", *closed))
    return std::move(e);
  if (auto e =
          resolve("generated_rows", "generated", *root->getArray("generated")))
    return std::move(e);
  return result;
}
json::Value WrittenLinks::reference() const {
  return json::Object{{"format", "zkc.source-correspondence/0"},
                      {"digest", digest}};
}
Expected<json::Value> WrittenLinks::link(const Definition &callee,
                                         StringRef caller,
                                         const Instruction *call) const {
  auto refuse = [](const Twine &detail) {
    return error("application-map-written", detail.str());
  };
  auto instance = instances.find(callee.name);
  auto helper = generated.find(callee.name);
  if ((instance == instances.end()) == (helper == generated.end()))
    return refuse("application callee is not one inventory entry");
  json::Value node = nullptr;
  if (!call) {
    // A root names its template owner's whole declaration.
    if (instance == instances.end())
      return json::Value(nullptr);
    node = json::Object{{"owner", instance->second}, {"path", json::Array{}}};
  } else {
    if (call->site.empty())
      return json::Value(nullptr);
    std::pair<std::string, std::string> occurrence{caller.str(), call->site};
    auto found = nodes.find(occurrence);
    if (found == nodes.end())
      return refuse("application site has no occurrence");
    if (helper != generated.end() && !helper->second.count(occurrence))
      return refuse("generated callee lacks this occurrence in its origins");
    if (found->second.size() != 1)
      return json::Value(nullptr);
    node = found->second.front();
  }
  return json::Value(json::Object{{"subject", json::Object(subject)},
                                  {"node", std::move(node)},
                                  {"instance", callee.name}});
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
  auto application = dyn_cast<protocol_ir::ApplyOp>(instruction.operation);
  return application ? application.getRolesAttr() : ArrayAttr();
}
bool sameDescriptor(const Instruction &source, const Instruction &candidate,
                    const Roles &roles) {
  if (source.operation->getName() != candidate.operation->getName())
    return false;
  auto attributes = [&](Operation *op, bool map) {
    NamedAttrList result(op->getAttrs());
    result.erase("site");
    result.erase("runtime.site");
    if (map)
      // Every declared role use an application renames, and nothing else.
      protocol_ir::renameRoleUses(op->getName(), result, [&](StringAttr role) {
        auto found = roles.find(role.str());
        return found == roles.end()
                   ? role
                   : StringAttr::get(op->getContext(), found->second);
      });
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
