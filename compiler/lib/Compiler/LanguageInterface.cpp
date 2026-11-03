#include "LanguageInterface.h"
#include "SourceView.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Layout.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
// LLVM JSON replaces duplicate object members. Reject them before parsing so a
// second spelling cannot silently replace an identity-bearing field.
Error preflight(StringRef bytes, size_t stringLimit, size_t nodeLimit,
                StringRef invalidCode) {
  if (!json::isUTF8(bytes))
    return error(invalidCode, "Entry JSON is not UTF-8");
  std::vector<std::optional<std::set<std::string>>> stack;
  size_t nodes = 0;
  bool invalidNumeric = false;
  for (size_t i = 0; i < bytes.size();) {
    char c = bytes[i++];
    if (c == '{' || c == '[') {
      ++nodes;
      if (stack.size() == 256)
        return error("source.limit", "Entry JSON nesting limit exceeded");
      stack.push_back(c == '{'
                          ? std::optional<std::set<std::string>>(std::in_place)
                          : std::nullopt);
    } else if (c == '}' || c == ']') {
      if (stack.empty() || bool(stack.back()) != (c == '}'))
        return error(invalidCode, "unbalanced Entry JSON");
      stack.pop_back();
    } else if (c == '"') {
      ++nodes;
      size_t start = i - 1;
      while (i < bytes.size() && bytes[i] != '"') {
        if (bytes[i] == '\\')
          ++i;
        ++i;
      }
      if (i >= bytes.size())
        return error(invalidCode, "unterminated Entry JSON string");
      // Metadata allows escaped variant spellings; executable carriers allow
      // larger embedded program/package strings under their document ceiling.
      if (i - start - 1 > stringLimit)
        return error("source.limit", "Entry JSON string limit exceeded");
      StringRef spelling = bytes.slice(start, ++i);
      if (!validStringEncoding(spelling))
        return error(invalidCode, "invalid Entry JSON string encoding");
      size_t next = i;
      while (next < bytes.size() && isSpace(bytes[next]))
        ++next;
      if (next < bytes.size() && bytes[next] == ':') {
        if (stack.empty() || !stack.back())
          return error(invalidCode, "object key outside object");
        auto parsed = json::parse(spelling);
        if (!parsed) {
          consumeError(parsed.takeError());
          return error(invalidCode, "invalid Entry JSON object key");
        }
        auto key = parsed->getAsString();
        if (!key || !stack.back()->insert(key->str()).second)
          return error(invalidCode, "duplicate Entry JSON key");
      }
    } else if (!isSpace(c) && c != ',' && c != ':') {
      ++nodes;
      size_t start = i - 1;
      while (i < bytes.size() && !isSpace(bytes[i]) &&
             !StringRef("[]{}\",:").contains(bytes[i]))
        ++i;
      if (i - start > 10)
        return error("source.limit", "Entry JSON scalar limit exceeded");
      auto token = bytes.slice(start, i);
      if (token != "true" && token != "false" && token != "null" &&
          ((token.size() > 1 && token.front() == '0') ||
           !all_of(token, [](char digit) { return isDigit(digit); })))
        invalidNumeric = true;
    }
    if (nodes > nodeLimit)
      return error("source.limit", "Entry JSON node limit exceeded");
  }
  if (invalidNumeric)
    return error(invalidCode, "invalid Entry JSON numeric spelling");
  return Error::success();
}
} // namespace
json::Value detail::encodeInterfaceOracle(const InterfaceOracle &oracle) {
  json::Array arguments;
  for (const auto &argument : oracle.arguments)
    arguments.push_back(
        argument.kind == protocol::TypeArgument::Kind::Nat
            ? json::Array{"nat", std::to_string(argument.natural)}
            : json::Array{"type", argument.type->spelling()});
  return json::Object{{"kind", oracle.kind},
                      {"arguments", std::move(arguments)}};
}
json::Value detail::encodeInterfaceSchema(const InterfaceSchema &s) {
  auto fields = [](ArrayRef<InterfaceField> fields) {
    json::Array result;
    for (const auto &f : fields) {
      json::Object field{
          {"name", f.name},
          {"offset", f.offset},
          {"public", f.isPublic},
          {"placement", f.placement ? encodeInterfacePlacement(*f.placement)
                                    : json::Value(nullptr)},
          {"schema", encodeInterfaceSchema(*f.schema)}};
      if (f.maximumRows)
        field["maximum_rows"] = std::to_string(*f.maximumRows);
      result.push_back(std::move(field));
    }
    return result;
  };
  json::Array alternatives, permissions, leaves, roles;
  for (const auto &a : s.alternatives)
    alternatives.push_back(
        json::Object{{"name", a.name}, {"fields", fields(a.fields)}});
  if (s.permissions.copy)
    permissions.push_back("Copy");
  if (s.permissions.drop)
    permissions.push_back("Drop");
  for (const auto &l : s.leaves)
    leaves.push_back(l);
  for (const auto &role : s.roles)
    roles.push_back(role);
  json::Object result{{"kind", typeKindName(s.kind)},
                      {"identity", s.identity},
                      {"type", s.type},
                      {"generated", s.generated.empty()
                                        ? json::Value(nullptr)
                                        : json::Value(s.generated)},
                      {"custody", s.custody},
                      {"sealed", s.sealed},
                      {"constructible", s.constructible},
                      {"permissions", std::move(permissions)},
                      {"roles", std::move(roles)},
                      {"element", s.element ? encodeInterfaceSchema(*s.element)
                                            : json::Value(nullptr)},
                      {"fields", fields(s.fields)},
                      {"alternatives", std::move(alternatives)},
                      {"leaves", std::move(leaves)}};
  if (s.oracle) {
    result["oracle"] = encodeInterfaceOracle(*s.oracle);
    result["data_schema"] = encodeInterfaceSchema(*s.oracleData);
  }
  if (s.maximum)
    result["maximum"] = std::to_string(*s.maximum);
  return result;
}
Expected<ValuePlacement>
detail::sourcePortPlacement(const Port &port,
                            const ProtocolPortLayout &native) {
  if (native.placement)
    return *native.placement;
  if (port.placement)
    return *port.placement;
  // API bridge for the existing ordinary and direct-handle native observer.
  // Distributed products require the new observer's checked placement/map.
  if (isLogicalValue(port.type) && !isOracleHandle(port.type))
    return error("source.interface",
                 "distributed native placement observation missing");
  if (!port.oracle)
    return ValuePlacement(DataPlacement{port.roles});
  std::vector<unsigned> receivers;
  for (unsigned role : port.roles)
    if (role != port.oracle->holder)
      receivers.push_back(role);
  return ValuePlacement(
      OraclePlacement{port.oracle->holder, std::move(receivers)});
}
Expected<std::vector<InterfaceComponent>>
detail::sourcePortComponents(const Port &port, const ProtocolPortLayout &native,
                             unsigned base, uint64_t &remaining) {
  std::vector<InterfaceComponent> result;
  auto append = [&](ArrayRef<unsigned> path, unsigned leaf, unsigned role,
                    InterfaceComponentFacet facet, unsigned index) -> Error {
    if (remaining < path.size() + 1)
      return error("source.limit", "component observation budget exceeded");
    remaining -= path.size() + 1;
    result.push_back({std::vector<unsigned>(path.begin(), path.end()), leaf,
                      role, facet, base + index});
    return Error::success();
  };
  auto finish = [&]() -> std::vector<InterfaceComponent> {
    for (auto begin = result.begin(); begin != result.end();) {
      auto end = begin + 1;
      while (end != result.end() && end->path == begin->path &&
             end->leaf == begin->leaf)
        ++end;
      std::stable_sort(begin, end, [](const auto &a, const auto &b) {
        return a.role < b.role;
      });
      begin = end;
    }
    return std::move(result);
  };
  for (const auto &c : native.components) {
    InterfaceComponentFacet facet;
    switch (c.facet) {
    case ProtocolComponentFacet::Data:
      facet = InterfaceComponentFacet::Data;
      break;
    case ProtocolComponentFacet::OracleData:
      facet = InterfaceComponentFacet::OracleData;
      break;
    case ProtocolComponentFacet::OracleAnchor:
      facet = InterfaceComponentFacet::OracleAnchor;
      break;
    case ProtocolComponentFacet::Custody:
      facet = InterfaceComponentFacet::Custody;
      break;
    }
    if (auto e = append(c.fieldPath, c.localLeaf, c.role, facet, c.nativeIndex))
      return std::move(e);
  }
  if (!native.components.empty() || native.leaves.empty())
    return finish();
  auto placed = sourcePortPlacement(port, native);
  if (!placed)
    return placed.takeError();
  if (std::holds_alternative<ProductPlacement>(placed->value))
    return error("source.interface",
                 "distributed native component observation missing");
  for (const auto &leaf : native.leaves) {
    auto selected = native.body;
    unsigned offset = 0;
    for (unsigned index : leaf.path) {
      if (!selected || index >= selected->fields.size())
        return error("source.interface", "native leaf path differs");
      offset += selected->fields[index].offset;
      selected = selected->fields[index].layout;
    }
    unsigned local = leaf.bodyOffset - offset;
    if (auto *data = std::get_if<DataPlacement>(&placed->value)) {
      for (unsigned role : data->roles)
        if (auto e = append(leaf.path, local, role,
                            local < selected->custodyCount
                                ? InterfaceComponentFacet::Custody
                                : InterfaceComponentFacet::Data,
                            leaf.nativeOffset))
          return std::move(e);
    } else {
      auto &oracle = std::get<OraclePlacement>(placed->value);
      if (auto e =
              append(leaf.path, local, oracle.holder,
                     InterfaceComponentFacet::OracleData, leaf.nativeOffset))
        return std::move(e);
      for (unsigned role : oracle.receivers)
        if (auto e = append(leaf.path, local, role,
                            InterfaceComponentFacet::OracleAnchor,
                            leaf.nativeOffset + 1))
          return std::move(e);
    }
  }
  return finish();
}
bool detail::logicalLayout(const Layout &s) {
  if (isOracleHandle(s.type) || s.type.kind == Type::Kind::LogicalRecord)
    return true;
  if (s.type.kind == Type::Kind::Array)
    return s.element && logicalLayout(*s.element);
  return s.type.kind == Type::Kind::Tuple &&
         llvm::any_of(s.fields,
                      [](const auto &f) { return logicalLayout(*f.layout); });
}
bool detail::logicalSchema(const InterfaceSchema &s) {
  if (s.oracle || s.kind == Type::Kind::LogicalRecord)
    return true;
  if (s.kind == Type::Kind::Array)
    return s.element && logicalSchema(*s.element);
  return s.kind == Type::Kind::Tuple &&
         llvm::any_of(s.fields,
                      [](const auto &f) { return logicalSchema(*f.schema); });
}
StringRef detail::componentFacetName(InterfaceComponentFacet facet) {
  switch (facet) {
  case InterfaceComponentFacet::Data:
    return "data";
  case InterfaceComponentFacet::OracleData:
    return "oracle_data";
  case InterfaceComponentFacet::OracleAnchor:
    return "oracle_anchor";
  case InterfaceComponentFacet::Custody:
    return "custody";
  }
  llvm_unreachable("unknown interface component facet");
}
json::Value detail::encodeInterfacePlacement(const ValuePlacement &p) {
  auto indices = [](ArrayRef<unsigned> values) {
    json::Array result;
    for (unsigned value : values)
      result.push_back(value);
    return result;
  };
  if (auto *data = std::get_if<DataPlacement>(&p.value))
    return json::Object{{"kind", "data"}, {"roles", indices(data->roles)}};
  if (auto *oracle = std::get_if<OraclePlacement>(&p.value))
    return json::Object{{"kind", "oracle"},
                        {"holder", oracle->holder},
                        {"receivers", indices(oracle->receivers)}};
  const auto &product = std::get<ProductPlacement>(p.value);
  json::Array fields;
  for (const auto &field : product.fields)
    fields.push_back(encodeInterfacePlacement(field));
  return json::Object{{"kind", "product"},
                      {"instance", product.instance},
                      {"arguments", indices(product.arguments)},
                      {"fields", std::move(fields)}};
}
Expected<ValuePlacement> detail::externalPlacement(const Layout &layout,
                                                   const ValuePlacement &p,
                                                   uint64_t &remaining,
                                                   const Limits &limits,
                                                   unsigned depth) {
  if (depth > limits.typeDepth || remaining == 0)
    return error("source.limit", "external placement traversal limit exceeded");
  --remaining;
  if (!std::holds_alternative<ProductPlacement>(p.value)) {
    uint64_t cost =
        std::holds_alternative<DataPlacement>(p.value)
            ? std::get<DataPlacement>(p.value).roles.size()
            : std::get<OraclePlacement>(p.value).receivers.size() + 1;
    if (cost > remaining)
      return error("source.limit", "external placement role budget exceeded");
    remaining -= cost;
    return p;
  }
  const auto &product = std::get<ProductPlacement>(p.value);
  // The internal instance is the snapshot lookup key; the external instance
  // is the schema's published revision-bound identity.
  auto identity = typeIdentity(layout.type);
  if (identity.size() + product.fields.size() + product.arguments.size() >
      remaining)
    return error("source.limit", "external placement identity limit exceeded");
  remaining -=
      identity.size() + product.fields.size() + product.arguments.size();
  if (product.instance != identity ||
      product.fields.size() !=
          (layout.type.kind == Type::Kind::Array ? 1 : layout.fields.size()))
    return error("source.interface",
                 "source placement instance or fields differ");
  ProductPlacement result{layout.identity.digest, product.arguments, {}};
  for (unsigned i = 0; i < product.fields.size(); ++i) {
    const auto &child = layout.type.kind == Type::Kind::Array
                            ? layout.element
                            : layout.fields[i].layout;
    if (!child)
      return error("source.interface", "array element layout missing");
    auto normalized = externalPlacement(*child, product.fields[i], remaining,
                                        limits, depth + 1);
    if (!normalized)
      return normalized.takeError();
    result.fields.push_back(std::move(*normalized));
  }
  return ValuePlacement(std::move(result));
}
Expected<json::Value> detail::parseInterface(StringRef bytes,
                                             const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  return parseEntryJson(bytes, limits.interfaceBytes,
                        6 * protocol::VariantSpellingBytes, InterfaceJsonNodes,
                        "source.interface");
}
Expected<json::Value> detail::parseEntryJson(StringRef bytes, size_t byteLimit,
                                             size_t stringLimit,
                                             size_t nodeLimit,
                                             StringRef invalidCode) {
  if (bytes.size() > byteLimit)
    return error("source.limit", "Entry JSON byte limit exceeded");
  if (auto error = preflight(bytes, stringLimit, nodeLimit, invalidCode))
    return std::move(error);
  auto actual = json::parse(bytes);
  if (!actual) {
    consumeError(actual.takeError());
    return error(invalidCode, "invalid Entry JSON");
  }
  return actual;
}
Error detail::withInterface(
    StringRef original, StringRef bytes, const Limits &limits,
    ArrayRef<Asset> assets,
    function_ref<Error(mlir::ModuleOp, LanguageInterface &&)> visit) {
  if (auto error = checkLimits(limits))
    return error;
  if (original.size() > limits.irBytes ||
      bytes.size() > limits.interfaceBytes || !mlirNestingWithinLimit(original))
    return error("source.limit", "original or interface limit exceeded");
  auto parsed = detail::parseInterface(bytes, limits);
  if (!parsed)
    return parsed.takeError();
  if (!json::isUTF8(original))
    return error("target.admission", "original is not UTF-8");
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  context.printOpOnDiagnostic(false);
  // Suppress detailed parser diagnostics; return a fixed refusal below.
  mlir::ScopedDiagnosticHandler handler(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  auto module = mlir::parseSourceString<mlir::ModuleOp>(original, &context);
  if (!module || mlir::failed(zkc::admitStage(*module)))
    return error("target.admission",
                 "original failed mathematical IR admission");
  uint64_t remaining = limits.work;
  auto checkMathematics = [&](mlir::ModuleOp subject) -> Error {
    return mathematical::checkFormulaDefinitions(subject, remaining);
  };
  if (parsed->getAsObject() && parsed->getAsObject()->get("selection")) {
    for (auto numeric : module->getOps<mlir::ModuleOp>()) {
      auto copy = mlir::OwningOpRef<mlir::ModuleOp>(
          mlir::cast<mlir::ModuleOp>(numeric->clone()));
      copy->getOperation()->removeAttr("entry.calculation");
      if (auto e = checkMathematics(*copy))
        return e;
    }
  } else if (auto e = checkMathematics(*module))
    return e;
  auto identity = toHex(SHA256::hash(arrayRefFromStringRef(original)), true);
  auto decoded =
      detail::decodeInterface(*module, identity, *parsed, limits, assets);
  if (!decoded)
    return decoded.takeError();
  return visit(*module, std::move(*decoded));
}
Error detail::withInterface(
    const CheckedOriginal &original, const Limits &limits,
    function_ref<Error(mlir::ModuleOp, const LanguageInterface &)> visit) {
  if (auto error = checkLimits(limits))
    return error;
  if (!limits.covers(original.admissionLimits()))
    return withInterface(original.bytes(), original.interfaceJson(), limits,
                         original.entry().project().assets(),
                         [&](mlir::ModuleOp module, LanguageInterface &&view) {
                           return visit(module, view);
                         });
  // The checked handle retains its parsed source and context. Inspect an
  // independent clone without reconstructing the admitted program from bytes.
  auto module = OriginalAccess::clone(original);
  return visit(*module, original.interface());
}
Expected<LanguageInterface> readInterface(StringRef original, StringRef bytes,
                                          const Limits &limits,
                                          ArrayRef<Asset> assets) {
  std::optional<LanguageInterface> result;
  if (auto error =
          detail::withInterface(original, bytes, limits, assets,
                                [&](mlir::ModuleOp, LanguageInterface &&view) {
                                  result = std::move(view);
                                  return Error::success();
                                }))
    return std::move(error);
  return std::move(*result);
}
Error checkInterface(const CheckedOriginal &original, StringRef bytes,
                     const Limits &limits) {
  auto actual = detail::parseInterface(bytes, limits);
  if (!actual)
    return actual.takeError();
  auto expected = json::parse(original.interfaceJson());
  if (!expected)
    return expected.takeError();
  if (!zkc::equalNaturalJson(*actual, *expected))
    return error(
        "source.interface",
        "interface does not match the retained original and selected Entry");
  return Error::success();
}
} // namespace zkc::language
