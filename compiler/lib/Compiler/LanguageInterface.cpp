#include "LanguageInterface.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/SHA256.h"
#include <set>

using namespace llvm;
namespace zkc::language {
namespace {
// LLVM JSON replaces duplicate object members. Reject them before parsing so a
// second spelling cannot silently replace an identity-bearing field.
Error preflight(StringRef bytes, size_t stringLimit, StringRef invalidCode) {
  if (!json::isUTF8(bytes))
    return error(invalidCode, "Entry JSON is not UTF-8");
  std::vector<std::optional<std::set<std::string>>> stack;
  unsigned nodes = 0;
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
    if (nodes > 200000)
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
    for (const auto &f : fields)
      result.push_back(
          json::Object{{"name", f.name},
                       {"offset", f.offset},
                       {"schema", encodeInterfaceSchema(*f.schema)}});
    return result;
  };
  json::Array alternatives, permissions, leaves;
  for (const auto &a : s.alternatives)
    alternatives.push_back(
        json::Object{{"name", a.name}, {"fields", fields(a.fields)}});
  if (s.permissions.copy)
    permissions.push_back("Copy");
  if (s.permissions.drop)
    permissions.push_back("Drop");
  for (const auto &l : s.leaves)
    leaves.push_back(l);
  json::Object result{{"kind", typeKindName(s.kind)},
                      {"identity", s.identity},
                      {"type", s.type},
                      {"custody", s.custody},
                      {"constructible", s.constructible},
                      {"permissions", std::move(permissions)},
                      {"fields", fields(s.fields)},
                      {"alternatives", std::move(alternatives)},
                      {"leaves", std::move(leaves)}};
  if (s.oracle)
    result["oracle"] = encodeInterfaceOracle(*s.oracle);
  return result;
}
Expected<json::Value> detail::parseInterface(StringRef bytes,
                                             const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  return parseEntryJson(bytes, limits.interfaceBytes,
                        6 * protocol::VariantSpellingBytes, "source.interface");
}
Expected<json::Value> detail::parseEntryJson(StringRef bytes, size_t byteLimit,
                                             size_t stringLimit,
                                             StringRef invalidCode) {
  if (bytes.size() > byteLimit)
    return error("source.limit", "Entry JSON byte limit exceeded");
  if (auto error = preflight(bytes, stringLimit, invalidCode))
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
  if (!module)
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
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry, mlir::MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  context.printOpOnDiagnostic(false);
  mlir::ScopedDiagnosticHandler handler(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  // The handle owns these exact admitted bytes. Reparse to keep visitor-owned
  // mutable MLIR out of the handle, without re-admitting its immutable facts.
  mlir::ParserConfig config(&context, false);
  auto module =
      mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), config);
  if (!module)
    return error("source.internal", "admitted original no longer parses");
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
  if (*actual != *expected)
    return error(
        "source.interface",
        "interface does not match the retained original and selected Entry");
  return Error::success();
}
} // namespace zkc::language
