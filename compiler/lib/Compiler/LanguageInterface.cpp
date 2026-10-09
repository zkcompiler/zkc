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
Error preflight(StringRef bytes) {
  if (!json::isUTF8(bytes))
    return error("source.interface", "interface is not UTF-8");
  std::vector<std::optional<std::set<std::string>>> stack;
  unsigned nodes = 0;
  for (size_t i = 0; i < bytes.size();) {
    char c = bytes[i++];
    if (c == '{' || c == '[') {
      ++nodes;
      if (stack.size() == 256)
        return error("source.limit", "interface nesting limit exceeded");
      stack.push_back(c == '{'
                          ? std::optional<std::set<std::string>>(std::in_place)
                          : std::nullopt);
    } else if (c == '}' || c == ']') {
      if (stack.empty() || bool(stack.back()) != (c == '}'))
        return error("source.interface", "unbalanced interface JSON");
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
        return error("source.interface", "unterminated interface string");
      // JSON can spell one ASCII byte as six characters (\uXXXX). The
      // decoded string ceiling follows the native variant carrier limit.
      if (i - start - 1 > 6 * protocol::VariantSpellingBytes)
        return error("source.limit", "interface string limit exceeded");
      StringRef spelling = bytes.slice(start, ++i);
      if (!validStringEncoding(spelling))
        return error("source.interface", "invalid interface string encoding");
      size_t next = i;
      while (next < bytes.size() && isSpace(bytes[next]))
        ++next;
      if (next < bytes.size() && bytes[next] == ':') {
        if (stack.empty() || !stack.back())
          return error("source.interface", "object key outside object");
        auto parsed = json::parse(spelling);
        if (!parsed) {
          consumeError(parsed.takeError());
          return error("source.interface", "invalid interface object key");
        }
        auto key = parsed->getAsString();
        if (!key || !stack.back()->insert(key->str()).second)
          return error("source.interface", "duplicate interface key");
      }
    } else if (!isSpace(c) && c != ',' && c != ':') {
      ++nodes;
      size_t start = i - 1;
      while (i < bytes.size() && !isSpace(bytes[i]) &&
             !StringRef("[]{}\",:").contains(bytes[i]))
        ++i;
      if (i - start > 10)
        return error("source.limit", "interface scalar limit exceeded");
      auto token = bytes.slice(start, i);
      if (token != "true" && token != "false" && token != "null" &&
          ((token.size() > 1 && token.front() == '0') ||
           !all_of(token, [](char digit) { return isDigit(digit); })))
        return error("source.interface", "invalid interface numeric spelling");
    }
    if (nodes > 200000)
      return error("source.limit", "interface node limit exceeded");
  }
  return Error::success();
}
} // namespace
Expected<json::Value> detail::parseInterface(StringRef bytes,
                                             const Limits &limits) {
  if (auto error = checkLimits(limits))
    return std::move(error);
  if (bytes.size() > limits.interfaceBytes)
    return error("source.limit", "interface byte limit exceeded");
  if (auto error = preflight(bytes))
    return std::move(error);
  auto actual = json::parse(bytes);
  if (!actual) {
    consumeError(actual.takeError());
    return error("source.interface", "invalid interface JSON");
  }
  return actual;
}
Error detail::withInterface(
    StringRef original, StringRef bytes, const Limits &limits,
    ArrayRef<RelationAsset> assets,
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
  if (auto error = mathematical::checkFormulaDefinitions(*module, remaining))
    return error;
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
                                          ArrayRef<RelationAsset> assets) {
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
