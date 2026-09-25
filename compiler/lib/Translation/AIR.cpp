#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Json.h"
#include "zkc/Translation/Relations.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;
using namespace mlir;
namespace zkc::relation {
namespace {
Attribute attribute(Builder &b, const json::Value &value) {
  if (auto text = value.getAsString())
    return b.getStringAttr(*text);
  if (auto number = value.getAsInteger())
    return b.getI64IntegerAttr(*number);
  if (const auto *array = value.getAsArray()) {
    SmallVector<Attribute> elements;
    for (const auto &item : *array)
      elements.push_back(attribute(b, item));
    return b.getArrayAttr(elements);
  }
  const auto *object = value.getAsObject();
  assert(object &&
         "AIR encoder only uses objects, arrays, strings and integers");
  SmallVector<NamedAttribute> fields;
  for (const auto &item : *object)
    fields.emplace_back(b.getStringAttr(item.first.str()),
                        attribute(b, item.second));
  return b.getDictionaryAttr(fields);
}

Expected<json::Value> data(Attribute attr, unsigned depth, size_t &remaining) {
  if (!remaining || depth > 8)
    return zkc::error("air-ir-limit");
  --remaining;
  if (auto text = dyn_cast<StringAttr>(attr)) {
    if (text.getValue().size() > 256 || !json::isUTF8(text.getValue()))
      return zkc::error("air-ir-attribute");
    return json::Value(text.getValue());
  }
  if (auto number = dyn_cast<IntegerAttr>(attr)) {
    if (!number.getType().isInteger(64) || number.getValue().isNegative())
      return zkc::error("air-ir-attribute");
    return json::Value(number.getInt());
  }
  if (auto array = dyn_cast<ArrayAttr>(attr)) {
    if (array.size() > remaining)
      return zkc::error("air-ir-limit");
    json::Array result;
    for (auto item : array) {
      auto value = data(item, depth + 1, remaining);
      if (!value)
        return value.takeError();
      result.push_back(std::move(*value));
    }
    return json::Value(std::move(result));
  }
  if (auto dict = dyn_cast<DictionaryAttr>(attr)) {
    if (dict.size() > remaining)
      return zkc::error("air-ir-limit");
    json::Object result;
    for (const auto &item : dict) {
      if (item.getName().size() > 64 || !json::isUTF8(item.getName().strref()))
        return zkc::error("air-ir-attribute");
      auto value = data(item.getValue(), depth + 1, remaining);
      if (!value)
        return value.takeError();
      result[item.getName().strref()] = std::move(*value);
    }
    return json::Value(std::move(result));
  }
  return zkc::error("air-ir-attribute");
}
} // namespace

Expected<AIR> readAIROperation(Operation *op) {
  if (!isa<AIRRelationOp>(op))
    return zkc::error("air-ir-operation");
  auto name = op->getAttrOfType<StringAttr>("sym_name");
  if (!name || name.getValue().empty())
    return zkc::error("air-ir-symbol");
  size_t remaining = 8 * AIRLimits::nodes + 8 * AIRLimits::constraints + 16;
  json::Object result{{"schema", "zkc.air.v1"}};
  for (const auto &item : op->getAttrs()) {
    auto key = item.getName().strref();
    if (key == "sym_name")
      continue;
    if (key != "field" && key != "columns" && key != "public_inputs" &&
        key != "constraints")
      return zkc::error("air-ir-attribute");
    auto value = data(item.getValue(), 0, remaining);
    if (!value)
      return value.takeError();
    result[key] = std::move(*value);
  }
  return readAIR(json::Value(std::move(result)));
}

Expected<OwningOpRef<ModuleOp>> importAIR(const AIR &relation, StringRef symbol,
                                          MLIRContext &context) {
  if (symbol.empty() || symbol.size() > 128 ||
      !(isAlpha(symbol.front()) || symbol.front() == '_') ||
      !all_of(symbol, [](char c) { return isAlnum(c) || c == '_'; }))
    return zkc::error("air-ir-symbol");
  context.getOrLoadDialect<RelationDialect>();
  OpBuilder b(&context);
  OwningOpRef<ModuleOp> module = ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToStart(module->getBody());
  OperationState state(b.getUnknownLoc(), AIRRelationOp::getOperationName());
  state.addAttribute("sym_name", b.getStringAttr(symbol));
  auto encoded = relation.encode();
  for (const auto &item : *encoded.getAsObject())
    if (item.first != "schema")
      state.addAttribute(item.first.str(), attribute(b, item.second));
  b.create(state);
  if (failed(verify(*module)))
    return zkc::error("air-ir");
  return module;
}
} // namespace zkc::relation

LogicalResult zkc::AIRRelationOp::verify() {
  auto relation = relation::readAIROperation(getOperation());
  if (!relation)
    return diagnostics::emit(emitOpError(), relation.takeError());
  return success();
}
