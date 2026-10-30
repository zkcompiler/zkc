#include "zkc/Dialect/Data/Layout.h"
#include "Structure.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Bindings.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSwitch.h"

using namespace mlir;
namespace zkc::data {
namespace {
bool text(StringAttr value) {
  return value && !value.getValue().empty() &&
         llvm::json::isUTF8(value.getValue());
}
bool knownKind(StringRef kind) {
  return llvm::StringSwitch<bool>(kind)
      .Cases({"boolean", "index", "field", "group"}, true)
      .Cases({"unit", "tuple", "array", "record"}, true)
      .Cases({"variant", "associated", "builtin"}, true)
      .Default(false);
}
bool formedFields(ArrayRef<LayoutFieldAttr> fields, uint64_t offset = 0) {
  llvm::SmallDenseSet<StringAttr, 8> names;
  for (auto field : fields) {
    if (!field || !names.insert(field.getName()).second ||
        field.getOffset() != offset)
      return false;
    offset += field.getLayout().getLeaves().size();
  }
  return true;
}
} // namespace
LogicalResult LayoutFieldAttr::verify(function_ref<InFlightDiagnostic()> emit,
                                      StringAttr name, uint64_t offset,
                                      LayoutAttr layout) {
  if (!text(name) || !layout || offset > 200000)
    return emit() << "invalid logical layout field";
  return success();
}
LogicalResult
LayoutAlternativeAttr::verify(function_ref<InFlightDiagnostic()> emit,
                              StringAttr name,
                              ArrayRef<LayoutFieldAttr> fields) {
  if (!text(name) || !formedFields(fields))
    return emit() << "invalid logical layout alternative";
  return success();
}
LogicalResult LayoutAttr::verify(function_ref<InFlightDiagnostic()> emit,
                                 StringAttr kind, StringAttr identity,
                                 StringAttr displayType, bool custody,
                                 bool /*constructible*/, bool copy, bool drop,
                                 ArrayRef<LayoutFieldAttr> fields,
                                 ArrayRef<LayoutAlternativeAttr> alternatives,
                                 ArrayRef<Type> leaves) {
  if (!text(kind) || !knownKind(kind.getValue()) || !text(identity) ||
      identity.getValue().size() != 64 ||
      !llvm::all_of(
          identity.getValue(),
          [](char c) { return llvm::isDigit(c) || (c >= 'a' && c <= 'f'); }) ||
      !text(displayType) || (copy && !drop) ||
      !formedFields(fields, custody ? 1 : 0))
    return emit() << "invalid logical layout metadata";
  bool variant = kind.getValue() == "variant";
  if (variant != !alternatives.empty() || (variant && !fields.empty()))
    return emit() << "logical alternatives require a variant layout";
  llvm::SmallDenseSet<StringAttr, 8> names;
  for (auto alternative : alternatives)
    if (!alternative || !names.insert(alternative.getName()).second)
      return emit() << "duplicate or missing logical alternative";
  if (llvm::any_of(leaves, [](Type type) { return !type; }))
    return emit() << "missing logical leaf type";
  // Formation exposes the whole tree and bounds expanded work. Source and
  // stage admission still check native flattening and construction authority.
  SmallVector<Attribute> attrs{kind, identity, displayType};
  llvm::append_range(attrs, fields);
  llvm::append_range(attrs, alternatives);
  return detail::verifyStructure(emit, attrs, leaves);
}
LogicalResult ValueType::verify(function_ref<InFlightDiagnostic()> emit,
                                LayoutAttr layout) {
  if (!layout || layout.getKind().getValue() == "boolean" ||
      layout.getKind().getValue() == "index")
    return emit() << "logical value requires a nonscalar layout";
  return success();
}
Type valueType(LayoutAttr layout) {
  if (!layout)
    return {};
  auto *context = layout.getContext();
  if (layout.getKind().getValue() == "boolean")
    return IntegerType::get(context, 1);
  if (layout.getKind().getValue() == "index")
    return IntegerType::get(context, 64);
  return ValueType::get(context, layout);
}
namespace {
class LayoutImport {
  Builder builder;
  unsigned remaining = 200000;
  size_t bytes = 0;
  StringAttr string(const llvm::json::Object &object, StringRef key) {
    auto value = object.getString(key);
    if (!value || value->empty() || !llvm::json::isUTF8(*value))
      return {};
    bytes += value->size();
    return bytes <= 64 * 1024 * 1024 ? builder.getStringAttr(*value)
                                     : StringAttr{};
  }
  bool fields(const llvm::json::Array &array,
              SmallVectorImpl<LayoutFieldAttr> &result, unsigned depth) {
    for (const auto &value : array) {
      auto *object = value.getAsObject();
      if (!object || object->size() != 3 || !remaining--)
        return false;
      auto name = string(*object, "name");
      auto offset = object->getInteger("offset");
      auto *schema = object->get("schema");
      if (!name || !offset || *offset < 0 || !schema)
        return false;
      auto child = read(*schema, depth + 1);
      if (!child)
        return false;
      auto field = LayoutFieldAttr::getChecked(builder.getUnknownLoc(),
                                               builder.getContext(), name,
                                               uint64_t(*offset), child);
      if (!field)
        return false;
      result.push_back(field);
    }
    return true;
  }

public:
  explicit LayoutImport(MLIRContext *context) : builder(context) {}
  LayoutAttr read(const llvm::json::Value &value, unsigned depth = 0) {
    auto *object = value.getAsObject();
    if (!object || object->size() != 9 || depth >= 64 || !remaining--)
      return {};
    auto kind = string(*object, "kind"), identity = string(*object, "identity"),
         display = string(*object, "type");
    auto custody = object->getBoolean("custody"),
         constructible = object->getBoolean("constructible");
    auto *permissions = object->getArray("permissions"),
         *fieldRows = object->getArray("fields"),
         *alternativeRows = object->getArray("alternatives"),
         *leafRows = object->getArray("leaves");
    if (!kind || !identity || !display || !custody || !constructible ||
        !permissions || !fieldRows || !alternativeRows || !leafRows)
      return {};
    bool copy = false, drop = false;
    if (permissions->size() == 2 && (*permissions)[0].getAsString() == "Copy" &&
        (*permissions)[1].getAsString() == "Drop")
      copy = drop = true;
    else if (permissions->size() == 1 &&
             permissions->front().getAsString() == "Drop")
      drop = true;
    else if (!permissions->empty())
      return {};
    SmallVector<LayoutFieldAttr> nativeFields;
    if (!fields(*fieldRows, nativeFields, depth))
      return {};
    SmallVector<LayoutAlternativeAttr> alternatives;
    for (const auto &row : *alternativeRows) {
      auto *alternative = row.getAsObject();
      if (!alternative || alternative->size() != 2 || !remaining--)
        return {};
      auto name = string(*alternative, "name");
      auto *rows = alternative->getArray("fields");
      SmallVector<LayoutFieldAttr> payload;
      if (!name || !rows || !fields(*rows, payload, depth))
        return {};
      auto attr = LayoutAlternativeAttr::getChecked(
          builder.getUnknownLoc(), builder.getContext(), name,
          ArrayRef<LayoutFieldAttr>(payload));
      if (!attr)
        return {};
      alternatives.push_back(attr);
    }
    SmallVector<Type> leaves;
    for (const auto &row : *leafRows) {
      auto spelling = row.getAsString();
      if (!spelling || !remaining--)
        return {};
      bytes += spelling->size();
      if (bytes > 64 * 1024 * 1024)
        return {};
      auto bound = protocol::parseBoundType(*spelling, false);
      if (!bound) {
        llvm::consumeError(bound.takeError());
        return {};
      }
      auto type = protocol::decodeBoundType(builder.getContext(), *bound);
      if (!type)
        return {};
      leaves.push_back(type);
    }
    return LayoutAttr::getChecked(
        builder.getUnknownLoc(), builder.getContext(), kind, identity, display,
        *custody, *constructible, copy, drop,
        ArrayRef<LayoutFieldAttr>(nativeFields),
        ArrayRef<LayoutAlternativeAttr>(alternatives), ArrayRef<Type>(leaves));
  }
};
} // namespace
LayoutAttr importLayout(MLIRContext *context, const llvm::json::Value &value) {
  auto registered = context
                        ? AbstractAttribute::lookup(LayoutAttr::name, context)
                        : std::nullopt;
  if (!registered || registered->get().getTypeID() != LayoutAttr::getTypeID())
    return {};
  return LayoutImport(context).read(value);
}
} // namespace zkc::data
