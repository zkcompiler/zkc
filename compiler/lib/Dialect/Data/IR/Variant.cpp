#include "zkc/Dialect/Data/Variant.h"
#include "Structure.h"
#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"

using namespace mlir;
namespace zkc::data {
LogicalResult IdentityAttr::verify(function_ref<InFlightDiagnostic()> emit,
                                   ArrayAttr term) {
  SmallVector<std::pair<Attribute, unsigned>> pending{{term, 0}};
  unsigned remaining = 200000;
  size_t bytes = 0;
  while (!pending.empty()) {
    auto [raw, depth] = pending.pop_back_val();
    if (!remaining-- || depth >= 64)
      return emit() << "identity exceeds structural work limits";
    auto row = dyn_cast_or_null<ArrayAttr>(raw);
    if (!row || row.size() != 2)
      return emit() << "identity requires a tagged pair";
    auto tag = dyn_cast<StringAttr>(row[0]);
    if (!tag)
      return emit() << "identity requires an atom or tuple tag";
    if (tag.getValue() == "atom") {
      auto atom = dyn_cast<StringAttr>(row[1]);
      if (!atom || atom.getValue().empty() ||
          !llvm::json::isUTF8(atom.getValue()))
        return emit() << "identity atom must be nonempty";
      bytes += atom.getValue().size();
      if (bytes > 64 * 1024 * 1024)
        return emit() << "identity exceeds metadata limits";
    } else if (tag.getValue() == "tuple") {
      auto children = dyn_cast<ArrayAttr>(row[1]);
      if (!children)
        return emit() << "identity tuple requires ordered children";
      for (auto child : children)
        pending.emplace_back(child, depth + 1);
    } else
      return emit() << "unknown identity tag";
  }
  return success();
}
LogicalResult AlternativeAttr::verify(function_ref<InFlightDiagnostic()> emit,
                                      StringAttr label,
                                      ArrayRef<Type> payload) {
  if (!label || label.getValue().empty() || label.getValue().size() > 128 ||
      payload.size() > 512)
    return emit() << "invalid variant alternative";
  auto name = label.getValue();
  if (!(llvm::isAlpha(name.front()) || name.front() == '_') ||
      !llvm::all_of(name, [](char c) {
        return llvm::isAlnum(c) || c == '_' || c == '-' || c == '.';
      }))
    return emit() << "invalid variant alternative label";
  if (llvm::any_of(payload, [](Type type) { return !type; }))
    return emit() << "missing variant payload type";
  return success();
}
LogicalResult VariantType::verify(function_ref<InFlightDiagnostic()> emit,
                                  IdentityAttr identity,
                                  ArrayRef<AlternativeAttr> alternatives) {
  if (!identity || alternatives.empty() || alternatives.size() > 512)
    return emit() << "variant requires an identity and alternatives";
  llvm::SmallDenseSet<StringAttr, 8> names;
  for (auto arm : alternatives)
    if (!arm || !names.insert(arm.getLabel()).second)
      return emit() << "duplicate or missing variant alternative";
  // Count expanded children, not only distinct context-uniqued storage. This
  // verifies structure; the enclosing stage admits the logical payload profile.
  SmallVector<Attribute> attrs{identity};
  llvm::append_range(attrs, alternatives);
  return detail::verifyStructure(emit, attrs);
}
namespace {
ArrayAttr identityTerm(Builder &builder, const llvm::json::Value &value,
                       unsigned depth, unsigned &remaining) {
  if (depth >= 64 || !remaining--)
    return {};
  if (auto atom = value.getAsString()) {
    if (atom->empty())
      return {};
    return builder.getArrayAttr(
        {builder.getStringAttr("atom"), builder.getStringAttr(*atom)});
  }
  auto *array = value.getAsArray();
  if (!array)
    return {};
  SmallVector<Attribute> children;
  for (const auto &value : *array) {
    auto child = identityTerm(builder, value, depth + 1, remaining);
    if (!child)
      return {};
    children.push_back(child);
  }
  return builder.getArrayAttr(
      {builder.getStringAttr("tuple"), builder.getArrayAttr(children)});
}
llvm::json::Value identityValue(ArrayAttr term) {
  if (cast<StringAttr>(term[0]).getValue() == "atom")
    return cast<StringAttr>(term[1]).getValue().str();
  llvm::json::Array children;
  for (auto child : cast<ArrayAttr>(term[1]))
    children.push_back(identityValue(cast<ArrayAttr>(child)));
  return children;
}
} // namespace
IdentityAttr importVariantIdentity(MLIRContext *context,
                                   const llvm::json::Value &value) {
  Builder builder(context);
  unsigned remaining = 200000;
  auto term = identityTerm(builder, value, 0, remaining);
  return term ? IdentityAttr::getChecked(builder.getUnknownLoc(), context, term)
              : IdentityAttr{};
}
llvm::json::Value exportVariantIdentity(IdentityAttr identity) {
  return identityValue(identity.getTerm());
}
VariantType importVariantType(MLIRContext *context,
                              const protocol::VariantDescriptor &descriptor) {
  auto identity = importVariantIdentity(context, descriptor.nominal);
  if (!identity)
    return {};
  Builder builder(context);
  SmallVector<AlternativeAttr> alternatives;
  for (const auto &arm : descriptor.alternatives) {
    SmallVector<Type> payload;
    for (const auto &spelling : arm.payload) {
      auto bound = protocol::parseBoundType(spelling, false);
      if (!bound) {
        llvm::consumeError(bound.takeError());
        return {};
      }
      auto type = protocol::decodeBoundType(context, *bound);
      if (!type)
        return {};
      payload.push_back(type);
    }
    auto alternative = AlternativeAttr::getChecked(
        builder.getUnknownLoc(), context, builder.getStringAttr(arm.label),
        ArrayRef<Type>(payload));
    if (!alternative)
      return {};
    alternatives.push_back(alternative);
  }
  return VariantType::getChecked(builder.getUnknownLoc(), context, identity,
                                 ArrayRef<AlternativeAttr>(alternatives));
}
llvm::Expected<llvm::SmallVector<Type>>
variantPayloadTypes(Type carrier, llvm::StringRef alternative) {
  auto represented = dyn_cast_or_null<runtime::RepresentedType>(carrier);
  auto logical = represented ? represented.getLogical() : carrier;
  auto variant = dyn_cast_or_null<VariantType>(logical);
  if (!variant)
    return error("variant-type");
  size_t offset = 0, total = 0;
  for (auto arm : variant.getAlternatives())
    total += arm.getPayload().size();
  if (represented) {
    if (represented.getChildren().size() != total)
      return error("binding-representation");
    size_t child = 0;
    for (auto arm : variant.getAlternatives())
      for (auto expected : arm.getPayload()) {
        Type actual = represented.getChildren()[child++];
        if (auto wrapper = dyn_cast<runtime::RepresentedType>(actual))
          actual = wrapper.getLogical();
        if (actual != expected)
          return error("binding-representation");
      }
  }
  for (auto arm : variant.getAlternatives()) {
    if (arm.getLabel().getValue() == alternative) {
      auto types =
          represented
              ? represented.getChildren().slice(offset, arm.getPayload().size())
              : arm.getPayload();
      return llvm::SmallVector<Type>(types);
    }
    offset += arm.getPayload().size();
  }
  return error("variant-alternative");
}
} // namespace zkc::data
