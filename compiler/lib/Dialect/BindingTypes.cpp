#include "zkc/Dialect/BindingTypes.h"
#include "Data/IR/Structure.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Dialect/TypeAdapters/Support.h"
#include "zkc/Dialect/TypeFormation.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <map>

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
struct TypeExport {
  TypeParseBudget budget;

  Expected<BoundType> logical(Type type, unsigned depth, bool account) {
    if (!type || depth > 8)
      return error("binding-type-limit");
    BoundType result;
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      if (!type_adapters::findAdapter("variant") || depth >= 8 ||
          variant.getAlternatives().size() > VariantDescriptorAlternatives ||
          (account && !budget.consume()))
        return error("variant-type");
      for (auto table : type_adapters::installedAdapters())
        for (const auto &adapter : table)
          if (adapter.arguments &&
              adapter.arguments(variant, adapter.constructor))
            return error("binding-type");
      VariantDescriptor descriptor{
          data::exportVariantIdentity(variant.getIdentity()), {}};
      for (auto arm : variant.getAlternatives()) {
        if (arm.getPayload().size() > 128)
          return error("variant-type");
        VariantAlternative alternative{arm.getLabel().getValue().str(), {}};
        for (Type child : arm.getPayload()) {
          auto bound = logical(child, depth + 1, account);
          if (!bound)
            return bound.takeError();
          alternative.payload.push_back(std::move(*bound));
        }
        descriptor.alternatives.push_back(std::move(alternative));
      }
      result.kind = "variant";
      result.variant =
          std::make_shared<const VariantDescriptor>(std::move(descriptor));
      if (!encodeVariant(*result.variant))
        return error("variant-type");
    } else {
      // Boundary adapters also admit builtin bool/index in a context with no
      // zkc dialect loaded. Observe the same compiled owner table directly;
      // ambiguity and constructor ownership remain checked.
      auto app = type_adapters::observeCatalogType(type);
      if (!app || !type_adapters::findAdapter(app->constructor))
        return error("binding-type");
      if (account && !budget.consume())
        return error("binding-type-limit");
      result.kind = app->constructor.str();
      auto *declaration = typeDeclaration(app->constructor);
      if (!declaration ||
          app->arguments.size() != declaration->parameters.size())
        return error("binding-type-identity");
      bool atomic = declaration->parameters.size() == 1 &&
                    declaration->parameters.front().kind == StaticKind::Domain;
      if (atomic)
        result.identity =
            cast<StringAttr>(app->arguments.front()).getValue().str();
      else {
        if (!app->arguments.empty() && depth >= 8)
          return error("binding-type-limit");
        if (account &&
            !budget.charge(app->arguments.size() * sizeof(TypeArgument)))
          return error("binding-type-limit");
        for (Attribute value : app->arguments) {
          if (auto domain = dyn_cast<StringAttr>(value)) {
            if (account && !budget.consume())
              return error("binding-type-limit");
            result.arguments.push_back(
                TypeArgument::domainArgument(domain.getValue().str()));
          } else if (auto nested = dyn_cast<TypeAttr>(value)) {
            auto child = logical(nested.getValue(), depth + 1, account);
            if (!child)
              return child.takeError();
            result.arguments.push_back(
                TypeArgument::typeArgument(std::move(*child)));
          } else if (auto natural = dyn_cast<IntegerAttr>(value)) {
            if (account && !budget.consume())
              return error("binding-type-limit");
            result.arguments.push_back(TypeArgument::naturalArgument(
                natural.getValue().getZExtValue()));
          } else
            return error("binding-type-identity");
        }
      }
    }
    size_t bytes = result.spelling().size();
    if (!bytes ||
        bytes > (result.kind == "variant" ? VariantSpellingBytes : 4096) ||
        (account && !budget.charge(sizeof(BoundType) + bytes)))
      return error("binding-type-limit");
    return result;
  }

  Expected<BoundType> physical(runtime::RepresentedType type, unsigned depth) {
    auto result = logical(type.getLogical(), depth, depth == 0);
    if (!result)
      return result.takeError();
    // The input reader accounts for the logical tree once, then every layout
    // node, including omitted defaults. Charge children before expanding them.
    if (!budget.consume() ||
        !budget.charge(sizeof(BoundType) + result->spelling().size()) ||
        !budget.charge(type.getChildren().size() * sizeof(BoundType)))
      return error("binding-type-limit");
    result->representation = type.getRepresentation().str();
    auto kind = result->kind;
    if (kind == "variant" || kind == "sequence" || kind == "field_array" ||
        kind == "fixed_vector") {
      std::vector<BoundType> children;
      for (Type child : type.getChildren()) {
        auto bound = physical(cast<runtime::RepresentedType>(child), depth + 1);
        if (!bound)
          return bound.takeError();
        children.push_back(std::move(*bound));
      }
      result->physicalChildren =
          std::make_shared<const std::vector<BoundType>>(std::move(children));
    }
    auto spelling = result->spelling();
    if (!budget.charge(StringRef(spelling).split('@').second.size()))
      return error("binding-type-limit");
    return result;
  }
};
} // namespace

Type decodeBoundType(MLIRContext *ctx, const BoundType &t) {
  if (!ctx)
    return {};
  if (auto e = checkBoundType(t, !t.representation.empty())) {
    consumeError(std::move(e));
    return {};
  }
  const auto *adapter = type_adapters::findAdapter(t.kind);
  if (!adapter)
    return {};
  Type result = adapter->decode(ctx, t);
  if (!result)
    return {};
  // Builtin bool/index translation also works without any zkc dialect (and
  // therefore without its external catalog interface models) loaded.
  if (!result.isSignlessInteger(1) && !result.isUnsignedInteger(64) &&
      failed(verifyLogicalType([&] { return emitError(UnknownLoc::get(ctx)); },
                               result)))
    return {};
  if (t.representation.empty())
    return result;
  SmallVector<Type> children;
  if (t.physicalChildren)
    for (const auto &child : *t.physicalChildren) {
      auto decoded = decodeBoundType(ctx, child);
      if (!decoded)
        return {};
      children.push_back(decoded);
    }
  return type_adapters::loadedType<zkc::runtime::RepresentedType>(
      ctx, result, t.representation, children);
}

Expected<BoundType> encodeBoundType(Type type, bool physical) {
  if (!type)
    return error("binding-type");
  auto represented = dyn_cast<runtime::RepresentedType>(type);
  if (physical != bool(represented))
    return error(physical ? "binding-logical-type-at-physical-stage"
                          : "binding-physical-type-at-logical-stage");
  Type logical = logicalValueType(type);
  if (!logical)
    return error("binding-type");
  auto emit = [&] {
    auto diagnostic = emitError(UnknownLoc::get(type.getContext()));
    diagnostic.abandon();
    return diagnostic;
  };
  // Unchecked native builders can retain malformed children in release builds.
  // Bound actual storage before adapter observation constructs TypeAttr values.
  if (failed(data::detail::verifyStructure(emit, {}, {type})))
    return error(physical ? "binding-representation" : "binding-type-identity");
  auto application = type_adapters::observeCatalogType(logical);
  if (!isa<data::VariantType>(logical) && !application)
    return error("binding-type");
  // Formation examines actual storage, foreign contexts, every inactive arm,
  // argument kind and the full represented layout before any conversion.
  bool builtin = logical.isSignlessInteger(1) || logical.isUnsignedInteger(64);
  if (failed(builtin ? verifyLogicalTypeApplication(emit, logical.getContext(),
                                                    *application)
                     : verifyLogicalType(emit, logical)))
    return error("binding-type-identity");
  if (physical && failed(verifyValueType(emit, type)))
    return error("binding-representation");
  TypeExport conversion;
  if (!physical)
    return conversion.logical(logical, 0, true);
  auto result = conversion.physical(represented, 0);
  if (!result)
    return result.takeError();
  auto spelling = result->spelling();
  if (spelling.empty() || spelling.size() > PhysicalSpellingBytes)
    return error("binding-type-limit");
  return result;
}
} // namespace zkc::protocol
