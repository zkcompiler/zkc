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
// First-use postorder interning is the /0 byte contract. Track the reader's
// cumulative expanded table sizes as well: compact DAGs must not evade its
// amplification allowance. This constructs bytes, never unpacks them.
struct VariantTable {
  struct Expansion {
    size_t bytes, nodes, depth;
  };
  json::Array nodes;
  std::map<std::string, size_t> ids;
  std::vector<Expansion> expansions;
  size_t visits = 0, encodedBytes = 0, expandedBytes = 0, expandedNodes = 0;

  Expected<size_t> intern(const json::Value &value, unsigned depth = 0) {
    if (depth >= 64 || ++visits > 200000)
      return error("variant-type");
    json::Value node = nullptr;
    Expansion expansion{2, 1, 1};
    if (auto text = value.getAsString()) {
      if (text->size() > VariantSpellingBytes ||
          !all_of(*text, [](unsigned char c) { return c >= 32 && c <= 126; }))
        return error("variant-type");
      node = text->str();
      expansion.bytes = printJson(node).size();
    } else if (auto *array = value.getAsArray()) {
      json::Array refs;
      for (const auto &child : *array) {
        auto id = intern(child, depth + 1);
        if (!id)
          return id.takeError();
        const auto &nested = expansions[*id];
        expansion.bytes += nested.bytes + (refs.empty() ? 0 : 1);
        expansion.nodes += nested.nodes;
        expansion.depth = std::max(expansion.depth, nested.depth + 1);
        if (expansion.bytes > 8 * 1024 * 1024 || expansion.nodes > 200000 ||
            expansion.depth > 64)
          return error("variant-type");
        refs.push_back(std::to_string(*id));
      }
      node = std::move(refs);
    } else
      return error("variant-type");
    auto key = printJson(node);
    if (auto found = ids.find(key); found != ids.end())
      return found->second;
    encodedBytes += key.size() + 1;
    expandedBytes += expansion.bytes;
    expandedNodes += expansion.nodes;
    if (nodes.size() >= 16384 ||
        encodedBytes > (VariantSpellingBytes - 8) / 2 ||
        expandedBytes > 8 * 1024 * 1024 || expandedNodes > 200000)
      return error("variant-type");
    size_t id = nodes.size();
    ids.emplace(std::move(key), id);
    expansions.push_back(expansion);
    nodes.push_back(std::move(node));
    return id;
  }
  Expected<std::string> pack(const json::Value &tree) {
    auto root = intern(tree);
    if (!root)
      return root.takeError();
    auto bytes = printJson(json::Array{"zkc.variant/0", std::move(nodes)});
    size_t spellingBytes = 8 + 2 * bytes.size();
    if (spellingBytes > VariantSpellingBytes ||
        expandedBytes >
            std::min(size_t(8 * 1024 * 1024), size_t(512) * spellingBytes) ||
        expandedNodes > std::min(size_t(200000), size_t(512) * spellingBytes))
      return error("variant-type");
    return toHex(bytes, true);
  }
};

struct TypeExport {
  TypeParseBudget budget;

  Expected<json::Value> variantTree(data::VariantType variant, unsigned depth,
                                    bool account) {
    // Special syntax still has exactly one installed owner, even though it
    // is not a generic catalog application.
    if (!type_adapters::findAdapter("variant"))
      return error("binding-type");
    for (auto table : type_adapters::installedAdapters())
      for (const auto &adapter : table)
        if (adapter.arguments &&
            adapter.arguments(variant, adapter.constructor))
          return error("binding-type");
    if (depth >= 8 || variant.getAlternatives().size() > 32 ||
        (account && !budget.consume()))
      return error("variant-type");
    json::Array alternatives;
    for (auto arm : variant.getAlternatives()) {
      if (arm.getPayload().size() > 128)
        return error("variant-type");
      json::Array payload;
      for (Type child : arm.getPayload()) {
        if (auto nested = dyn_cast<data::VariantType>(child)) {
          auto tree = variantTree(nested, depth + 1, account);
          if (!tree)
            return tree.takeError();
          // Decoding an inline arm subsequently imports its own self-contained
          // descriptor. It must satisfy the table allowance on its own too.
          auto spelling = VariantTable{}.pack(*tree);
          if (!spelling)
            return spelling.takeError();
          payload.push_back(std::move(*tree));
        } else {
          auto bound = logical(child, depth + 1, account);
          if (!bound)
            return bound.takeError();
          payload.push_back(bound->spelling());
        }
      }
      alternatives.push_back(
          json::Array{arm.getLabel().getValue(), std::move(payload)});
    }
    return json::Value(
        json::Array{data::exportVariantIdentity(variant.getIdentity()),
                    std::move(alternatives)});
  }

  Expected<BoundType> logical(Type type, unsigned depth, bool account) {
    if (!type || depth > 8)
      return error("binding-type-limit");
    BoundType result;
    if (auto variant = dyn_cast<data::VariantType>(type)) {
      auto tree = variantTree(variant, depth, account);
      if (!tree)
        return tree.takeError();
      auto identity = VariantTable{}.pack(*tree);
      if (!identity)
        return identity.takeError();
      result = {"variant", std::move(*identity), {}};
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
    if (bytes > (result.kind == "variant" ? VariantSpellingBytes : 4096) ||
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
  auto checked = parseBoundType(t.spelling(), !t.representation.empty());
  if (!checked) {
    consumeError(checked.takeError());
    return {};
  }
  if (!(*checked == t))
    return {};
  const auto *adapter = type_adapters::findAdapter(t.kind);
  if (!adapter)
    return {};
  Type result = adapter->decode(ctx, t);
  if (!result)
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
  if (result->spelling().size() > PhysicalSpellingBytes)
    return error("binding-type-limit");
  return result;
}
} // namespace zkc::protocol
