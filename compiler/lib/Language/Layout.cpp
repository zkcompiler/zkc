#include "zkc/Language/Layout.h"
#include "Semantics.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/FramedHash.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include <limits>
using namespace llvm;
namespace zkc::language {
namespace {
Expected<unsigned> placementParticipants(const ValuePlacement &placement) {
  unsigned count = 0;
  auto add = [&](unsigned role) -> Error {
    if (role == std::numeric_limits<unsigned>::max())
      return error("source.roles", "participant index exceeds native bounds");
    count = std::max(count, role + 1);
    return Error::success();
  };
  ArrayRef<unsigned> roles;
  if (const auto *data = std::get_if<DataPlacement>(&placement.value))
    roles = data->roles;
  else if (const auto *oracle =
               std::get_if<OraclePlacement>(&placement.value)) {
    if (auto e = add(oracle->holder))
      return std::move(e);
    roles = oracle->receivers;
  } else
    roles = std::get<ProductPlacement>(placement.value).arguments;
  for (auto role : roles)
    if (auto e = add(role))
      return std::move(e);
  return count;
}
} // namespace
Expected<std::string> LayoutIdentities::get(const Layout &layout) {
  if (auto found = cache.find(&layout); found != cache.end())
    return found->second;
  if (depth > Limits{}.typeDepth)
    return error("source.limit", "schema identity depth limit exceeded");
  ++depth;
  auto restoreDepth = llvm::scope_exit([&] { --depth; });
  auto complexity = typeComplexity(layout.type, remaining, Limits{}.typeDepth);
  if (!complexity)
    return complexity.takeError();
  if (*complexity > remaining)
    return error("source.limit", "schema identity type budget exceeded");
  remaining -= *complexity;
  // The revision-bound identity, never the lookup key, enters the schema.
  if (layout.identity.digest.empty())
    return error("source.layout", "schema has no nominal identity");
  if (layout.identity.key.size() > remaining)
    return error("source.limit", "schema type identity limit exceeded");
  remaining -= layout.identity.key.size();
  FramedHash hash(remaining);
  hash.frame("zkc.language.schema/0");
  hash.frame(typeKindName(layout.type.kind));
  hash.frame(layout.identity.digest);
  if (!layout.generatedIdentity.empty())
    hash.frame(layout.generatedIdentity);
  hash.frame(std::to_string(layout.custodyCount));
  hash.frame(layout.sealed ? "1" : "0");
  hash.frame(layout.constructible ? "1" : "0");
  for (bool allowed : {layout.permissions.copy, layout.permissions.drop})
    hash.frame(allowed ? "1" : "0");
  hash.frame(std::to_string(layout.roleParameters.size()));
  for (const auto &role : layout.roleParameters)
    hash.frame(role);
  if (layout.element) {
    hash.frame("element");
    auto element = get(*layout.element);
    if (!element)
      return element.takeError();
    hash.frame(*element);
  } else
    hash.frame("");
  if (layout.oracleData) {
    hash.frame("data_schema");
    auto data = get(*layout.oracleData);
    if (!data)
      return data.takeError();
    hash.frame(*data);
  } else
    hash.frame("");
  hash.frame(std::to_string(layout.leaves.size()));
  for (const auto &leaf : layout.leaves) {
    if (!remaining)
      return error("source.limit", "schema identity leaf budget exceeded");
    --remaining;
    if (const auto *oracle = leaf.oracle()) {
      hash.frame("oracle");
      hash.frame(oracle->kind.identity);
      for (const auto &argument : oracle->kind.arguments)
        hash.frame(argument.spelling());
      hash.frame(oracle->maximum ? std::to_string(*oracle->maximum) : "");
      continue;
    }
    if (!leaf.data())
      return error("source.formal", "relation schema contains a formal leaf");
    auto encoded = leaf.data()->spelling();
    if (encoded.empty())
      return error("source.limit",
                   "published schema leaf exceeds encoding limits");
    hash.frame(encoded);
  }
  // A product formula node frames its schema's published identity, the same
  // value an external placement carries, so readers hash what they read.
  std::function<Error(const Layout &, const ValuePlacement &, unsigned)>
      formula = [&](const Layout &schema, const ValuePlacement &p,
                    unsigned level) -> Error {
    if (!remaining || level > Limits{}.typeDepth)
      return error("source.limit", "schema formula identity budget exceeded");
    --remaining;
    if (const auto *data = std::get_if<DataPlacement>(&p.value)) {
      hash.frame("data");
      hash.frame(std::to_string(data->roles.size()));
      for (unsigned role : data->roles)
        hash.frame(std::to_string(role));
    } else if (const auto *oracle = std::get_if<OraclePlacement>(&p.value)) {
      hash.frame("oracle");
      hash.frame(std::to_string(oracle->holder));
      hash.frame(std::to_string(oracle->receivers.size()));
      for (unsigned role : oracle->receivers)
        hash.frame(std::to_string(role));
    } else {
      const auto &product = std::get<ProductPlacement>(p.value);
      hash.frame("product");
      if (product.instance.size() > remaining)
        return error("source.limit", "schema formula instance budget exceeded");
      remaining -= product.instance.size();
      const bool array = schema.type.kind == Type::Kind::Array;
      if (product.instance != typeIdentity(schema.type) ||
          product.fields.size() != (array ? 1 : schema.fields.size()))
        return error("source.layout", "schema formula instance differs");
      hash.frame(schema.identity.digest);
      hash.frame(std::to_string(product.arguments.size()));
      for (unsigned role : product.arguments)
        hash.frame(std::to_string(role));
      hash.frame(std::to_string(product.fields.size()));
      for (unsigned i = 0; i < product.fields.size(); ++i) {
        const auto *child =
            array ? schema.element.get() : schema.fields[i].layout.get();
        if (!child)
          return error("source.layout", "schema formula lacks its child");
        if (auto e = formula(*child, product.fields[i], level + 1))
          return e;
      }
    }
    return Error::success();
  };
  auto fields = [&](ArrayRef<LayoutField> fields) -> Error {
    hash.frame(std::to_string(fields.size()));
    for (const auto &field : fields) {
      if (!remaining)
        return error("source.limit", "schema field identity budget exceeded");
      --remaining;
      hash.frame(field.name);
      hash.frame(std::to_string(field.offset));
      hash.frame(field.isPublic ? "1" : "0");
      hash.frame(field.placement ? "placement" : "");
      if (field.placement)
        if (auto e = formula(*field.layout, *field.placement, 0))
          return e;
      if (field.maximumRows) {
        hash.frame("maximum_rows");
        hash.frame(std::to_string(*field.maximumRows));
      }
      auto child = get(*field.layout);
      if (!child)
        return child.takeError();
      hash.frame(*child);
    }
    return Error::success();
  };
  if (auto error = fields(layout.fields))
    return std::move(error);
  hash.frame(std::to_string(layout.alternatives.size()));
  for (const auto &alternative : layout.alternatives) {
    hash.frame(alternative.name);
    if (auto error = fields(alternative.fields))
      return std::move(error);
  }
  auto digest = hash.finish();
  if (!digest)
    return digest.takeError();
  cache.emplace(&layout, *digest);
  return digest;
}
struct Layouts::State {
  Limits workLimits;
  detail::Work work;
  const std::vector<Declaration> &declarations;
  ArrayRef<Asset> assets;
  detail::AuthorityView authorities;
  std::optional<detail::Semantics> types;
  State(const std::vector<Declaration> &declarations, const Limits &limits,
        detail::AuthorityView authorities, ArrayRef<Asset> assets = {})
      : workLimits(limits), work{workLimits}, declarations(declarations),
        assets(assets), authorities(authorities) {}
};
// An observer of a checked project or closed Entry lays out with the
// project's final authorities, computed once after all checking.
Layouts::Layouts(const CheckedProject &project, const Limits &limits)
    : definitions(project.declarations()), limits(limits),
      state(std::make_unique<State>(
          project.storage->declarations, this->limits,
          detail::AuthorityView{project.storage.get()}, project.assets())) {}
Layouts::Layouts(const ClosedEntry &entry, const Limits &limits)
    : definitions(entry.declarations()), limits(limits),
      state(std::make_unique<State>(
          entry.storage->declarations, this->limits,
          detail::AuthorityView{entry.project().storage.get()},
          entry.assets())) {}
Layouts::Layouts(const ClosedEntry &entry, const Limits &limits,
                 uint64_t &remaining)
    : Layouts(entry, limits) {
  state->workLimits.work = std::min(limits.work, remaining);
  state->work.allowance = &remaining;
}
Layouts::~Layouts() = default;
Layouts::Layouts(const std::vector<Declaration> &declarations,
                 const Limits &limits, detail::AuthorityView authorities)
    : definitions(declarations), limits(limits),
      state(std::make_unique<State>(declarations, this->limits, authorities)) {}
Expected<ValuePlacement> Layouts::placement(const Type &type,
                                            const ValuePlacement &seed,
                                            unsigned participants) {
  if (auto e = initializeTypes())
    return e;
  auto result = state->types->placement(type, seed, participants, {});
  if (!result)
    return state->types->takeError();
  return std::move(*result);
}
Expected<protocol::BoundType>
detail::Semantics::nativeLayout(const Type &type) {
  if (auto e = work.charge(0))
    return e;
  if (isNativeData(type) &&
      !(type.kind == Type::Kind::Builtin && type.domain == "sequence"))
    return builtinLayout(type);
  auto limits = work.limits;
  limits.work = work.remaining();
  Layouts layouts(declarations, limits, authorities);
  auto result = layouts.packed(type);
  auto charged = work.charge(layouts.state->work.used);
  if (charged) {
    if (!result)
      consumeError(result.takeError());
    return std::move(charged);
  }
  if (!result) {
    return result.takeError();
  }
  return std::move(result->carrier);
}
Expected<ProtocolPortLayout>
detail::Semantics::nativePortLayout(const Port &port) {
  if (auto e = work.charge(0))
    return e;
  auto limits = work.limits;
  limits.work = work.remaining();
  Layouts layouts(declarations, limits, authorities);
  auto result = layouts.protocolPort(port);
  auto charged = work.charge(layouts.state->work.used);
  if (charged) {
    if (!result)
      consumeError(result.takeError());
    return std::move(charged);
  }
  if (!result) {
    return result.takeError();
  }
  return result;
}
Expected<OracleKindLayout> Layouts::oracleKind(const Type &kind) {
  if (kind.kind != Type::Kind::OracleKind || kind.symbolic)
    return error("source.oracle-kind", "oracle layout requires a closed kind");
  auto complexity = typeComplexity(kind, limits.typeNodes, limits.typeDepth);
  if (!complexity)
    return complexity.takeError();
  if (auto e = charge(*complexity))
    return std::move(e);
  auto formed = builtinType(oracleConstructor(kind), kind.arguments);
  if (!formed)
    return formed.takeError();
  auto row = packed(kind.arguments.front());
  if (!row)
    return row.takeError();
  std::vector<protocol::TypeArgument> arguments{
      protocol::TypeArgument::typeArgument(row->carrier)};
  if (kind.arguments.size() == 2) {
    const auto &rows = kind.arguments[1].dimension;
    if (!rows.isClosed())
      return error("source.generic", "oracle cardinality remains symbolic");
    arguments.push_back(
        protocol::TypeArgument::naturalArgument(rows.closedValue()));
  }
  auto signature = protocol::oracleKindSignature(kind.domain, arguments);
  if (!signature)
    return error("source.oracle-kind", toString(signature.takeError()));
  return OracleKindLayout{kind.domain, std::move(arguments),
                          std::move(*signature)};
}
Expected<PackedLayout> Layouts::packed(const Type &type) {
  auto flat = get(type);
  if (!flat)
    return flat.takeError();
  return pack(*flat);
}
Expected<PackedLayout> Layouts::pack(std::shared_ptr<const Layout> flat) {
  if (isLogicalValue(flat->type) || !isSequenceElement(flat->type) ||
      flat->formal || flat->custody || !flat->permissions.copy ||
      !flat->permissions.drop)
    return error("source.sequence",
                 "sequence element requires executable Copy and Drop data");
  using K = Type::Kind;
  bool product = flat->type.kind == K::Record || flat->type.kind == K::Tuple ||
                 flat->type.kind == K::Array || flat->type.kind == K::Unit ||
                 flat->type.kind == K::Associated;
  if (!product) {
    if (flat->leaves.size() != 1 || !flat->leaves.front().data())
      return error("source.layout", "native element requires one data leaf");
    auto carrier = *flat->leaves.front().data();
    return PackedLayout{std::move(flat), std::move(carrier), false, {}};
  }
  const auto &identity = flat->identity.key;
  if (identity.size() > protocol::VariantSpellingBytes / 2)
    return error("source.limit", "packed nominal encoding exceeds byte limit");
  if (auto e = charge(2 * identity.size() + flat->leaves.size()))
    return std::move(e);
  protocol::VariantAlternative alternative{nativeAlternativeName(0), {}};
  for (const auto &leaf : flat->leaves) {
    if (!leaf.data())
      return error("source.sequence",
                   "sequence element contains a formal leaf");
    if (auto e = charge(leaf.cost()))
      return std::move(e);
    alternative.payload.push_back(*leaf.data());
  }
  protocol::VariantDescriptor descriptor{
      protocol::VariantIdentity::Tuple{"zkc.language.pack",
                                       encodeNominalIdentity(identity)},
      {alternative}};
  auto carrier = protocol::variantType(std::move(descriptor));
  if (!carrier)
    return carrier.takeError();
  return PackedLayout{std::move(flat), std::move(*carrier), true,
                      alternative.label};
}
Expected<std::vector<std::string>>
Layouts::kernelArguments(StringRef contract, ArrayRef<Type> arguments) {
  return language::kernelArguments(
      contract, arguments,
      [&](const Type &type) -> Expected<protocol::BoundType> {
        auto layout = packed(type);
        if (!layout)
          return layout.takeError();
        return std::move(layout->carrier);
      });
}
Error Layouts::initializeTypes() {
  if (state->types)
    return Error::success();
  if (auto e = checkLimits(limits))
    return e;
  if (auto e = detail::chargeSemanticIndex(state->declarations, state->work))
    return e;
  state->types.emplace(state->declarations, state->assets, state->work);
  state->types->authorities = state->authorities;
  return Error::success();
}
Error Layouts::charge(uint64_t n) { return state->work.charge(n); }
Expected<LayoutSlice> ProtocolPortLayout::select(ArrayRef<unsigned> path,
                                                 bool anchor,
                                                 bool specification) const {
  if (!body)
    return error("source.layout", "protocol layout has no source body");
  auto selected = body;
  unsigned bodyOffset = 0;
  for (auto index : path) {
    if ((selected->custody && !specification) ||
        selected->type.kind == Type::Kind::Associated ||
        selected->type.kind == Type::Kind::Variant ||
        index >= selected->fields.size())
      return error("source.layout", "selector is not a source product path");
    bodyOffset += selected->fields[index].offset;
    selected = selected->fields[index].layout;
  }
  if (bodyOffset >= nativeOffsets.size())
    return error("source.layout", "selector body offset is out of bounds");
  unsigned offset = nativeOffsets[bodyOffset];
  if (anchor) {
    if (selected->type.kind != Type::Kind::Oracle || !selected->oracleData ||
        selected->leaves.size() != 1)
      return error("source.layout", "anchor requires a singleton oracle field");
    return LayoutSlice{offset + 1, selected->oracleData};
  }
  if (isLogicalValue(selected->type))
    return error("source.layout", "logical selection requires an anchor");
  return LayoutSlice{offset, std::move(selected)};
}
std::vector<unsigned> ProtocolPortLeaf::roles() const {
  if (!placement)
    return {};
  if (const auto *data = std::get_if<DataPlacement>(&placement->value))
    return data->roles;
  const auto &oracle = std::get<OraclePlacement>(placement->value);
  auto result = oracle.receivers;
  result.push_back(oracle.holder);
  llvm::sort(result);
  return result;
}
Expected<ProtocolPortLayout>
observeProtocolPort(std::shared_ptr<const Layout> body,
                    const std::optional<ValuePlacement> &placement,
                    uint64_t &remaining, const Limits &limits,
                    std::optional<uint64_t> maximumRows, bool checkBounds) {
  if (!body)
    return error("source.layout", "protocol observation requires a layout");
  auto charge = [&](uint64_t amount) -> Error {
    if (amount > remaining)
      return error("source.limit", "protocol observation work limit exceeded");
    remaining -= amount;
    return Error::success();
  };
  unsigned participants = 0;
  if (placement) {
    auto roster = placementParticipants(*placement);
    if (!roster)
      return roster.takeError();
    participants = *roster;
    if (auto e = validatePlacement(*placement, participants, remaining,
                                   limits.typeDepth))
      return std::move(e);
  }
  ProtocolPortLayout result;
  result.body = std::move(body);
  result.placement = placement;
  std::vector<unsigned> path;
  auto append = [&](const LayoutLeaf &leaf, unsigned offset, unsigned local,
                    const std::optional<ValuePlacement> &placed, bool custody,
                    bool materialized, std::shared_ptr<const Layout> data = {},
                    std::optional<uint64_t> maximum = {}) -> Error {
    if (materialized &&
        result.size() + (leaf.oracle() ? 2 : 1) > limits.aggregateLeaves)
      return error("source.limit",
                   "expanded protocol layout exceeds leaf limit");
    if (leaf.cost() == UINT64_MAX)
      return error("source.limit", "invalid leaf work estimate");
    if (auto e = charge(leaf.cost()))
      return e;
    if (auto e = charge(path.size() + 1))
      return e;
    if (!materialized)
      return Error::success();
    auto native = result.size();
    result.leaves.push_back({leaf, offset, native, path, std::move(data),
                             maximum, placed, custody});
    result.nativeOffsets.push_back(native + (leaf.oracle() ? 2 : 1));
    auto component = [&](unsigned role, ProtocolComponentFacet facet,
                         unsigned index) -> Error {
      if (auto e = charge(path.size() + 1))
        return e;
      result.components.push_back({path, local, role, facet, index});
      return Error::success();
    };
    if (placed) {
      if (const auto *ordinary = std::get_if<DataPlacement>(&placed->value)) {
        for (auto role : ordinary->roles)
          if (auto e = component(role,
                                 custody ? ProtocolComponentFacet::Custody
                                         : ProtocolComponentFacet::Data,
                                 native))
            return e;
      } else if (const auto *oracle =
                     std::get_if<OraclePlacement>(&placed->value)) {
        if (!leaf.oracle())
          return error("source.placement",
                       "ordinary leaf has oracle placement");
        // Component order is participant order within this logical leaf.
        // Its physical holder data still precedes the shared anchor slot.
        bool holderEmitted = false;
        for (auto role : oracle->receivers) {
          if (!holderEmitted && oracle->holder < role) {
            if (auto e = component(oracle->holder,
                                   ProtocolComponentFacet::OracleData, native))
              return e;
            holderEmitted = true;
          }
          if (auto e = component(role, ProtocolComponentFacet::OracleAnchor,
                                 native + 1))
            return e;
        }
        if (!holderEmitted)
          if (auto e = component(oracle->holder,
                                 ProtocolComponentFacet::OracleData, native))
            return e;
      } else
        return error("source.placement", "leaf has aggregate placement");
    } else if (leaf.oracle())
      return error("source.placement", "oracle leaf lacks its exact family");
    return Error::success();
  };
  // Substitution preserves nominal telescope order. Structural products instead
  // carry a canonical union, so normalize only the expected formula against its
  // schema. Never normalize the candidate placement we are validating.
  std::function<Error(const Layout &, ValuePlacement &, unsigned)>
      structuralScopes = [&](const Layout &schema, ValuePlacement &value,
                             unsigned depth) -> Error {
    if (depth > limits.typeDepth)
      return error("source.limit", "placement formula depth exceeded");
    if (auto e = charge(1))
      return e;
    auto *product = std::get_if<ProductPlacement>(&value.value);
    if (!product)
      return Error::success();
    const bool array = schema.type.kind == Type::Kind::Array;
    if (product->fields.size() != (array ? 1 : schema.fields.size()))
      return error("source.placement", "field formula schema arity differs");
    std::vector<unsigned> roles;
    for (unsigned i = 0; i < product->fields.size(); ++i) {
      auto child = array ? schema.element : schema.fields[i].layout;
      if (!child)
        return error("source.layout", "field formula lacks its child schema");
      if (auto e = structuralScopes(*child, product->fields[i], depth + 1))
        return e;
      auto members = placementRoles(product->fields[i]);
      if (auto e = charge(members.size() + 1))
        return e;
      llvm::append_range(roles, members);
    }
    if (array || schema.type.kind == Type::Kind::Tuple) {
      llvm::sort(roles);
      roles.erase(std::unique(roles.begin(), roles.end()), roles.end());
      product->arguments = std::move(roles);
    }
    return Error::success();
  };
  std::function<Error(const Layout &, unsigned,
                      const std::optional<ValuePlacement> &,
                      std::optional<uint64_t>, unsigned, bool)>
      visit = [&](const Layout &value, unsigned base,
                  const std::optional<ValuePlacement> &placed,
                  std::optional<uint64_t> maximum, unsigned depth,
                  bool materialized) -> Error {
    if (depth > limits.typeDepth)
      return error("source.limit", "protocol layout depth exceeded");
    if (auto e = charge(1 + path.size()))
      return e;
    const auto *product =
        placed ? std::get_if<ProductPlacement>(&placed->value) : nullptr;
    const bool structural = value.type.kind == Type::Kind::Tuple ||
                            value.type.kind == Type::Kind::Array;
    const bool requiresProduct = value.type.kind == Type::Kind::LogicalRecord ||
                                 (structural && isLogicalValue(value.type));
    if ((requiresProduct && !product) ||
        (product && !requiresProduct && !structural))
      return error("source.placement", "logical product placement differs");
    if (maximum && !isOracleHandle(value.type))
      return error("source.layout", "row maximum requires a direct oracle");
    if (product &&
        ((!value.roleParameters.empty() &&
          product->arguments.size() != value.roleParameters.size()) ||
         product->instance != typeIdentity(value.type) ||
         product->fields.size() !=
             (value.type.kind == Type::Kind::Array ? 1 : value.fields.size())))
      return error("source.placement", "logical product schema differs");
    if (product && structural) {
      std::vector<unsigned> roles;
      for (const auto &field : product->fields) {
        auto members = std::visit(
            [](const auto &placement) -> std::vector<unsigned> {
              using P = std::decay_t<decltype(placement)>;
              if constexpr (std::is_same_v<P, DataPlacement>)
                return placement.roles;
              else if constexpr (std::is_same_v<P, OraclePlacement>) {
                auto result = placement.receivers;
                result.push_back(placement.holder);
                return result;
              } else
                return placement.arguments;
            },
            field.value);
        if (auto e = charge(members.size() + 1))
          return e;
        llvm::append_range(roles, members);
      }
      llvm::sort(roles);
      roles.erase(std::unique(roles.begin(), roles.end()), roles.end());
      if (roles != product->arguments)
        return error("source.placement", "structural product scope differs");
    }
    if (isOracleHandle(value.type)) {
      if (!placed || !std::holds_alternative<OraclePlacement>(placed->value) ||
          value.leaves.size() != 1 || !value.leaves[0].oracle() ||
          !value.oracleData || value.oracleData->leaves.size() != 1 ||
          !value.oracleData->leaves[0].data() ||
          (checkBounds && value.leaves[0]
                                  .oracle()
                                  ->kind.signature.staticShape("rows")
                                  .has_value() == maximum.has_value()))
        return error("source.layout",
                     "logical field data or row bound differs");
      return append(value.leaves[0], base, 0, placed, false, materialized,
                    value.oracleData, maximum);
    }
    if (placed && std::holds_alternative<OraclePlacement>(placed->value))
      return error("source.placement",
                   "non-oracle schema has oracle placement");
    if (value.custody != (value.custodyCount != 0) ||
        value.custodyCount > value.leaves.size() ||
        (value.custody && product &&
         value.custodyCount != product->arguments.size()))
      return error("source.layout", "custody prefix arity differs");
    if (value.custody && placed && !product &&
        std::get<DataPlacement>(placed->value).roles.size() != 1)
      return error("source.placement", "custody fragment requires one owner");
    for (unsigned i = 0; i < value.custodyCount; ++i) {
      auto fragment = product ? std::optional<ValuePlacement>(
                                    DataPlacement{{product->arguments[i]}})
                              : placed;
      if (auto e = append(value.leaves[i], base + i, i, fragment, true,
                          materialized))
        return e;
    }
    // A zero array still retains a typed element-placement template. Validate
    // it without creating storage or granting an otherwise unavailable field.
    if (value.type.kind == Type::Kind::Array && value.fields.empty()) {
      if (!value.element)
        return error("source.layout", "array lacks its element schema");
      auto elementPlacement =
          product ? std::optional(product->fields.front()) : placed;
      path.push_back(0);
      auto e = visit(*value.element, 0, elementPlacement, {}, depth + 1, false);
      path.pop_back();
      if (e)
        return e;
    }
    if (!value.fields.empty()) {
      unsigned next = value.custodyCount;
      for (unsigned i = 0; i < value.fields.size(); ++i) {
        const auto &field = value.fields[i];
        if (!field.layout || field.offset != next)
          return error("source.layout", "product field offset differs");
        if (product && field.placement) {
          auto expected =
              substitutePlacement(*field.placement, product->arguments,
                                  participants, remaining, limits.typeDepth);
          if (!expected)
            return expected.takeError();
          if (auto e = structuralScopes(*field.layout, *expected, depth + 1))
            return e;
          if (*expected !=
              product->fields[value.type.kind == Type::Kind::Array ? 0 : i])
            return error("source.placement", "field role formula differs");
        }
        path.push_back(i);
        auto e = visit(
            *field.layout, base + field.offset,
            product
                ? std::optional(
                      product->fields[value.type.kind == Type::Kind::Array ? 0
                                                                           : i])
                : placed,
            field.maximumRows, depth + 1, materialized);
        path.pop_back();
        if (e)
          return e;
        next += field.layout->leaves.size();
      }
      if (next != value.leaves.size())
        return error("source.layout", "product field coverage differs");
    } else {
      for (unsigned i = value.custodyCount; i < value.leaves.size(); ++i) {
        if (value.leaves[i].oracle())
          return error("source.layout", "oracle lacks a direct source field");
        if (auto e = append(value.leaves[i], base + i, i, placed, false,
                            materialized))
          return e;
      }
    }
    return Error::success();
  };
  if (auto e = visit(*result.body, 0, placement, maximumRows, 1, true))
    return std::move(e);
  if (result.leaves.size() != result.body->leaves.size())
    return error("source.layout", "protocol body leaf coverage differs");
  for (unsigned i = 0; i < result.leaves.size(); ++i)
    if (result.leaves[i].bodyOffset != i)
      return error("source.layout", "protocol body leaf order differs");
  return result;
}
Expected<ProtocolPortLayout> Layouts::protocolPort(const Port &port) {
  return protocolPort(port, true);
}
Expected<ProtocolPortLayout> Layouts::protocolValue(const Value &value) {
  Port port{"", value.type, value.components, value.span, {}, value.placement};
  if (value.oracleHolder)
    port.oracle = OraclePort{*value.oracleHolder, {}};
  return protocolPort(port, false);
}
Expected<ProtocolPortLayout> Layouts::protocolPort(const Port &port,
                                                   bool checkBounds) {
  auto body = get(port.type);
  if (!body)
    return body.takeError();
  std::optional<ValuePlacement> placed = port.placement;
  if (port.oracle && port.placement) {
    const auto *oracle = std::get_if<OraclePlacement>(&port.placement->value);
    if (!oracle || oracle->holder != port.oracle->holder)
      return error("source.oracle-port", "direct oracle metadata differs");
  }
  // Temporary source migration seam: only legacy, telescope-free records may
  // derive their field formulas from the historical explicit oriented port.
  if (!placed && port.oracle) {
    std::function<ValuePlacement(const Layout &)> legacy =
        [&](const Layout &l) {
          if (isOracleHandle(l.type)) {
            auto receivers = port.roles;
            llvm::erase(receivers, port.oracle->holder);
            return ValuePlacement(
                OraclePlacement{port.oracle->holder, receivers});
          }
          if (l.type.kind == Type::Kind::LogicalRecord) {
            const auto *decl = state->types->typeDeclaration(l.type);
            if (!decl || !decl->roles.empty())
              return ValuePlacement(DataPlacement{});
            ProductPlacement product{typeIdentity(l.type), port.roles, {}};
            for (const auto &field : l.fields)
              product.fields.push_back(legacy(*field.layout));
            return ValuePlacement(std::move(product));
          }
          return ValuePlacement(DataPlacement{port.roles});
        };
    placed = legacy(**body);
  } else if (!placed && !port.roles.empty())
    placed = DataPlacement{port.roles};
  if (placed) {
    auto participants = placementParticipants(*placed);
    if (!participants)
      return participants.takeError();
    if (port.placement) {
      auto rebuilt = placement(port.type, *placed, *participants);
      if (!rebuilt)
        return rebuilt.takeError();
      if (*rebuilt != *placed)
        return error("source.placement",
                     "port differs from its checked schema");
    }
  }
  std::optional<uint64_t> maximum;
  if (port.oracle && port.oracle->maximumRows) {
    if (port.oracle->maximumRows->kind != Type::Kind::Natural ||
        !port.oracle->maximumRows->dimension.isClosed())
      return error("source.layout", "port row maximum is not a closed natural");
    maximum = port.oracle->maximumRows->dimension.closedValue();
  }
  const auto available = state->work.remaining();
  auto remaining = available;
  auto result = observeProtocolPort(*body, placed, remaining, limits, maximum,
                                    checkBounds);
  auto charged = charge(available - remaining);
  if (!result) {
    consumeError(std::move(charged));
    return result.takeError();
  }
  if (charged)
    return std::move(charged);
  return result;
}
Expected<LayoutSlice> Layouts::select(const Declaration &decl,
                                      const SpecificationSelector &selector) {
  auto ports = selector.output ? ArrayRef(decl.outputs) : ArrayRef(decl.inputs);
  if (selector.port >= ports.size() || selector.path.size() > limits.typeDepth)
    return error("source.layout", "selector port is out of bounds");
  auto port = protocolPort(ports[selector.port]);
  if (!port)
    return port.takeError();
  // Source checking has independently authorized specification field reads.
  // Executable input/setup selection keeps the ordinary custody barrier.
  auto slice = port->select(selector.path, selector.anchor, true);
  if (!slice)
    return slice.takeError();
  uint64_t offset = slice->offset;
  for (unsigned i = 0; i < selector.port; ++i) {
    auto before = protocolPort(ports[i]);
    if (!before)
      return before.takeError();
    offset += before->size();
  }
  if (offset > std::numeric_limits<unsigned>::max())
    return error("source.limit", "selector offset exceeds native bounds");
  slice->offset = static_cast<unsigned>(offset);
  return slice;
}
Expected<LayoutSlice> Layouts::selectInput(const Declaration &decl,
                                           const InputSelector &selector) {
  return select(decl.inputs, selector.port, selector.path);
}
Expected<LayoutSlice> Layouts::select(ArrayRef<Port> ports, unsigned port,
                                      ArrayRef<unsigned> path) {
  if (port >= ports.size() || path.size() > limits.typeDepth)
    return error("source.layout", "logical selector is out of bounds");
  uint64_t offset = 0;
  for (unsigned i = 0; i < port; ++i) {
    auto before = protocolPort(ports[i]);
    if (!before)
      return before.takeError();
    offset += before->size();
  }
  auto observed = protocolPort(ports[port]);
  if (!observed)
    return observed.takeError();
  auto slice = observed->select(path);
  if (!slice)
    return slice.takeError();
  offset += slice->offset;
  if (offset > std::numeric_limits<unsigned>::max())
    return error("source.limit",
                 "logical selector offset exceeds native bounds");
  return LayoutSlice{static_cast<unsigned>(offset), slice->layout};
}
Expected<Type> Layouts::substitute(const Type &type,
                                   const std::map<std::string, Type> &bindings,
                                   unsigned depth) {
  auto result = state->types->substitute(type, bindings, {}, depth);
  if (!result)
    return state->types->takeError();
  if (state->types->symbolic(*result))
    return error("source.generic", "unresolved logical layout");
  return std::move(*result);
}
Expected<std::shared_ptr<const Layout>> Layouts::get(const Type &type) {
  if (auto e = checkLimits(limits))
    return e;
  if (auto e = initializeTypes())
    return e;
  return build(type, 1);
}
Expected<std::shared_ptr<const Layout>> Layouts::build(const Type &type,
                                                       unsigned depth) {
  if (depth > limits.typeDepth)
    return error("source.limit", "logical layout depth exceeded");
  if (auto e = charge(1))
    return e;
  auto cost = typeComplexity(type, limits.typeNodes, limits.typeDepth);
  if (!cost)
    return cost.takeError();
  if (auto e = charge(*cost))
    return std::move(e);
  auto key = typeIdentity(type);
  if (auto e = charge(key.size()))
    return e;
  auto known = cache.find(key);
  if (known != cache.end())
    return known->second;
  if (type.symbolic || !type.dimension.isClosed())
    return error("source.generic", "layout requires a closed type");
  using K = Type::Kind;
  if (type.kind != K::Array && !type.dimension.terms().empty())
    return error("source.layout", "runtime type has an unexpected dimension");
  if ((type.kind == K::Boolean || type.kind == K::Index ||
       type.kind == K::Unit || type.kind == K::Field ||
       type.kind == K::Group) &&
      !type.arguments.empty())
    return error("source.layout", "scalar type has unexpected arguments");
  if ((type.kind == K::Boolean || type.kind == K::Index ||
       type.kind == K::Unit || type.kind == K::Tuple ||
       type.kind == K::Array) &&
      !type.domain.empty())
    return error("source.layout", "structural type has an unexpected identity");
  if (type.kind == K::Array && type.arguments.size() != 1)
    return error("source.layout", "array requires one element type");
  if (type.kind == K::Associated &&
      (type.arguments.size() != 1 || type.arguments.front().kind != K::Module))
    return error("source.layout", "associated type requires one module");
  auto result = std::make_shared<Layout>();
  result->type = type;
  // The revision-bound identity is formed once, when custody or a nominal
  // preimage first needs it, and otherwise after the layout is complete.
  auto identify = [&]() -> Error {
    if (!result->identity.digest.empty())
      return Error::success();
    auto canonical = canonicalTypeKey(type, [&](StringRef path) {
      return state->types->nominalAuthority(path);
    });
    if (!canonical)
      return canonical.takeError();
    if (auto e = charge(canonical->size()))
      return e;
    result->identity.digest = detail::digest(*canonical);
    result->identity.key = std::move(*canonical);
    return Error::success();
  };
  result->permissions = {true, true};
  result->constructible = true;
  auto *decl = state->types->typeDeclaration(type);
  if (decl) {
    for (const auto &role : decl->roles)
      if (auto e = charge(role.size() + 1))
        return std::move(e);
    result->roleParameters = decl->roles;
    result->restriction = decl->resource;
    result->sealed = decl->sealed;
    if (decl->generated)
      result->generatedIdentity = decl->generated->identity;
  }
  if (((type.kind == K::Record || type.kind == K::LogicalRecord) &&
       (!decl || decl->kind != Declaration::Kind::Record ||
        decl->logical != (type.kind == K::LogicalRecord))) ||
      (type.kind == K::Variant &&
       (!decl || decl->kind != Declaration::Kind::Variant)) ||
      (type.kind == K::Associated &&
       (!decl || decl->kind != Declaration::Kind::Associated || !decl->parent)))
    return error("source.layout", "nominal type declaration differs");
  std::map<std::string, Type> bindings;
  if (type.kind == K::LogicalRecord && decl && decl->roles.empty() &&
      !state->types->logicalRecord(type, {}))
    return state->types->takeError();
  if (decl) {
    const auto *owner = decl;
    const auto *args = &type.arguments;
    if (type.kind == K::Associated) {
      owner = &definitions[decl->parent->index];
      if (type.arguments.front().domain != owner->qualifiedName ||
          decl->abstract)
        return error("source.layout", "associated module identity differs");
      args = &type.arguments.front().arguments;
    }
    if (owner->parameters.size() != args->size())
      return error("source.layout", "nominal static arity differs");
    for (unsigned i = 0; i < args->size(); ++i)
      bindings.emplace(owner->parameters[i].atom, (*args)[i]);
    result->custody = decl->resource.has_value();
    if (result->custody) {
      // The slot names the revision-bound identity: equal lookup keys from
      // different source revisions never share custody.
      if (auto e = identify())
        return e;
      const auto &canonical = result->identity.key;
      auto slot = "zkl_resource_" + result->identity.digest;
      auto [entry, inserted] = slots.emplace(slot, canonical);
      if (!inserted && entry->second != canonical)
        return error("source.symbol",
                     "distinct source types have the same custody identity");
      if (slot.size() > limits.symbolBytes)
        return error("source.limit", "custody identity is too long");
      result->custodyCount = type.kind == K::LogicalRecord
                                 ? std::max<size_t>(1, decl->roles.size())
                                 : 1;
      for (unsigned i = 0; i < result->custodyCount; ++i)
        result->leaves.emplace_back(
            protocol::BoundType{"resource_unit", slot, {}});
    }
  }
  auto addField = [&](StringRef name, const Type &field,
                      std::vector<LayoutField> &fields,
                      std::vector<LayoutLeaf> &leaves,
                      const std::optional<Type> &maximumRows = {}) -> Error {
    auto closed = substitute(field, bindings, depth + 1);
    if (!closed)
      return closed.takeError();
    if (isLogicalValue(*closed) && type.kind != K::LogicalRecord &&
        !((type.kind == K::Tuple || type.kind == K::Array) &&
          isLogicalValue(type)))
      return error("source.oracle-aggregate",
                   "ordinary aggregates cannot contain oracle handles");
    std::optional<uint64_t> maximum;
    if (maximumRows) {
      auto bound = substitute(*maximumRows, bindings, depth + 1);
      if (!bound)
        return bound.takeError();
      if (bound->kind != K::Natural || !bound->dimension.isClosed())
        return error("source.layout",
                     "logical field row maximum is not closed");
      maximum = bound->dimension.closedValue();
    }
    auto layout = build(*closed, depth + 1);
    if (!layout)
      return layout.takeError();
    if (leaves.size() + (*layout)->leaves.size() > limits.aggregateLeaves)
      return error("source.limit", "aggregate layout exceeds leaf limit");
    if (auto e = charge(name.size() + 1))
      return e;
    for (const auto &leaf : (*layout)->leaves)
      if (auto e = charge(leaf.cost()))
        return e;
    result->formal |= (*layout)->formal;
    fields.push_back({name.str(), *layout, unsigned(leaves.size()), maximum});
    leaves.insert(leaves.end(), (*layout)->leaves.begin(),
                  (*layout)->leaves.end());
    return Error::success();
  };
  if (type.kind == K::Boolean)
    result->leaves = {protocol::BoundType{"bool", {}, {}}};
  else if (type.kind == K::Index)
    result->leaves = {protocol::BoundType{"index", {}, {}}};
  else if (type.kind == K::Field)
    result->leaves = {protocol::BoundType{"field", type.domain, {}}};
  else if (type.kind == K::Group)
    result->leaves = {protocol::BoundType{"group", type.domain, {}}};
  else if (isOracleHandle(type)) {
    auto formed = builtinType(oracleConstructor(type), type.arguments);
    if (!formed)
      return formed.takeError();
    auto kind = oracleKind(type.arguments.front());
    if (!kind)
      return kind.takeError();
    std::optional<uint64_t> maximum;
    if (type.kind == K::OracleSequence) {
      if (!type.arguments[1].dimension.isClosed())
        return error("source.generic",
                     "oracle sequence maximum remains symbolic");
      maximum = type.arguments[1].dimension.closedValue();
    }
    auto data = oracleMember(type.arguments.front(), "Data");
    if (!data)
      return data.takeError();
    if (type.kind == K::OracleSequence) {
      auto sequence = builtinType("sequence", {*data});
      if (!sequence)
        return sequence.takeError();
      data = std::move(sequence);
    }
    auto dataLayout = build(*data, depth + 1);
    if (!dataLayout)
      return dataLayout.takeError();
    result->oracleData = *dataLayout;
    result->leaves = {OracleLayout{std::move(*kind), maximum}};
  } else if (type.kind == K::Formal) {
    auto formed = formalType(type.domain, type.arguments);
    if (!formed)
      return formed.takeError();
    if (type.domain == "quotient") {
      const auto &q = type.arguments[0].dimension;
      const auto &n = type.arguments[1].dimension;
      if (!q.isClosed() || !n.isClosed())
        return error("source.generic",
                     "quotient layout requires closed parameters");
      result->formal = true;
      result->leaves = {QuotientLayout{q.closedValue(), n.closedValue()}};
    } else {
      auto field = builtinLayout(type.arguments[0]);
      if (!field)
        return field.takeError();
      const auto &arity = type.arguments[1].dimension;
      if (!arity.isClosed())
        return error("source.generic", "formal layout requires a closed arity");
      result->formal = true;
      result->leaves = {PolynomialLayout{field->identity, arity.closedValue()}};
    }
  } else if (type.kind == K::Builtin) {
    auto native = builtinLayout(
        type, [&](const Type &element) -> Expected<protocol::BoundType> {
          auto flat = build(element, depth + 1);
          if (!flat)
            return flat.takeError();
          auto packed = pack(*flat);
          if (!packed)
            return packed.takeError();
          return std::move(packed->carrier);
        });
    if (!native)
      return native.takeError();
    auto policy = protocol::nativeTypePolicy(*native);
    if (!policy)
      return error("source.builtin",
                   "native data lacks an installed type policy");
    result->leaves = {std::move(*native)};

  } else if (type.kind == K::Unit) {
  } else if (type.kind == K::Tuple) {
    for (unsigned i = 0; i < type.arguments.size(); ++i)
      if (auto e = addField(std::to_string(i), type.arguments[i],
                            result->fields, result->leaves))
        return e;
  } else if (type.kind == K::Array) {
    auto size = type.dimension.closedValue();
    if (size > limits.aggregateLeaves)
      return error("source.limit", "array layout exceeds length limit");
    if (size == 0) {
      auto element = substitute(type.arguments.front(), bindings, depth + 1);
      if (!element)
        return element.takeError();
      if (isLogicalValue(*element) && !isLogicalValue(type))
        return error("source.oracle-aggregate",
                     "empty arrays cannot erase logical category");
      auto layout = build(*element, depth + 1);
      if (!layout)
        return layout.takeError();
      result->formal = (*layout)->formal;
      result->element = *layout;
    }
    for (uint64_t i = 0; i < size; ++i)
      if (auto e = addField(std::to_string(i), type.arguments.front(),
                            result->fields, result->leaves))
        return e;
    if (!result->fields.empty())
      result->element = result->fields.front().layout;
  } else if ((type.kind == K::Record || type.kind == K::LogicalRecord) &&
             decl) {
    std::optional<std::vector<TypeField>> generatedFields;
    const auto *definitionFields = &decl->fields;
    if (decl->generated) {
      generatedFields = state->types->fields(type, {}, depth + 1);
      if (!generatedFields)
        return state->types->takeError();
      definitionFields = &*generatedFields;
    }
    for (const auto &field : *definitionFields) {
      if (auto e = addField(field.name, field.type, result->fields,
                            result->leaves, field.maximumRows))
        return e;
      result->fields.back().isPublic = field.isPublic;
      if (field.placement) {
        auto formula = placement(result->fields.back().layout->type,
                                 *field.placement, decl->roles.size());
        if (!formula)
          return formula.takeError();
        result->fields.back().placement = std::move(*formula);
      }
    }
  } else if (type.kind == K::Associated && decl && !decl->abstract) {
    if (auto e =
            addField("value", decl->domain, result->fields, result->leaves))
      return e;
    result->fields.back().isPublic = false;
  } else if (type.kind == K::Variant && decl) {
    // The native carrier remains ASCII; its nominal preimage is exact UTF-8.
    if (auto e = identify())
      return e;
    const auto &canonical = result->identity.key;
    if (canonical.size() > protocol::VariantSpellingBytes / 2)
      return error("source.limit",
                   "variant nominal encoding exceeds byte limit");
    if (auto e = charge(2 * canonical.size()))
      return e;
    protocol::VariantDescriptor descriptor{
        protocol::VariantIdentity::Tuple{"zkc.language",
                                         encodeNominalIdentity(canonical)},
        {}};
    for (unsigned i = 0; i < decl->alternatives.size(); ++i) {
      const auto &alt = decl->alternatives[i];
      LayoutAlternative logical{alt.name, {}};
      protocol::VariantAlternative native{nativeAlternativeName(i), {}};
      std::vector<LayoutLeaf> payload;
      for (auto &field : alt.fields) {
        if (auto e = addField(field.name, field.type, logical.fields, payload))
          return e;
        logical.fields.back().isPublic = field.isPublic;
      }
      if (result->formal)
        return error("source.formal",
                     "variant payload cannot contain formal values");
      for (const auto &leaf : payload) {
        const auto *data = leaf.data();
        if (!data)
          return error("source.formal",
                       "variant payload cannot contain formal leaves");
        native.payload.push_back(*data);
      }
      result->alternatives.push_back(std::move(logical));
      descriptor.alternatives.push_back(std::move(native));
    }
    auto carrier = protocol::variantType(std::move(descriptor));
    if (!carrier)
      return carrier.takeError();
    result->leaves.emplace_back(std::move(*carrier));
  } else
    return error("source.layout", "type has no closed native layout");
  if (result->formal && result->custody)
    return error("source.formal",
                 "formal values cannot have executable custody");
  for (auto &leaf : result->leaves)
    if (const auto *data = leaf.data()) {
      if (auto e = protocol::checkBoundType(*data, false))
        return e;
    }
  if (type.kind == K::LogicalRecord && decl && !decl->roles.empty()) {
    for (const auto &field : result->fields) {
      result->permissions.copy &= field.layout->permissions.copy;
      result->permissions.drop &= field.layout->permissions.drop;
    }
    if (decl->resource) {
      if (decl->resource == Resource::Affine && !result->permissions.drop)
        return error("source.permission", "affine fields must permit Drop");
      result->permissions.copy = false;
      result->permissions.drop = decl->resource == Resource::Affine;
    }
  } else {
    auto permissions = state->types->permissions(type, {});
    if (!permissions)
      return state->types->takeError();
    result->permissions = *permissions;
  }
  auto construction = state->types->admission(type, Boundary::Construction, {});
  if (!construction)
    return state->types->takeError();
  result->constructible =
      *construction == detail::Semantics::Admission::Accepted &&
      (!decl || !decl->generated || decl->generated->constructible);
  // Product construction packs already typed fields. External import separately
  // requires construction authority for every nested field and alternative.
  if (type.kind == K::Tuple ||
      (type.kind == K::Array && !result->fields.empty()))
    result->constructible = true;
  else if ((type.kind == K::Record || type.kind == K::Variant) && decl &&
           !decl->sealed && !decl->resource &&
           (!decl->generated || decl->generated->constructible)) {
    result->constructible =
        llvm::all_of(decl->fields,
                     [](const auto &field) { return field.isPublic; }) &&
        llvm::all_of(decl->alternatives, [](const auto &alternative) {
          return llvm::all_of(alternative.fields,
                              [](const auto &field) { return field.isPublic; });
        });
  }
  // Structural logical products keep source construction separate from byte
  // ingress.
  if (isLogicalValue(type))
    result->constructible = false;
  if (auto e = identify())
    return e;
  std::shared_ptr<const Layout> immutable = result;
  cache.emplace(std::move(key), immutable);
  return immutable;
}
} // namespace zkc::language
