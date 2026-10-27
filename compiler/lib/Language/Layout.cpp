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
#include "llvm/ADT/StringExtras.h"
#include <limits>
using namespace llvm;
namespace zkc::language {
Expected<std::string> LayoutIdentities::get(const Layout &layout) {
  if (auto found = cache.find(&layout); found != cache.end())
    return found->second;
  auto key = typeIdentity(layout.type);
  if (key.size() > remaining)
    return error("source.limit", "schema type identity limit exceeded");
  remaining -= key.size();
  FramedHash hash(remaining);
  hash.frame("zkc.language.schema/0");
  hash.frame(typeKindName(layout.type.kind));
  hash.frame(toHex(SHA256::hash(arrayRefFromStringRef(key)), true));
  if (!layout.generatedIdentity.empty())
    hash.frame(layout.generatedIdentity);
  hash.frame(layout.custody ? "1" : "0");
  hash.frame(layout.constructible ? "1" : "0");
  for (bool allowed : {layout.permissions.copy, layout.permissions.drop})
    hash.frame(allowed ? "1" : "0");
  hash.frame(std::to_string(layout.leaves.size()));
  for (const auto &leaf : layout.leaves) {
    if (!leaf.data())
      return error("source.formal", "relation schema contains a formal leaf");
    hash.frame(*leaf.data());
  }
  auto fields = [&](ArrayRef<LayoutField> fields) -> Error {
    hash.frame(std::to_string(fields.size()));
    for (const auto &field : fields) {
      hash.frame(field.name);
      hash.frame(std::to_string(field.offset));
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
  detail::Work work;
  const std::vector<Declaration> &declarations;
  std::optional<detail::Semantics> types;
  State(const std::vector<Declaration> &declarations, const Limits &limits)
      : work{limits}, declarations(declarations) {}
};
Layouts::Layouts(const CheckedProject &project, const Limits &limits)
    : definitions(project.declarations()), limits(limits),
      state(std::make_unique<State>(project.storage->declarations,
                                    this->limits)) {}
Layouts::Layouts(const ClosedEntry &entry, const Limits &limits)
    : definitions(entry.declarations()), limits(limits),
      state(
          std::make_unique<State>(entry.storage->declarations, this->limits)) {}
Layouts::~Layouts() = default;
Layouts::Layouts(const std::vector<Declaration> &declarations,
                 const Limits &limits)
    : definitions(declarations), limits(limits),
      state(std::make_unique<State>(declarations, this->limits)) {}
Expected<protocol::BoundType>
detail::Semantics::nativeLayout(const Type &type) {
  if (isNativeData(type) &&
      !(type.kind == Type::Kind::Builtin && type.domain == "sequence"))
    return builtinLayout(type);
  auto limits = work.limits;
  limits.work -= work.used;
  Layouts layouts(declarations, limits);
  auto result = layouts.packed(type);
  auto charged = work.charge(layouts.state->work.used);
  if (!result) {
    consumeError(std::move(charged));
    return result.takeError();
  }
  if (charged)
    return std::move(charged);
  return std::move(result->carrier);
}
Expected<PackedLayout> Layouts::packed(const Type &type) {
  auto flat = get(type);
  if (!flat)
    return flat.takeError();
  return pack(*flat);
}
Expected<PackedLayout> Layouts::pack(std::shared_ptr<const Layout> flat) {
  if (!isSequenceElement(flat->type) || flat->formal || flat->custody ||
      !flat->permissions.copy || !flat->permissions.drop)
    return error("source.sequence",
                 "sequence element requires executable Copy and Drop data");
  using K = Type::Kind;
  bool product = flat->type.kind == K::Record || flat->type.kind == K::Tuple ||
                 flat->type.kind == K::Array || flat->type.kind == K::Unit ||
                 flat->type.kind == K::Associated;
  if (!product) {
    if (flat->leaves.size() != 1 || !flat->leaves.front().data())
      return error("source.layout", "native element requires one data leaf");
    auto carrier =
        protocol::parseBoundType(*flat->leaves.front().data(), false);
    if (!carrier)
      return carrier.takeError();
    return PackedLayout{std::move(flat), std::move(*carrier), false, {}};
  }
  auto identity = typeIdentity(flat->type);
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
      json::Array{"zkc.language.pack", encodeNominalIdentity(identity)},
      {alternative}};
  auto encoded = protocol::encodeVariant(descriptor);
  if (!encoded)
    return error("source.limit",
                 "packed product exceeds native descriptor limits");
  auto carrier = protocol::parseBoundType(*encoded, false);
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
Error Layouts::charge(uint64_t n) { return state->work.charge(n); }
Expected<LayoutSlice> Layouts::select(const Declaration &decl,
                                      const SpecificationSelector &selector) {
  return select(selector.output ? decl.outputs : decl.inputs, selector.port,
                selector.path);
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
  std::shared_ptr<const Layout> selected;
  for (unsigned i = 0; i <= port; ++i) {
    if (auto error = charge(1))
      return std::move(error);
    auto layout = get(ports[i].type);
    if (!layout)
      return layout.takeError();
    if (i == port)
      selected = *layout;
    else
      offset += (*layout)->leaves.size();
  }
  for (auto field : path) {
    if (auto error = charge(1))
      return std::move(error);
    if (selected->custody || selected->type.kind == Type::Kind::Associated ||
        selected->type.kind == Type::Kind::Variant ||
        field >= selected->fields.size())
      return error("source.layout",
                   "logical selector is not a product projection");
    offset += selected->fields[field].offset;
    selected = selected->fields[field].layout;
  }
  if (offset > std::numeric_limits<unsigned>::max())
    return error("source.limit",
                 "logical selector offset exceeds native bounds");
  return LayoutSlice{static_cast<unsigned>(offset), std::move(selected)};
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
  if (!state->types) {
    for (const auto &decl : definitions) {
      if (auto e = charge(decl.qualifiedName.size() + 1))
        return std::move(e);
      for (const auto &parameter : decl.parameters)
        if (auto e = charge(parameter.atom.size() + 1))
          return std::move(e);
    }
    // Layouts see closed types only; no asset projection remains to resolve.
    state->types.emplace(state->declarations, ArrayRef<Asset>(), state->work);
  }
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
  result->permissions = {true, true};
  result->constructible = true;
  auto *decl = state->types->typeDeclaration(type);
  if (decl && decl->generated)
    result->generatedIdentity = decl->generated->identity;
  if ((type.kind == K::Record &&
       (!decl || decl->kind != Declaration::Kind::Record)) ||
      (type.kind == K::Variant &&
       (!decl || decl->kind != Declaration::Kind::Variant)) ||
      (type.kind == K::Associated &&
       (!decl || decl->kind != Declaration::Kind::Associated || !decl->parent)))
    return error("source.layout", "nominal type declaration differs");
  std::map<std::string, Type> bindings;
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
      auto slot = "zkl_resource_" + detail::digest(key);
      auto [entry, inserted] = slots.emplace(slot, key);
      if (!inserted && entry->second != key)
        return error("source.symbol",
                     "distinct source types have the same custody identity");
      if (slot.size() > limits.symbolBytes)
        return error("source.limit", "custody identity is too long");
      result->leaves.push_back("resource_unit:" + slot);
    }
  }
  auto addField = [&](StringRef name, const Type &field,
                      std::vector<LayoutField> &fields,
                      std::vector<LayoutLeaf> &leaves) -> Error {
    auto closed = substitute(field, bindings, depth + 1);
    if (!closed)
      return closed.takeError();
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
    fields.push_back({name.str(), *layout, unsigned(leaves.size())});
    leaves.insert(leaves.end(), (*layout)->leaves.begin(),
                  (*layout)->leaves.end());
    return Error::success();
  };
  if (type.kind == K::Boolean)
    result->leaves = {"bool"};
  else if (type.kind == K::Index)
    result->leaves = {"index"};
  else if (type.kind == K::Field)
    result->leaves = {"field:" + type.domain};
  else if (type.kind == K::Group)
    result->leaves = {"group:" + type.domain};
  else if (type.kind == K::Formal) {
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
    result->leaves = {native->spelling()};

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
      auto layout = build(*element, depth + 1);
      if (!layout)
        return layout.takeError();
      result->formal = (*layout)->formal;
    }
    for (uint64_t i = 0; i < size; ++i)
      if (auto e = addField(std::to_string(i), type.arguments.front(),
                            result->fields, result->leaves))
        return e;
  } else if (type.kind == K::Record && decl) {
    for (auto &field : decl->fields) {
      if (auto e =
              addField(field.name, field.type, result->fields, result->leaves))
        return e;
    }
  } else if (type.kind == K::Associated && decl && !decl->abstract) {
    if (auto e =
            addField("value", decl->domain, result->fields, result->leaves))
      return e;
  } else if (type.kind == K::Variant && decl) {
    // The native carrier remains ASCII; its nominal preimage is exact UTF-8.
    if (key.size() > protocol::VariantSpellingBytes / 2)
      return error("source.limit",
                   "variant nominal encoding exceeds byte limit");
    if (auto e = charge(2 * key.size()))
      return e;
    protocol::VariantDescriptor descriptor{
        json::Array{"zkc.language", encodeNominalIdentity(key)}, {}};
    for (unsigned i = 0; i < decl->alternatives.size(); ++i) {
      const auto &alt = decl->alternatives[i];
      LayoutAlternative logical{alt.name, {}};
      protocol::VariantAlternative native{nativeAlternativeName(i), {}};
      std::vector<LayoutLeaf> payload;
      for (auto &field : alt.fields)
        if (auto e = addField(field.name, field.type, logical.fields, payload))
          return e;
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
    auto encoded = protocol::encodeVariant(descriptor);
    if (!encoded)
      return error("source.layout", "variant exceeds native descriptor limits");
    result->leaves.push_back(std::move(*encoded));
  } else
    return error("source.layout", "type has no closed native layout");
  // Plain linear records are source obligations, not native resources. Keep
  // native custody only when the payload itself contains a native resource.
  // In particular, a loop may consume a plain claim and yield a successor.
  if (type.kind == K::Record && decl && decl->resource == Resource::Linear &&
      result->custody &&
      llvm::all_of(ArrayRef(result->leaves).drop_front(),
                   [](const LayoutLeaf &leaf) {
                     if (!leaf.data())
                       return false;
                     auto bound = protocol::parseBoundType(*leaf.data(), false);
                     if (!bound) {
                       consumeError(bound.takeError());
                       return false;
                     }
                     auto policy = protocol::nativeTypePolicy(*bound);
                     return policy && policy->shared && !policy->affine;
                   })) {
    result->custody = false;
    result->leaves.erase(result->leaves.begin());
    for (auto &field : result->fields)
      --field.offset;
  }
  if (result->formal && result->custody)
    return error("source.formal",
                 "formal values cannot have executable custody");
  for (auto &leaf : result->leaves)
    if (const auto *data = leaf.data()) {
      auto bound = protocol::parseBoundType(*data, false);
      if (!bound)
        return bound.takeError();
    }
  auto permissions = state->types->permissions(type, {});
  if (!permissions)
    return state->types->takeError();
  result->permissions = *permissions;
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
  std::shared_ptr<const Layout> immutable = result;
  cache.emplace(std::move(key), immutable);
  return immutable;
}
} // namespace zkc::language
