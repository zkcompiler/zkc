#include "Checker.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;
namespace zkc::language::detail {
std::optional<ValuePlacement>
Semantics::remapPlacement(const ValuePlacement &value, ArrayRef<unsigned> map,
                          unsigned participants, Span span) {
  if (!charge(0, span))
    return {};
  auto remaining = work.remaining();
  const auto before = remaining;
  auto result = substitutePlacement(value, map, participants, remaining,
                                    work.limits.typeDepth);
  const bool charged = charge(before - remaining, span);
  if (!result) {
    accept(result.takeError(), span);
    return {};
  }
  if (!charged)
    return {};
  return std::move(*result);
}

std::optional<ValuePlacement> Semantics::placement(const Type &type,
                                                   const ValuePlacement &seed,
                                                   unsigned participants,
                                                   Span span, unsigned depth) {
  if (depth > work.limits.typeDepth || !chargeType(type, span)) {
    if (!diagnostic)
      fail("source.limit", "placed type depth limit exceeded", span);
    return {};
  }
  auto remaining = work.remaining();
  const auto before = remaining;
  auto error =
      validatePlacement(seed, participants, remaining, work.limits.typeDepth);
  const bool charged = charge(before - remaining, span);
  if (error) {
    accept(std::move(error), span);
    return {};
  }
  if (!charged)
    return {};
  if (const auto *data = std::get_if<DataPlacement>(&seed.value)) {
    if (isOracleHandle(type)) {
      fail("source.oracle-port",
           "oracle handles require explicit holder and receiver placement",
           span);
      return {};
    }
    if (!executableType(type, span))
      return {};
    if (data->roles.size() > 1) {
      auto admitted = admission(type, Boundary::Participants, span);
      if (!admitted)
        return {};
      if (*admitted == Admission::Rejected) {
        fail("source.participants",
             "field cannot have multiple participant components", span);
        return {};
      }
    }
    return seed;
  }
  if (std::holds_alternative<OraclePlacement>(seed.value)) {
    if (!isOracleHandle(type)) {
      fail("source.placement", "oracle placement requires a direct handle",
           span);
      return {};
    }
    return seed;
  }
  const auto &application = std::get<ProductPlacement>(seed.value);
  if (type.kind == Type::Kind::Tuple || type.kind == Type::Kind::Array) {
    if (application.fields.size() != type.arguments.size()) {
      fail("source.placement", "structural product placement arity differs",
           span);
      return {};
    }
    ProductPlacement result{typeIdentity(type), application.arguments, {}};
    std::set<unsigned> roles;
    for (unsigned i = 0; i < type.arguments.size(); ++i) {
      auto child = placement(type.arguments[i], application.fields[i],
                             participants, span, depth + 1);
      if (!child)
        return {};
      auto participants = placementRoles(*child);
      roles.insert(participants.begin(), participants.end());
      result.fields.push_back(std::move(*child));
    }
    result.arguments.assign(roles.begin(), roles.end());
    return ValuePlacement(std::move(result));
  }
  const auto *decl = typeDeclaration(type);
  if (type.kind != Type::Kind::LogicalRecord || !decl || decl->roles.empty() ||
      application.arguments.size() != decl->roles.size()) {
    fail("source.placement", "product role application does not match its type",
         span);
    return {};
  }
  auto fields = this->fields(type, span, depth + 1);
  if (!fields)
    return {};
  ProductPlacement result{typeIdentity(type), application.arguments, {}};
  for (const auto &field : *fields) {
    if (!field.placement) {
      fail("source.placement", "distributed field requires a placement",
           field.span);
      return {};
    }
    auto mapped = remapPlacement(*field.placement, application.arguments,
                                 participants, field.span);
    auto child = mapped ? placement(field.type, *mapped, participants,
                                    field.span, depth + 1)
                        : std::nullopt;
    if (!child)
      return {};
    result.fields.push_back(std::move(*child));
  }
  return ValuePlacement(std::move(result));
}

std::optional<PlacedType>
Semantics::substitutePlaced(const PlacedType &input,
                            const Substitution &bindings, unsigned participants,
                            Span span) {
  auto type = substitute(input.type, bindings, span);
  if (!type)
    return {};
  PlacedType result{std::move(*type)};
  if (input.placement) {
    result.placement =
        placement(result.type, *input.placement, participants, span);
    if (!result.placement)
      return {};
  }
  return result;
}

bool Semantics::admitPlaced(const PlacedType &value, Span span,
                            const Declaration *context, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic
               ? false
               : fail("source.limit", "placed admission depth exceeded", span);
  if (!value.placement)
    return true;
  if (const auto *data = std::get_if<DataPlacement>(&value.placement->value))
    return data->roles.size() < 2 ||
           admit(value.type, Boundary::Participants, span, context);
  const auto *product = std::get_if<ProductPlacement>(&value.placement->value);
  if (!product)
    return true;
  std::vector<Type> children;
  if (value.type.kind == Type::Kind::Array ||
      value.type.kind == Type::Kind::Tuple)
    children = value.type.arguments;
  else {
    auto schema = fields(value.type, span, depth + 1);
    if (!schema)
      return false;
    for (const auto &field : *schema)
      children.push_back(field.type);
  }
  if (children.size() != product->fields.size())
    return fail("source.placement", "placed admission schema arity differs",
                span);
  for (unsigned i = 0; i < children.size(); ++i)
    if (!admitPlaced({children[i], product->fields[i]}, span, context,
                     depth + 1))
      return false;
  return true;
}

std::optional<ValuePlacement>
Semantics::projectedPlacement(const Type &input, const ValuePlacement &root,
                              ArrayRef<unsigned> path, Span span) {
  // Select within the root tree and copy only the selected subtree.
  Type type = input;
  const ValuePlacement *result = &root;
  for (auto ordinal : path) {
    if (!charge(1, span))
      return {};
    if (type.kind == Type::Kind::Array) {
      if (type.dimension.isClosed() &&
          ordinal >= type.dimension.closedValue()) {
        fail("source.index", "static array index is out of range", span);
        return {};
      }
      if (const auto *product = std::get_if<ProductPlacement>(&result->value)) {
        if (product->instance != typeIdentity(type) ||
            product->fields.size() != 1) {
          fail("source.placement",
               "array element placement disagrees with its schema", span);
          return {};
        }
        result = &product->fields[0];
      } else if (!std::holds_alternative<DataPlacement>(result->value)) {
        fail("source.placement",
             "array requires data or element-schema placement", span);
        return {};
      }
      auto element = type.arguments.front();
      type = std::move(element);
      continue;
    }
    std::optional<std::vector<TypeField>> computed;
    const auto *fields = productFields(type, span, 1, computed);
    if (!fields || ordinal >= fields->size()) {
      if (!diagnostic)
        fail("source.placement", "invalid placed field ordinal", span);
      return {};
    }
    if (const auto *product = std::get_if<ProductPlacement>(&result->value)) {
      if (product->instance != typeIdentity(type) ||
          product->fields.size() != fields->size()) {
        fail("source.placement", "placed product disagrees with its schema",
             span);
        return {};
      }
      result = &product->fields[ordinal];
    } else if (!std::holds_alternative<DataPlacement>(result->value)) {
      fail("source.placement", "direct oracle has no ordinary product fields",
           span);
      return {};
    }
    auto selected = (*fields)[ordinal].type;
    type = std::move(selected);
  }
  return *result;
}

std::optional<PlacedType> Checker::placedType(const Declaration &context,
                                              const SyntaxType &syntax,
                                              unsigned depth) {
  auto resolved = type(context, syntax, depth, true);
  if (!resolved)
    return {};
  PlacedType result{*resolved};
  const Declaration *alias = nullptr;
  if (syntax.kind == SyntaxType::Kind::Name) {
    auto id = resolve(context, syntax.name, syntax.span, false);
    if (types.diagnostic)
      return {};
    if (id && output.declarations[id->index].kind == Declaration::Kind::Alias)
      alias = &output.declarations[id->index];
  }
  if (alias && alias->placement && syntax.components) {
    types.fail("source.placement",
               "a placed alias cannot have an overriding outer placement",
               syntax.span);
    return {};
  }
  if (syntax.kind == SyntaxType::Kind::Tuple ||
      syntax.kind == SyntaxType::Kind::Array) {
    const unsigned arity =
        syntax.kind == SyntaxType::Kind::Array ? 1 : syntax.arguments.size();
    std::vector<PlacedType> children;
    bool placed = isLogicalValue(*resolved);
    for (unsigned i = 0; i < arity; ++i) {
      auto child = placedType(context, syntax.arguments[i], depth + 1);
      if (!child)
        return {};
      placed |= child->placement.has_value();
      children.push_back(std::move(*child));
    }
    if (placed) {
      if (syntax.roles || syntax.components) {
        types.fail("source.placement",
                   "structural product placements belong to its children",
                   syntax.span);
        return {};
      }
      ProductPlacement schema{typeIdentity(*resolved), {}, {}};
      std::set<unsigned> participants;
      for (const auto &child : children) {
        if (!child.placement) {
          types.fail("source.placement",
                     "distributed product child requires placement",
                     syntax.span);
          return {};
        }
        auto roles = placementRoles(*child.placement);
        participants.insert(roles.begin(), roles.end());
        schema.fields.push_back(*child.placement);
      }
      schema.arguments.assign(participants.begin(), participants.end());
      result.placement = types.placement(
          *resolved, schema, context.roles.size(), syntax.span, depth);
      return result.placement ? std::optional(result) : std::nullopt;
    }
  }
  if (syntax.components) {
    if (syntax.roles) {
      types.fail("source.placement", "product cannot have an outer placement",
                 syntax.span);
      return {};
    }
    auto selected = roles(context, *syntax.components, syntax.span);
    if (!selected)
      return {};
    if (syntax.oracleHolder) {
      auto holder = roleArguments(context, {*syntax.oracleHolder}, syntax.span);
      if (!holder)
        return {};
      result.placement = OraclePlacement{holder->front(), *selected};
    } else
      result.placement = DataPlacement{*selected};
    result.placement = types.placement(
        *resolved, *result.placement, context.roles.size(), syntax.span, depth);
    return result.placement ? std::optional(result) : std::nullopt;
  }
  // Aliases can retain a role abstraction with a reordered target map. Its
  // ordinary Type remains exactly the target's static/nominal identity.
  if (alias && alias->placement) {
    auto args = arguments(context, *alias, syntax.arguments, syntax.span,
                          syntax.labels);
    if (!args)
      return {};
    auto target = types.substitutePlaced({alias->domain, alias->placement},
                                         types.substitution(*alias, *args),
                                         alias->roles.size(), syntax.span);
    if (!target)
      return {};
    if (!syntax.roles) {
      types.fail("source.roles", "alias requires an explicit role application",
                 syntax.span);
      return {};
    }
    auto mapping = roleArguments(context, *syntax.roles, syntax.span);
    if (!mapping || mapping->size() != alias->roles.size()) {
      if (!types.diagnostic)
        types.fail("source.roles", "alias role application arity differs",
                   syntax.span);
      return {};
    }
    auto mapped = types.remapPlacement(*target->placement, *mapping,
                                       context.roles.size(), syntax.span);
    if (!mapped)
      return {};
    result.placement = types.placement(result.type, *mapped,
                                       context.roles.size(), syntax.span);
  } else if (syntax.roles) {
    const auto *definition = types.typeDeclaration(*resolved);
    if (!definition || resolved->kind != Type::Kind::LogicalRecord ||
        definition->roles.empty()) {
      types.fail("source.roles", "role application requires a distributed type",
                 syntax.span);
      return {};
    }
    auto mapping = roleArguments(context, *syntax.roles, syntax.span);
    if (!mapping || mapping->size() != definition->roles.size()) {
      if (!types.diagnostic)
        types.fail("source.roles", "record role application arity differs",
                   syntax.span);
      return {};
    }
    // The initial seed only supplies the ordered map. Recompute all schema
    // fields and nominal identity, including statics, in the semantic owner.
    result.placement = types.placement(
        *resolved, ProductPlacement{typeIdentity(*resolved), *mapping, {}},
        context.roles.size(), syntax.span, depth);
  }
  if ((syntax.roles || (alias && alias->placement)) && !result.placement)
    return {};
  return result;
}
} // namespace zkc::language::detail
