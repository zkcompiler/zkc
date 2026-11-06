#include "Semantics.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Language/Builtins.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
Permissions intersect(Permissions a, const Permissions &b) {
  return {a.copy && b.copy, a.drop && b.drop};
}
} // namespace

std::shared_ptr<const std::vector<TypeField>>
Semantics::fields(const Type &type, Span span, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "field expansion depth", span);
    return nullptr;
  }
  std::vector<TypeField> result;
  auto finish = [&]() -> std::shared_ptr<const std::vector<TypeField>> {
    if (!charge(1, span))
      return {};
    return std::make_shared<const std::vector<TypeField>>(std::move(result));
  };
  if (type.kind == Type::Kind::Unit)
    return finish();
  if (type.kind == Type::Kind::Tuple) {
    for (unsigned i = 0; i < type.arguments.size(); ++i) {
      if (!chargeType(type.arguments[i], span))
        return nullptr;
      result.push_back({std::to_string(i), type.arguments[i], true, span});
    }
    return finish();
  }
  if (type.kind == Type::Kind::Array) {
    if (!type.dimension.isClosed()) {
      fail("source.bound", "array expansion requires a closed length", span);
      return nullptr;
    }
    if (type.dimension.closedValue() > work.limits.aggregateLeaves) {
      fail("source.limit", "array layout exceeds bound", span);
      return nullptr;
    }
    if (!charge(type.dimension.closedValue(), span))
      return nullptr;
    for (uint64_t i = 0; i < type.dimension.closedValue(); ++i) {
      if (!chargeType(type.arguments.front(), span))
        return nullptr;
      result.push_back({std::to_string(i), type.arguments.front(), true, span});
    }
    return finish();
  }
  if (!charge(type.domain.size() + 1, span))
    return {};
  auto *decl = typeDeclaration(type);
  if (!decl || (type.kind != Type::Kind::Record &&
                type.kind != Type::Kind::LogicalRecord &&
                type.kind != Type::Kind::Associated)) {
    fail("source.type",
         "type has no product fields; variants require match: " +
             spelling(type),
         span);
    return nullptr;
  }
  if (decl->generated) {
    StringRef member = decl->generated->member;
    if (member.contains(':') || member == "Public" || member == "Witness" ||
        member == "ProverOutputs" || member == "VerifierOutputs") {
      if (!chargeType(type, span))
        return {};
      auto selected = entryFamilyFields(*decl, type.arguments, span);
      if (!selected)
        return nullptr;
      for (auto &field : *selected)
        result.push_back(
            {std::move(field.name), std::move(field.type), true, span});
      return finish();
    }
  }
  if (type.kind == Type::Kind::Associated) {
    if (decl->abstract) {
      fail("source.private", "abstract type representation is unavailable",
           span);
      return nullptr;
    }
    const auto &base = type.arguments.front();
    auto &owner = declarations[decl->parent->index];
    if (!chargeType(base, span))
      return nullptr;
    for (const auto &parameter : owner.parameters)
      if (!charge(parameter.atom.size() + 1, span))
        return nullptr;
    auto bindings = substitution(owner, base.arguments);
    auto repr = substitute(decl->domain, bindings, span, depth + 1);
    if (!repr)
      return nullptr;
    result.push_back({"value", std::move(*repr), false, span});
    return finish();
  }
  // Placement checks walk each field of a wide record once per placed role;
  // reuse the substituted declaration instead of expanding it again.
  // Route by the bounded root head only. Compare the complete candidate while
  // performing its mandatory preflight, without a separate hash walk or
  // equality traversal. No routing hash confers admission authority.
  auto sample = [](StringRef text) {
    return text.empty()
               ? llvm::hash_value(size_t(0))
               : llvm::hash_combine(text.size(), text.front(),
                                    text[text.size() / 2], text.back());
  };
  uint64_t nodes = work.limits.typeNodes;
  std::function<std::optional<llvm::hash_code>(const Type &, unsigned)> route =
      [&](const Type &term, unsigned level) -> std::optional<llvm::hash_code> {
    if (!nodes || level > work.limits.typeDepth || !charge(4, span)) {
      if (!diagnostic)
        fail("source.limit", "field lookup type bound", span);
      return {};
    }
    --nodes;
    auto key = llvm::hash_value(unsigned(term.kind));
    if (term.kind != Type::Kind::Natural)
      key = llvm::hash_combine(
          key, sample(term.domain), sample(term.sort), term.symbolic,
          term.arguments.size(),
          term.kind == Type::Kind::Descriptor ? unsigned(term.family) : 0);
    for (const auto &[factors, coefficient] : term.dimension.terms()) {
      if (!charge(2, span))
        return {};
      key = llvm::hash_combine(key, coefficient, factors.size());
      for (const auto &factor : factors) {
        if (!charge(4, span))
          return {};
        key = llvm::hash_combine(key, unsigned(factor.kind),
                                 sample(factor.name), sample(factor.member));
      }
    }
    if (term.kind != Type::Kind::Natural)
      for (const auto &argument : term.arguments) {
        auto child = route(argument, level + 1);
        if (!child)
          return {};
        key = llvm::hash_combine(key, *child);
      }
    return key;
  };
  auto routed = route(type, 1);
  if (!routed)
    return {};
  auto hash = size_t(*routed);
  auto found = declaredFields.find(hash);
  bool checked = false;
  if (found != declaredFields.end())
    for (const auto &entry : llvm::reverse(found->second)) {
      auto equal = sameSnapshot(type, entry.type, span);
      if (!equal)
        return {};
      checked = true;
      if (*equal) {
        if (depth <= entry.depth)
          return entry.fields;
        break;
      }
    }
  if (!checked && !chargeType(type, span))
    return {};
  // Cache hits never construct a substitution. On a miss, admit each owned
  // argument/name copy before building the map.
  if (!chargeType(type, span, /*complete=*/false))
    return nullptr;
  for (const auto &parameter : decl->parameters)
    if (!charge(parameter.atom.size() + 1, span))
      return nullptr;
  auto bindings = substitution(*decl, type.arguments);
  std::vector<TypeField> expanded;
  for (const auto &source : decl->fields) {
    if (!charge(source.name.size() + 1, span))
      return nullptr;
    auto t = substitute(source.type, bindings, span, depth + 1);
    if (!t)
      return nullptr;
    TypeField field{source.name, std::move(*t), source.isPublic, source.span};
    if (source.maximumRows) {
      field.maximumRows =
          substitute(*source.maximumRows, bindings, span, depth + 1);
      if (!field.maximumRows)
        return nullptr;
    }
    if (source.placement) {
      field.placement = placement(field.type, *source.placement,
                                  decl->roles.size(), field.span, depth + 1);
      if (!field.placement)
        return nullptr;
    }
    if (type.kind == Type::Kind::LogicalRecord && !oracleField(field))
      return nullptr;
    expanded.push_back(std::move(field));
  }
  if (!chargeType(type, span, /*complete=*/false) || !charge(1, span))
    return {};
  auto fields =
      std::make_shared<const std::vector<TypeField>>(std::move(expanded));
  // Append an immutable depth version. Existing shared results and their
  // addresses remain valid even if a deeper query recomputes the fields.
  declaredFields[hash].emplace_back(type, fields, depth);
  return fields;
}
bool Semantics::oracleField(const TypeField &field) {
  if (field.maximumRows) {
    if (!chargeType(*field.maximumRows, field.span))
      return false;
    if (field.maximumRows->kind != Type::Kind::Natural)
      return fail("source.oracle-shape",
                  "field row maximum must be a static natural", field.span);
  }
  if (!isOracleHandle(field.type))
    return !field.maximumRows ||
           fail("source.oracle-shape",
                "row bounds require a direct oracle field", field.span);
  unsigned arity = field.type.kind == Type::Kind::OracleSequence ? 2 : 1;
  if (field.type.arguments.size() != arity)
    return fail("source.oracle-kind", "invalid direct oracle field",
                field.span);
  const auto &kind = field.type.arguments.front();
  if (kind.kind != Type::Kind::OracleKind)
    return fail("source.oracle-kind", "field requires an oracle kind",
                field.span);
  if (kind.symbolic)
    return true;
  if (!symbolic(kind) && !oracleKind(kind, field.span))
    return false;
  if ((kind.arguments.size() == 1) != field.maximumRows.has_value())
    return fail("source.oracle-shape",
                "only an unsized oracle field requires a row maximum",
                field.span);
  return true;
}
bool Semantics::logicalRecord(const Type &type, Span span) {
  if (!chargeType(type, span))
    return false;
  const auto *decl = typeDeclaration(type);
  if (type.kind != Type::Kind::LogicalRecord || !decl ||
      decl->kind != Declaration::Kind::Record || !decl->logical)
    return fail("source.type", "expected a nominal logical record", span);
  auto &checked = checkedLogicalRecords[size_t(typeLookupHash(type))];
  for (const auto &candidate : checked) {
    auto equal = sameSnapshot(type, candidate, span, /*complete=*/false);
    if (!equal)
      return false;
    if (*equal)
      return true;
  }
  auto retain = [&] {
    if (!chargeType(type, span, /*complete=*/false))
      return false;
    checked.push_back(type);
    return true;
  };
  if (decl->resource && decl->roles.empty())
    return fail("source.resource", "logical records require Copy and Drop",
                decl->span);
  auto product = fields(type, span);
  if (!product)
    return false;
  if (!decl->roles.empty()) {
    for (const auto &field : *product)
      if (!field.placement)
        return fail("source.placement", "distributed field has no placement",
                    field.span);
    return retain();
  }
  bool logical = false;
  for (const auto &field : *product) {
    if (isOracleHandle(field.type))
      logical = true;
    else if (!sharedData(field.type, field.span, decl))
      return false;
  }
  if (!logical)
    return fail("source.oracle-aggregate",
                "logical record requires a direct oracle handle or sequence",
                decl->span);
  return retain();
}
std::optional<std::vector<Alternative>>
Semantics::alternatives(const Type &type, Span span, unsigned depth) {
  auto *decl = typeDeclaration(type);
  if (!decl || decl->kind != Declaration::Kind::Variant) {
    fail("source.type", "match requires a nominal variant", span);
    return {};
  }
  if (depth > work.limits.typeDepth ||
      !charge(decl->alternatives.size(), span)) {
    if (!diagnostic)
      fail("source.limit", "variant expansion depth", span);
    return {};
  }
  for (const auto &alt : decl->alternatives)
    for (const auto &field : alt.fields)
      if (!chargeType(field.type, span))
        return {};
  auto result = decl->alternatives;
  auto bindings = substitution(*decl, type.arguments);
  for (auto &alt : result)
    for (auto &field : alt.fields) {
      auto t = substitute(field.type, bindings, span, depth + 1);
      if (!t)
        return {};
      field.type = std::move(*t);
    }
  return result;
}
std::optional<Permissions> Semantics::permissions(const Type &type, Span span,
                                                  const Declaration *scope,
                                                  unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "permission expansion depth", span);
    return {};
  }
  using K = Type::Kind;
  auto scoped = [&](Permissions inherent) -> std::optional<Permissions> {
    auto include = [&](Permissions p) {
      inherent = {inherent.copy || p.copy, inherent.drop || p.drop};
    };
    if (scope) {
      // Copy already implies Drop. Once both permissions follow from the
      // value itself, no parameter-name lookup can strengthen the answer.
      // Bound candidates below are still completely checked on every query.
      if (!inherent.copy)
        for (const auto &parameter : scope->parameters) {
          if (!charge(parameter.atom.size() + 1, span))
            return {};
          if (parameter.atom == type.domain)
            include(parameter.permissions);
        }
      for (const auto &bound : scope->permissionBounds) {
        if (!chargeType(bound.type, span))
          return {};
        if (type == bound.type)
          include(bound.permissions);
      }
    }
    inherent.drop |= inherent.copy;
    return inherent;
  };
  if (isStaticOnly(type)) {
    fail("source.type", "static term has no runtime permissions", span);
    return {};
  }
  if (type.symbolic || type.kind == K::Parameter)
    return scoped(type.assumptions);
  if (type.kind == K::Associated) {
    auto *decl = typeDeclaration(type);
    if (!decl) {
      fail("source.type", "unknown associated type", span);
      return {};
    }
    Permissions result;
    if (decl->abstract)
      result = decl->permissions.value_or(Permissions{});
    else {
      auto representation = fields(type, span, depth + 1);
      auto properties = representation
                            ? permissions(representation->front().type, span,
                                          scope, depth + 1)
                            : std::nullopt;
      if (!properties)
        return {};
      result = *properties;
      if (decl->permissions && !result.includes(*decl->permissions)) {
        fail("source.permission", "associated promises exceed representation",
             decl->span);
        return {};
      }
    }
    if (decl->resource) {
      if (*decl->resource == Resource::Affine && !result.drop &&
          !decl->abstract) {
        fail("source.permission", "affine representation must permit Drop",
             decl->span);
        return {};
      }
      result.copy = false;
      result.drop = *decl->resource == Resource::Affine;
    }
    // Generic assumptions refine unknown properties, never an authored
    // restriction on this nominal type.
    return decl->resource ? std::optional(result) : scoped(result);
  }
  if (type.kind == K::Boolean || type.kind == K::Index ||
      type.kind == K::Field || type.kind == K::Group || type.kind == K::Unit)
    return Permissions{true, true};
  if (type.kind == K::LogicalRecord && !logicalRecord(type, span))
    return {};
  if (type.kind == K::Formal || isOracleHandle(type))
    return Permissions{true, true};
  if (type.kind == K::Builtin) {
    auto formed = builtinType(type.domain, type.arguments);
    if (!formed) {
      fail("source.builtin", toString(formed.takeError()), span);
      return {};
    }
    if (type.domain == "sequence") {
      const auto &element = type.arguments.front();
      auto child = permissions(element, span, scope, depth + 1);
      if (!child)
        return {};
      if (!executableType(element, span, depth + 1))
        return {};
      return child;
    }
    if (!symbolic(type)) {
      auto native = builtinLayout(type);
      if (!native) {
        accept(native.takeError(), span);
        return {};
      }
      return Permissions{protocol::duplicable(*native),
                         protocol::discardable(*native)};
    }
    const auto *base = protocol::typePermissions(type.domain);
    Permissions result{base && base->copy, base && base->drop};
    for (const auto &argument : type.arguments) {
      if (isStaticOnly(argument))
        continue;
      auto child = permissions(argument, span, scope, depth + 1);
      if (!child)
        return {};
      result = intersect(result, *child);
    }
    return result;
  }
  Permissions result{true, true};
  auto include = [&](const Type &child) {
    auto p = permissions(child, span, scope, depth + 1);
    if (!p)
      return false;
    result = intersect(result, *p);
    return true;
  };
  if (type.kind == K::Tuple || type.kind == K::Array) {
    for (const auto &child : type.arguments)
      if (!include(child))
        return {};
  } else if (type.kind == K::Record || type.kind == K::LogicalRecord) {
    auto fs = fields(type, span, depth + 1);
    if (!fs)
      return {};
    for (const auto &field : *fs)
      if (!include(field.type))
        return {};
  } else if (type.kind == K::Variant) {
    auto alts = alternatives(type, span, depth + 1);
    if (!alts)
      return {};
    for (const auto &alternative : *alts)
      for (const auto &field : alternative.fields)
        if (!include(field.type))
          return {};
  } else {
    fail("source.type", "static term has no runtime permissions", span);
    return {};
  }
  if (auto *decl = typeDeclaration(type)) {
    if (decl->resource) {
      if (*decl->resource == Resource::Affine && !result.drop &&
          decl->roles.empty()) {
        fail("source.permission", "affine fields must permit Drop", decl->span);
        return {};
      }
      result.copy = false;
      result.drop = result.drop && *decl->resource == Resource::Affine;
    }
  }
  return result;
}
bool Semantics::executableType(const Type &type, Span span, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic ? false
                      : fail("source.limit", "executable type depth", span);
  using K = Type::Kind;
  if (isLogicalValue(type))
    return fail("source.oracle-boundary",
                "logical oracle handles require semantic realization", span);
  if (type.kind == K::Formal)
    return fail("source.formal",
                "formal values cannot cross an executable boundary", span);
  if (type.kind == K::Array || type.kind == K::Tuple ||
      type.kind == K::Builtin) {
    for (const auto &child : type.arguments)
      if (!(type.kind == K::Builtin && isStaticOnly(child)) &&
          !executableType(child, span, depth + 1))
        return false;
  } else if (type.kind == K::Record || type.kind == K::Associated) {
    auto *decl = typeDeclaration(type);
    if (type.kind == K::Associated && decl && decl->abstract)
      return true;
    auto children = fields(type, span, depth + 1);
    if (!children)
      return false;
    for (const auto &child : *children)
      if (!executableType(child.type, span, depth + 1))
        return false;
  } else if (type.kind == K::Variant) {
    auto alts = alternatives(type, span, depth + 1);
    if (!alts)
      return false;
    for (const auto &alt : *alts)
      for (const auto &child : alt.fields)
        if (!executableType(child.type, span, depth + 1))
          return false;
  } else if (type.kind != K::Boolean && type.kind != K::Index &&
             type.kind != K::Field && type.kind != K::Group &&
             type.kind != K::Unit && type.kind != K::Parameter &&
             type.kind != K::OracleProjection)
    return fail("source.type", "type has no executable representation", span);
  return true;
}
bool Semantics::mathematicalData(const Type &type, Span span,
                                 const Declaration *scope, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic ? false
                      : fail("source.limit", "mathematical type depth", span);
  // Copy is structural: one demand covers the complete value. The recursive
  // walk below independently checks mathematical vocabulary and representation.
  if (depth == 1 && !requireUsage(type, Usage::Copy, span, scope, "source.mode",
                                  "mathematical values require Copy"))
    return false;
  using K = Type::Kind;
  if (isLogicalValue(type))
    return fail("source.oracle-boundary",
                "logical oracle handles are outside ordinary Math", span);
  if (type.kind == K::Builtin) {
    auto policy = protocol::nativeTypeConstructorPolicy(type.domain);
    if (!policy || (!policy->total && type.domain != "sequence"))
      return fail("source.mode",
                  "native data is outside the mathematical vocabulary", span);
    for (const auto &arg : type.arguments)
      if (!isStaticOnly(arg) && !mathematicalData(arg, span, scope, depth + 1))
        return false;
  } else if (type.kind == K::Tuple || type.kind == K::Array) {
    for (const auto &arg : type.arguments)
      if (!mathematicalData(arg, span, scope, depth + 1))
        return false;
  } else if (type.kind == K::Record || type.kind == K::Associated) {
    if (type.kind == K::Associated && symbolic(type))
      return true;
    auto children = fields(type, span, depth + 1);
    if (!children)
      return false;
    for (const auto &child : *children)
      if (!mathematicalData(child.type, span, scope, depth + 1))
        return false;
  } else if (type.kind == K::Variant) {
    auto alts = alternatives(type, span, depth + 1);
    if (!alts)
      return false;
    for (const auto &alt : *alts)
      for (const auto &child : alt.fields)
        if (!mathematicalData(child.type, span, scope, depth + 1))
          return false;
  } else if (type.kind != K::Boolean && type.kind != K::Index &&
             type.kind != K::Field && type.kind != K::Group &&
             type.kind != K::Unit && type.kind != K::Parameter &&
             type.kind != K::OracleProjection && type.kind != K::Formal)
    return fail("source.mode", "type is outside mathematical data", span);
  return true;
}
bool Semantics::sharedData(const Type &type, Span span,
                           const Declaration *scope, unsigned depth) {
  if (depth > work.limits.typeDepth || !charge(1, span))
    return diagnostic ? false
                      : fail("source.limit", "shared data type depth", span);
  if (depth == 1 &&
      (!executableType(type, span) ||
       !requireUsage(type, Usage::Copy, span, scope, "source.permission",
                     "role assembly requires Copy")))
    return false;
  using K = Type::Kind;
  if (isLogicalValue(type))
    return fail("source.oracle-boundary",
                "logical protocol values are not ordinary shared data", span);
  auto include = [&](const Type &child) {
    return sharedData(child, span, scope, depth + 1);
  };
  if (type.kind == K::Builtin) {
    auto policy = protocol::nativeTypeConstructorPolicy(type.domain);
    if (!policy || !policy->total || !policy->shared)
      return fail("source.roles",
                  "role assembly requires ordinary total shared data", span);
    for (const auto &argument : type.arguments)
      if (!isStaticOnly(argument) && !include(argument))
        return false;
  } else if (type.kind == K::Tuple || type.kind == K::Array) {
    for (const auto &child : type.arguments)
      if (!include(child))
        return false;
  } else if (type.kind == K::Record || type.kind == K::Associated) {
    // Abstract associated data is checked again after module substitution.
    if (type.kind == K::Associated && symbolic(type))
      return true;
    auto fields = this->fields(type, span, depth + 1);
    if (!fields)
      return false;
    for (const auto &field : *fields)
      if (!include(field.type))
        return false;
  } else if (type.kind == K::Variant) {
    auto alternatives = this->alternatives(type, span, depth + 1);
    if (!alternatives)
      return false;
    for (const auto &alternative : *alternatives)
      for (const auto &field : alternative.fields)
        if (!include(field.type))
          return false;
  } else if (type.kind != K::Boolean && type.kind != K::Index &&
             type.kind != K::Field && type.kind != K::Group &&
             type.kind != K::Unit && type.kind != K::Parameter &&
             type.kind != K::OracleProjection)
    return fail("source.roles", "type is not ordinary shared data", span);
  return true;
}
bool Semantics::withinModule(DeclarationId context, DeclarationId owner) const {
  for (auto id = std::optional(context); id;
       id = declarations[id->index].parent)
    if (id->index == owner.index)
      return true;
  return false;
}
bool Semantics::constructorAllowed(const Declaration &context,
                                   const Type &type) const {
  auto *decl = typeDeclaration(type);
  return decl && (!decl->generated || decl->generated->constructible) &&
         (type.kind == Type::Kind::Record ||
          type.kind == Type::Kind::LogicalRecord ||
          type.kind == Type::Kind::Variant ||
          type.kind == Type::Kind::Associated) &&
         withinModule(context.module, decl->module);
}
std::shared_ptr<const std::vector<TypeField>>
Semantics::structuralFields(const Type &type, Span span) {
  if (!chargeType(type, span))
    return {};
  if (type.kind == Type::Kind::Array && !type.dimension.isClosed())
    return {};
  if (type.kind == Type::Kind::Associated) {
    const auto *decl = typeDeclaration(type);
    if (decl && decl->abstract)
      return {};
  }
  return fields(type, span);
}
std::optional<Type> Semantics::projectionType(const Type &type, StringRef name,
                                              Span span) {
  if (!chargeType(type, span))
    return {};
  if (type.kind == Type::Kind::Array) {
    unsigned index;
    if ((name.size() > 1 && name.front() == '0') ||
        name.getAsInteger(10, index)) {
      fail("source.index", "fixed arrays require a static numeric index", span);
      return {};
    }
    // Even a closed out-of-bounds access is a validity check, not an overload
    // selection rule. Body checking discharges it for the chosen signature.
    if (!chargeType(type.arguments.front(), span, /*complete=*/false))
      return {};
    return type.arguments.front();
  }
  auto product = structuralFields(type, span);
  if (!product)
    return {};
  auto found = llvm::find_if(
      *product, [&](const auto &field) { return field.name == name; });
  if (found == product->end()) {
    fail("source.field", "unknown field: " + name, span);
    return {};
  }
  if (!chargeType(found->type, span, /*complete=*/false))
    return {};
  return found->type;
}
std::optional<Type> Semantics::projectedType(const Declaration &decl,
                                             const Type &input,
                                             ArrayRef<unsigned> path,
                                             Span span) {
  if (!charge(path.size() + 1, span))
    return {};
  // Declared and generated record fields perform complete candidate preflight
  // themselves before expansion/cache use. Borrow directly into that consumer
  // rather than traversing the unchanged root twice in this same call.
  bool record = input.kind == Type::Kind::Record ||
                input.kind == Type::Kind::LogicalRecord;
  if ((path.empty() || !record) && !chargeType(input, span))
    return {};
  if (path.empty())
    return input;
  // Borrow intermediate Types. Recursive owners keep expanded record fields
  // alive until the final selected Type has been admitted and copied once.
  std::function<std::optional<Type>(const Type &, ArrayRef<unsigned>)> select =
      [&](const Type &type,
          ArrayRef<unsigned> remaining) -> std::optional<Type> {
    if (remaining.empty()) {
      if (!chargeType(type, span))
        return {};
      return type;
    }
    if (remaining.size() > work.limits.typeDepth || !charge(1, span)) {
      if (!diagnostic)
        fail("source.limit", "projection path depth exceeded", span);
      return {};
    }
    auto index = remaining.front();
    if (type.kind == Type::Kind::Array) {
      if (type.dimension.isClosed() && index >= type.dimension.closedValue()) {
        fail("source.index", "static array index is out of range", span);
        return {};
      }
      if (!type.dimension.isClosed()) {
        NaturalBound required{Natural::constant(uint64_t(index) + 1),
                              type.dimension, span};
        if (!assumptions(decl, required, {}, span))
          return {};
      }
      return select(type.arguments.front(), remaining.drop_front());
    }
    if (type.kind == Type::Kind::Tuple) {
      if (index >= type.arguments.size()) {
        fail("source.index", "product index is out of range", span);
        return {};
      }
      return select(type.arguments[index], remaining.drop_front());
    }
    auto fs = fields(type, span);
    if (!fs)
      return {};
    if (index >= fs->size()) {
      fail("source.index", "product index is out of range", span);
      return {};
    }
    return select((*fs)[index].type, remaining.drop_front());
  };
  return select(input, path);
}
std::optional<unsigned> Semantics::fieldIndex(const Declaration &decl,
                                              const Type &type, StringRef name,
                                              Span span,
                                              bool specificationRead) {
  auto *nominal = typeDeclaration(type);
  if (type.kind == Type::Kind::Associated ||
      type.kind == Type::Kind::Parameter ||
      (nominal && nominal->sealed &&
       !(specificationRead && type.kind == Type::Kind::Record &&
         constructorAllowed(decl, type)))) {
    fail("source.private",
         "restricted values require their module's unpack or consume operation",
         span);
    return {};
  }
  unsigned index;
  if (type.kind == Type::Kind::Array) {
    if ((name.size() > 1 && name.front() == '0') ||
        name.getAsInteger(10, index)) {
      fail("source.index", "fixed arrays require a static numeric index", span);
      return {};
    }
    return index;
  }
  auto product = fields(type, span);
  if (!product)
    return {};
  auto found = llvm::find_if(
      *product, [&](const auto &field) { return field.name == name; });
  if (found == product->end()) {
    fail("source.field", "unknown field: " + name, span);
    return {};
  }
  if (!found->isPublic && !constructorAllowed(decl, type)) {
    fail("source.private", "private record field", span);
    return {};
  }
  return unsigned(found - product->begin());
}
} // namespace zkc::language::detail
