#include "Arguments.h"
#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>
#include <limits>
using namespace llvm;
namespace zkc::language::detail {
std::optional<std::vector<bool>>
Checker::enclosingParameters(const Declaration &context,
                             const Declaration &target, Span span) {
  if (!types.charge(context.parameters.size() + target.parameters.size() + 1,
                    span))
    return {};
  std::set<std::string> available;
  for (const auto &parameter : context.parameters)
    available.insert(parameter.atom);
  std::vector<bool> result;
  for (const auto &parameter : target.parameters)
    result.push_back(available.count(parameter.atom));
  return result;
}
std::optional<std::vector<Type>>
Checker::arguments(const Declaration &context, const Declaration &target,
                   ArrayRef<SyntaxType> syntax, Span span,
                   ArrayRef<ArgumentLabel> labels) {
  std::vector<Type> result(target.parameters.size());
  auto enclosing = enclosingParameters(context, target, span);
  if (!enclosing)
    return {};
  auto binding =
      bindArguments(types, argumentNames<Parameter>(target.parameters),
                    syntax.size(), labels, false, span, "source.generic");
  if (!binding)
    return {};
  std::vector<bool> written(target.parameters.size());
  for (unsigned i = 0; i < syntax.size(); ++i) {
    auto arg = type(context, syntax[i]);
    if (!arg)
      return {};
    result[(*binding)[i]] = std::move(*arg);
    written[(*binding)[i]] = true;
  }
  for (unsigned i = 0; i < target.parameters.size(); ++i) {
    if (written[i])
      continue;
    if (!(*enclosing)[i]) {
      types.fail("source.generic",
                 "missing static argument: " + target.parameters[i].name, span);
      return {};
    }
    result[i] = parameterType(target.parameters[i]);
  }
  if (formingParameters.count(context.id.index)) {
    for (const auto &argument : result)
      if (!types.chargeType(argument, span))
        return {};
    deferredApplications[context.id.index].push_back({target.id, result, span});
    return result;
  }
  if (!types.checkArguments(target, result, span, &context))
    return {};
  auto bindings = types.substitution(target, result);
  for (const auto &bound : target.bounds)
    if (!types.assumptions(context, bound, bindings, span))
      return {};
  return result;
}

std::optional<Type>
Checker::associated(const Declaration &context, const Type &base,
                    StringRef path, Span span,
                    std::optional<ResolvedReference> reference) {
  Type current = base;
  unsigned depth = 0;
  std::string written;
  while (!path.empty()) {
    if (++depth > work.limits.typeDepth) {
      types.fail("source.limit", "associated reference depth", span);
      return {};
    }
    auto [name, tail] = path.split("::");
    written += (written.empty() ? "" : "::") + name.str();
    if (current.kind == Type::Kind::Module) {
      const Declaration *owner = nullptr;
      uint32_t slot = UINT32_MAX;
      auto binderOwner = context.id;
      if (current.symbolic) {
        if (auto *parameter = types.parameter(current.domain);
            parameter && parameter->interface) {
          owner = &output.declarations[parameter->interface->index];
          auto selected = moduleParameterReferences.find(parameter->atom);
          if (selected != moduleParameterReferences.end()) {
            reference = selected->second.reference;
            binderOwner = selected->second.owner;
            slot = selected->second.slot;
          }
        } else if (StringRef(current.domain).starts_with("self:")) {
          if (auto id =
                  index().canonical(StringRef(current.domain).drop_front(5)))
            owner = &output.declarations[id->index];
        }
      } else
        owner = types.typeDeclaration(current);
      if (!owner) {
        types.fail("source.type", "unknown associated module", span);
        return {};
      }
      auto result = index().member(accessFor(context), owner->id, name,
                                   {[&] { return types.charge(1, span); }, {}});
      auto *member = std::get_if<ResolvedReference>(&result);
      if (!member) {
        acceptFailure(std::get<LookupFailure>(result), span, true);
        return {};
      }
      if (!reference)
        reference = *member;
      else {
        reference->target = member->target;
        reference->category = member->category;
        reference->path.insert(reference->path.end(), member->path.begin(),
                               member->path.end());
      }
      reference->abstract =
          AbstractMemberContext{current, owner->id, binderOwner, slot};
      if (!recordReference(context, ReferenceRoute::ModuleMember, *reference,
                           written, span))
        return {};
    }
    auto next = types.associated(current, name, span);
    if (!next)
      return {};
    current = std::move(*next);
    path = tail;
  }
  return current;
}

std::optional<Type> Checker::type(const Declaration &context,
                                  const SyntaxType &s, unsigned depth,
                                  bool allowPlacement) {
  SaveAndRestore site(referenceSite, s.referenceSite);
  auto elaborated = elaborateType(context, s, depth, allowPlacement);
  auto result = std::move(elaborated.value);
  if (result && !elaborated.complete && !types.chargeType(*result, s.span))
    return {};
  if (result && result->kind == Type::Kind::LogicalRecord &&
      !types.logicalRecord(*result, s.span))
    return {};
  return result;
}
Checker::ElaboratedType Checker::elaborateType(const Declaration &context,
                                               const SyntaxType &s,
                                               unsigned depth,
                                               bool allowPlacement) {
  if (depth > work.limits.typeDepth || !types.charge(1, s.span)) {
    if (!types.diagnostic)
      types.fail("source.limit", "source type complexity limit exceeded",
                 s.span);
    return {};
  }
  using S = SyntaxType::Kind;
  using K = Type::Kind;
  if (!allowPlacement && (s.roles || s.components)) {
    types.fail("source.oracle-aggregate",
               "placed values are not ordinary static type arguments", s.span);
    return {};
  }
  if (s.kind == S::Hole) {
    types.fail("source.inference",
               "a static hole is allowed only as a whole call argument",
               s.span);
    return {};
  }
  if (s.kind == S::Builtin || s.kind == S::Formal) {
    std::vector<Type> arguments;
    for (const auto &syntax : s.arguments) {
      auto argument = type(context, syntax, depth + 1);
      if (!argument)
        return {};
      arguments.push_back(std::move(*argument));
    }
    auto result = s.kind == S::Formal ? formalType(s.name, arguments)
                                      : builtinType(s.name, arguments);
    if (!result) {
      types.fail(s.kind == S::Formal ? "source.formal" : "source.builtin",
                 toString(result.takeError()), s.span);
      return {};
    }
    if (result->kind == K::OracleKind &&
        !types.oracleKind(*result, s.span, &context))
      return {};
    if (s.kind == S::Builtin && s.name == "sequence" &&
        (!types.requireUsage(arguments.front(), Usage::Copy, s.span, &context,
                             "source.sequence",
                             "sequence elements require Copy") ||
         !types.executableType(arguments.front(), s.span)))
      return {};
    return std::move(*result);
  }
  if (s.kind == S::Natural) {
    uint64_t value;
    if (StringRef(s.name).getAsInteger(10, value)) {
      types.fail("source.natural", "natural literal overflows uint64", s.span);
      return {};
    }
    Type result(K::Natural);
    result.dimension = Natural::constant(value);
    return result;
  }
  if (s.kind == S::PowerOfTwo) {
    auto exponent = type(context, s.arguments[0], depth + 1);
    if (!exponent)
      return {};
    if (exponent->kind != K::Natural) {
      types.fail("source.natural", "pow2 requires a natural exponent", s.span);
      return {};
    }
    auto value = types.naturals.powerOfTwo(exponent->dimension);
    if (!value) {
      types.accept(value.takeError(), s.span);
      return {};
    }
    Type result(K::Natural);
    result.dimension = std::move(*value);
    result.symbolic = !result.dimension.isClosed();
    return result;
  }
  if (s.kind == S::Add || s.kind == S::Multiply) {
    auto a = type(context, s.arguments[0], depth + 1),
         b = type(context, s.arguments[1], depth + 1);
    if (!a || !b)
      return {};
    if (a->kind != K::Natural || b->kind != K::Natural) {
      types.fail("source.natural", "static arithmetic requires naturals",
                 s.span);
      return {};
    }
    auto n = s.kind == S::Add
                 ? types.naturals.add(a->dimension, b->dimension)
                 : types.naturals.multiply(a->dimension, b->dimension);
    if (!n) {
      types.accept(n.takeError(), s.span);
      return {};
    }
    Type result(K::Natural);
    result.dimension = std::move(*n);
    result.symbolic = !result.dimension.isClosed();
    return result;
  }
  if (s.kind == S::Array) {
    auto element = type(context, s.arguments[0], depth + 1, allowPlacement);
    auto count = type(context, s.arguments[1], depth + 1);
    if (!element || !count)
      return {};
    if (!valueType(*element) || count->kind != K::Natural) {
      types.fail("source.type",
                 "array requires an element type and natural length", s.span);
      return {};
    }
    if (count->dimension.isClosed() &&
        count->dimension.closedValue() > work.limits.aggregateLeaves) {
      types.fail("source.limit", "fixed array length exceeds aggregate bound",
                 s.span);
      return {};
    }
    if (isLogicalValue(*element) &&
        !(element->kind == K::LogicalRecord &&
          !types.typeDeclaration(*element)->roles.empty()) &&
        element->kind != K::Tuple && element->kind != K::Array &&
        !(isOracleHandle(*element) && s.arguments[0].oracleHolder)) {
      types.fail("source.oracle-aggregate",
                 "logical oracle handles require their bounded sequence",
                 s.span);
      return {};
    }
    Type result(K::Array);
    result.arguments.push_back(std::move(*element));
    result.dimension = std::move(count->dimension);
    return result;
  }
  if (s.kind == S::Tuple) {
    Type result(s.arguments.empty() ? K::Unit : K::Tuple);
    for (auto &child : s.arguments) {
      auto t = type(context, child, depth + 1, allowPlacement);
      if (!t)
        return {};
      if (!valueType(*t)) {
        types.fail("source.type", "static term in tuple type", s.span);
        return {};
      }
      if (isLogicalValue(*t) &&
          !(t->kind == K::LogicalRecord &&
            !types.typeDeclaration(*t)->roles.empty()) &&
          t->kind != K::Tuple && t->kind != K::Array &&
          !(isOracleHandle(*t) && child.oracleHolder)) {
        types.fail("source.oracle-aggregate",
                   "logical oracle handles require separate protocol ports",
                   s.span);
        return {};
      }
      result.arguments.push_back(std::move(*t));
    }
    return result;
  }
  if (!StringRef(s.name).starts_with("::")) {
    if (!types.charge(context.parameters.size(), s.span))
      return {};
    auto [head, tail] = StringRef(s.name).split("::");
    for (const auto &parameter : context.parameters)
      if (parameter.name == head) {
        if (!s.arguments.empty()) {
          types.fail("source.generic",
                     "a selected static binder cannot take static arguments",
                     s.span);
          return {};
        }
        if (tail.empty())
          return parameterType(parameter);
        return associated(context, parameterType(parameter), tail, s.span);
      }
  }
  if (s.arguments.empty()) {
    if (s.name == "bool")
      return Type{};
    if (s.name == "index")
      return Type(K::Index);
  }
  auto selection =
      index().lookup(accessFor(context), s.name, lookupTraversal(s.span));
  auto *selected = std::get_if<ResolvedReference>(&selection);
  if (!selected &&
      std::get<LookupFailure>(selection).kind != LookupFailureKind::NotFound) {
    acceptFailure(std::get<LookupFailure>(selection), s.span, true);
    return {};
  }
  if (!selected && s.arguments.empty()) {
    // A complete declaration route wins before considering projections. In
    // particular, an exact external qualified root must not be reclassified
    // through an ambiguous short-name probe of its prefix.
    // Module qualification and catalog projections share path syntax; only an
    // absent declaration tail may be elaborated as a projection.
    StringRef prefix = s.name;
    while (prefix.contains("::")) {
      prefix = prefix.rsplit("::").first;
      // A kept prefix is resolved again, and recorded, as its own type below.
      auto id = probe(context, prefix, s.span, nullptr);
      if (!id) {
        if (types.diagnostic)
          return {};
        continue;
      }
      const auto &decl = output.declarations[id->index];
      if (decl.kind != Declaration::Kind::Domain &&
          decl.kind != Declaration::Kind::Associated &&
          decl.kind != Declaration::Kind::Alias)
        continue;
      SyntaxType syntax;
      syntax.referenceSite = s.referenceSite;
      syntax.name = prefix.str();
      syntax.span = s.span;
      auto base = type(context, syntax, depth + 1);
      if (!base)
        return {};
      return associated(context, *base,
                        StringRef(s.name).drop_front(prefix.size() + 2), s.span,
                        typeReferences.count(s.referenceSite)
                            ? std::optional(typeReferences.at(s.referenceSite))
                            : std::nullopt);
    }
  }
  if (!selected) {
    acceptFailure(std::get<LookupFailure>(selection), s.span, true);
    return {};
  }
  auto reference = std::optional(*selected);
  auto id = std::optional(reference->target);
  if (!signature(*id, depth + 1))
    return {};
  if (auto *row = index().association(*id);
      row && row->rule == protocol::FrontendSignature::RandomConstructor) {
    types.fail("source.service",
               "managed constructor requires a protocol service port", s.span);
    return {};
  }
  auto &decl = output.declarations[id->index];
  if (decl.kind == Declaration::Kind::Associated) {
    auto &parent = output.declarations[decl.parent->index];
    Type base(K::Module, parent.kind == Declaration::Kind::Interface
                             ? "self:" + parent.qualifiedName
                             : parent.qualifiedName);
    base.symbolic = parent.kind == Declaration::Kind::Interface;
    if (!s.arguments.empty()) {
      if (base.symbolic) {
        types.fail("source.generic", "interface type requires a bound module",
                   s.span);
        return {};
      }
      auto args = arguments(context, parent, s.arguments, s.span, s.labels);
      if (!args)
        return {};
      base.arguments = std::move(*args);
    } else {
      if (base.symbolic &&
          (!context.parent || context.parent->index != parent.id.index)) {
        types.fail("source.generic", "interface type requires a bound module",
                   s.span);
        return {};
      }
      auto enclosing = enclosingParameters(context, parent, s.span);
      if (!enclosing)
        return {};
      if (!llvm::all_of(*enclosing, [](bool available) { return available; })) {
        types.fail("source.generic",
                   "associated type needs its module's static arguments",
                   s.span);
        return {};
      }
      for (const auto &parameter : parent.parameters)
        base.arguments.push_back(parameterType(parameter));
    }
    reference->abstract =
        AbstractMemberContext{base, parent.id, context.id, UINT32_MAX};
    if (!recordReference(context, ReferenceRoute::Path, *reference, s.name,
                         s.span))
      return {};
    typeReferences.insert_or_assign(s.referenceSite, *reference);
    return types.associated(base, decl.id, s.span);
  }
  if (!recordReference(context, ReferenceRoute::Path, *reference, s.name,
                       s.span))
    return {};
  typeReferences.insert_or_assign(s.referenceSite, *reference);
  auto args = arguments(context, decl, s.arguments, s.span, s.labels);
  if (!args)
    return {};
  if (decl.kind == Declaration::Kind::Domain)
    return decl.domain;
  if (decl.kind == Declaration::Kind::Alias) {
    // Admit the alias category before its placed target becomes an ordinary
    // Type. Structural children inherit the same category requirement.
    if (!allowPlacement && decl.placement) {
      types.fail("source.oracle-aggregate",
                 "a placed alias is not an ordinary data type", s.span);
      return {};
    }
    return ElaboratedType(
        types.substitute(decl.domain, types.substitution(decl, *args), s.span),
        /*complete=*/true);
  }
  Type result;
  if (decl.kind == Declaration::Kind::Record)
    result.kind = decl.logical ? K::LogicalRecord : K::Record;
  else if (decl.kind == Declaration::Kind::Variant)
    result.kind = K::Variant;
  else if (decl.kind == Declaration::Kind::Module ||
           decl.kind == Declaration::Kind::Interface)
    result.kind = K::Module;
  else {
    types.fail("source.type", "expected a type, domain, or static module",
               s.span);
    return {};
  }
  result.domain = decl.qualifiedName;
  result.arguments = std::move(*args);
  return result;
}

} // namespace zkc::language::detail
