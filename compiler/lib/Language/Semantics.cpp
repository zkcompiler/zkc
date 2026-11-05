#include "Semantics.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/ScopeExit.h"
using namespace llvm;
namespace zkc::language::detail {
Semantics::Semantics(const std::vector<Declaration> &declarations,
                     ArrayRef<Asset> assets, Work &work,
                     std::function<bool(DeclarationId)> complete)
    : work(work),
      naturals(work.limits.work, work.limits.naturalTerms,
               work.limits.naturalFactors,
               [&work](uint64_t amount) { return work.charge(amount); }),
      declarations(declarations), assets(assets), ownedIndex(std::in_place),
      index(*ownedIndex), complete(std::move(complete)) {
  for (const auto &decl : declarations) {
    indexDeclaration(decl);
    for (unsigned i = 0; i < decl.parameters.size(); ++i)
      indexParameter(decl.parameters[i], decl.id, i);
  }
}
Semantics::Semantics(const Semantics &owner, Work &work)
    : work(work),
      naturals(work.limits.work, work.limits.naturalTerms,
               work.limits.naturalFactors,
               [&work](uint64_t amount) { return work.charge(amount); }),
      authorities(owner.authorities), declarations(owner.declarations),
      index(owner.index) {}
Expected<std::optional<std::string>>
Semantics::nominalAuthority(StringRef path) const {
  if (authorities.final)
    return definingAuthority(*authorities.final, path);
  auto found = index.qualified.find(path.str());
  if (found == index.qualified.end())
    return failure("source.authority",
                   "no checked declaration has path " + path);
  if (declarations[found->second.index].generated)
    return std::optional<std::string>{};
  return std::optional<std::string>(std::string(64, '-'));
}
void Semantics::indexDeclaration(const Declaration &decl) {
  assert(ownedIndex && "only the semantic index owner can add declarations");
  if (!decl.origin && !decl.anonymous)
    ownedIndex->qualified.emplace(decl.qualifiedName, decl.id);
}
void Semantics::indexParameter(const Parameter &parameter, DeclarationId id,
                               unsigned index) {
  assert(ownedIndex && "only the semantic index owner can add parameters");
  ownedIndex->parameters.emplace(parameter.atom, std::make_pair(id, index));
}
// Private memo routing only. Collisions always compare the complete owned
// Type; this hash is never an identity or source/native admission witness.
size_t typeLookupHash(const Type &type) {
  hash_code dimension = hash_value(type.dimension.terms().size());
  for (const auto &[factors, coefficient] : type.dimension.terms()) {
    dimension = hash_combine(dimension, coefficient, factors.size());
    for (const auto &factor : factors)
      dimension = hash_combine(dimension, unsigned(factor.kind), factor.name,
                               factor.member);
  }
  if (type.kind == Type::Kind::Natural)
    return hash_combine(unsigned(type.kind), dimension);
  auto result = hash_combine(
      unsigned(type.kind), type.domain, type.sort, dimension, type.symbolic,
      type.arguments.size(),
      type.kind == Type::Kind::Descriptor ? unsigned(type.family) : 0);
  for (const auto &child : type.arguments)
    result = hash_combine(result, typeLookupHash(child));
  return result;
}

Type typeHead(const Type &type, bool includeDimension) {
  Type result(type.kind, type.domain);
  result.family = type.family;
  result.sort = type.sort;
  if (includeDimension)
    result.dimension = type.dimension;
  result.symbolic = type.symbolic;
  result.assumptions = type.assumptions;
  return result;
}
Type parameterType(const Parameter &p) {
  using K = Type::Kind;
  Type value =
      p.sort == Parameter::Sort::Domain ? domainType(p.domainSort, p.atom)
      : p.sort == Parameter::Sort::Asset
          ? assetType(p.domainSort, p.atom)
          : Type(p.sort == Parameter::Sort::Natural      ? K::Natural
                 : p.sort == Parameter::Sort::Module     ? K::Module
                 : p.sort == Parameter::Sort::OracleKind ? K::OracleKind
                                                         : K::Parameter,
                 p.atom);
  value.symbolic = true;
  value.assumptions = p.permissions;
  if (p.sort == Parameter::Sort::Natural)
    value.dimension = cantFail(Natural::atom(p.atom));
  if (p.sort == Parameter::Sort::Module)
    value.arguments = p.arguments;
  return value;
}

bool Semantics::fail(StringRef code, const Twine &message, Span span,
                     std::vector<Span> related) {
  if (!diagnostic)
    diagnostic =
        Diagnostic{code.str(), message.str(), span, std::move(related)};
  return false;
}
bool Semantics::accept(Error error, std::optional<Span> fallback) {
  auto found =
      diagnose(work.contextualize(std::move(error), fallback), fallback);
  if (!found)
    return true;
  if (!diagnostic)
    diagnostic = std::move(found);
  return false;
}
bool Semantics::charge(uint64_t count, Span span) {
  return accept(work.charge(count, span));
}
Error Semantics::takeError() {
  assert(diagnostic && "failed semantic query must carry a diagnostic");
  auto result = make_error<DiagnosticError>(std::move(*diagnostic));
  diagnostic.reset();
  return result;
}
bool valueType(const Type &type) { return !isStaticOnly(type); }
bool Semantics::protocolValue(const Type &type, Span span) {
  if (type.kind == Type::Kind::LogicalRecord)
    return logicalRecord(type, span);
  if ((type.kind == Type::Kind::Array || type.kind == Type::Kind::Tuple) &&
      isLogicalValue(type)) {
    for (const auto &child : type.arguments) {
      const auto *nominal = typeDeclaration(child);
      if (child.kind == Type::Kind::LogicalRecord && nominal &&
          nominal->roles.empty())
        return fail("source.oracle-boundary",
                    "legacy logical families require separate ports", span);
      if (!protocolValue(child, span))
        return false;
    }
    return true;
  }
  return isOracleHandle(type) || executableType(type, span);
}
bool Semantics::oraclePort(const Port &port) {
  if (port.placement) {
    unsigned participants = 0;
    for (auto role : placementRoles(*port.placement))
      participants = std::max(participants, role + 1);
    auto rebuilt =
        placement(port.type, *port.placement, participants, port.span);
    if (!rebuilt)
      return false;
    if (*rebuilt != *port.placement || placementRoles(*rebuilt) != port.roles)
      return fail("source.placement",
                  "port placement disagrees with its schema", port.span);
    if (const auto *oracle =
            std::get_if<OraclePlacement>(&port.placement->value))
      if (!port.oracle || port.oracle->holder != oracle->holder)
        return fail("source.placement",
                    "direct oracle holder metadata disagrees", port.span);
    if (std::holds_alternative<ProductPlacement>(port.placement->value))
      return !port.oracle ||
             fail("source.placement", "product has no aggregate oracle holder",
                  port.span);
  }
  const auto *nominal = typeDeclaration(port.type);
  if (!port.placement && port.type.kind == Type::Kind::LogicalRecord &&
      nominal && !nominal->roles.empty())
    return fail("source.placement",
                "distributed port requires its field placement tree",
                port.span);
  if (isLogicalValue(port.type) != port.oracle.has_value())
    return fail("source.oracle-port",
                "oracle ports require an explicit holder and receiver arrow",
                port.span);
  if (!port.oracle)
    return true;
  if (port.roles.size() < 2 ||
      !llvm::is_contained(port.roles, port.oracle->holder))
    return fail("source.oracle-port", "invalid oracle port role family",
                port.span);
  if (port.type.kind == Type::Kind::LogicalRecord) {
    if (port.oracle->maximumRows)
      return fail("source.oracle-shape",
                  "logical record row bounds belong to direct fields",
                  port.span);
    return logicalRecord(port.type, port.span);
  }
  unsigned arity = port.type.kind == Type::Kind::OracleSequence ? 2 : 1;
  if (port.type.arguments.size() != arity)
    return fail("source.oracle-port", "invalid oracle port type", port.span);
  if (port.oracle->maximumRows &&
      port.oracle->maximumRows->kind != Type::Kind::Natural)
    return fail("source.oracle-shape",
                "oracle maximum must be a static natural", port.span);
  const auto &kind = port.type.arguments.front();
  if (!kind.arguments.empty() &&
      ((kind.arguments.size() == 2) == port.oracle->maximumRows.has_value()))
    return fail("source.oracle-shape",
                "only an unsized oracle port requires an explicit maximum",
                port.span);
  return true;
}
bool Semantics::chargeConstruction(const ConstructionDefinition &value,
                                   Span span) {
  if (!charge(value.suite.size() + value.rules.size() +
                  value.applications.size() + 1,
              span))
    return false;
  for (const auto *type : {&value.provider, &value.state})
    if (*type && !chargeType(**type, span))
      return false;
  if (value.initializer && value.initializer->module &&
      !chargeType(*value.initializer->module, span))
    return false;
  for (const auto *arguments : {&value.arguments, &value.initializerArguments})
    for (const auto &argument : *arguments)
      if (!chargeType(argument, span))
        return false;
  if (value.codec) {
    const auto &codec = *value.codec;
    if (!chargeType(codec.provider, span) || !chargeType(codec.record, span) ||
        !charge(codec.inputs.size() + 1, span))
      return false;
    for (const auto *method :
         {&codec.initialize, &codec.write, &codec.finish}) {
      if (method->target.module && !chargeType(*method->target.module, span))
        return false;
      for (const auto &argument : method->arguments)
        if (!chargeType(argument, span))
          return false;
    }
  }
  for (const auto &application : value.applications) {
    for (const auto &part : application.path)
      if (!charge(part.size() + 1, application.span))
        return false;
    for (const auto &argument : application.arguments)
      if (!chargeType(argument, application.span))
        return false;
  }
  for (const auto &rule : value.rules) {
    if (!charge(rule.inputs.size() + 1, rule.span))
      return false;
    for (const auto &part : rule.path)
      if (!charge(part.size() + 1, rule.span))
        return false;
    for (const auto &argument : rule.arguments)
      if (!chargeType(argument, rule.span))
        return false;
    for (const auto *type : {&rule.payload, &rule.chunks})
      if (*type && !chargeType(**type, rule.span))
        return false;
  }
  return true;
}
bool Semantics::chargeType(const Type &type, Span span, bool complete) {
  auto cost =
      typeComplexity(type, work.limits.typeNodes, work.limits.typeDepth,
                     work.remaining(), nullptr, complete, TypeWork::Copy);
  if (!cost)
    return accept(cost.takeError(), span);
  return charge(*cost, span);
}
bool Semantics::chargeIdentity(const Type &type, Span span) {
  auto cost =
      typeComplexity(type, work.limits.typeNodes, work.limits.typeDepth,
                     work.remaining(), nullptr, true, TypeWork::Identity);
  if (!cost)
    return accept(cost.takeError(), span);
  return charge(*cost, span);
}
std::optional<bool> Semantics::sameSnapshot(const Type &type,
                                            const Type &expected, Span span,
                                            bool complete) {
  TypeComparison comparison{expected};
  auto cost = typeComplexity(type, work.limits.typeNodes, work.limits.typeDepth,
                             work.remaining(), nullptr, complete,
                             TypeWork::Copy, &comparison);
  if (!cost) {
    accept(cost.takeError(), span);
    return {};
  }
  if (!charge(*cost, span))
    return {};
  return comparison.equal;
}
const Parameter *Semantics::parameter(StringRef atom) const {
  auto found = index.parameters.find(atom.str());
  if (found == index.parameters.end())
    return nullptr;
  auto [id, index] = found->second;
  return &declarations[id.index].parameters[index];
}
const Declaration *Semantics::typeDeclaration(const Type &type) const {
  using K = Type::Kind;
  if (type.kind != K::Record && type.kind != K::LogicalRecord &&
      type.kind != K::Variant && type.kind != K::Associated &&
      type.kind != K::Module)
    return nullptr;
  auto found = index.qualified.find(type.domain);
  return found == index.qualified.end() ? nullptr
                                        : &declarations[found->second.index];
}
bool Semantics::symbolic(const Type &type) const {
  return type.kind == Type::Kind::Parameter || type.symbolic ||
         !type.dimension.isClosed() ||
         llvm::any_of(type.arguments, [&](auto &t) { return symbolic(t); });
}
Substitution Semantics::substitution(const Declaration &decl,
                                     ArrayRef<Type> args) const {
  Substitution out;
  for (unsigned i = 0; i < args.size() && i < decl.parameters.size(); ++i)
    out.emplace(decl.parameters[i].atom, args[i]);
  return out;
}
std::optional<Type> Semantics::substitute(const Type &input,
                                          const Substitution &bindings,
                                          Span span, unsigned depth) {
  if (normalizationDepth >= work.limits.typeDepth) {
    fail("source.limit", "type normalization depth limit", span);
    return {};
  }
  ++normalizationDepth;
  auto restoreDepth = llvm::scope_exit([&] { --normalizationDepth; });

  if (depth > work.limits.typeDepth || !charge(1, span)) {
    if (!diagnostic)
      fail("source.limit", "type substitution depth limit", span);
    return {};
  }
  bool resultNeedsPreflight = true;
  if (depth == 1 || normalizationDepth == 1) {
    // Bound the selected tree as a whole before any recursive result copy.
    // Each binding is an ordinary static term, not a descriptor-kind variable.
    bool normalizationNeeded = false, bindingSelected = false;
    bool reductionNeeded = false;
    auto cost = typeComplexity(
        input, work.limits.typeNodes, work.limits.typeDepth - depth + 1,
        work.remaining(),
        [&](const Type &term) -> const Type * {
          // Replaced heads return the selected term directly; they perform no
          // normalization or formation of the unreplaced pattern.
          if (term.symbolic) {
            auto found = bindings.find(term.domain);
            if (found != bindings.end()) {
              bindingSelected = true;
              return &found->second;
            }
          }
          reductionNeeded |= (term.kind == Type::Kind::OracleProjection &&
                              term.arguments.size() == 1) ||
                             ((term.kind == Type::Kind::Associated ||
                               !domainSort(term).empty()) &&
                              !term.arguments.empty());
          normalizationNeeded |=
              (!bindings.empty() && !term.dimension.isClosed()) ||
              term.kind == Type::Kind::OracleKind ||
              term.kind == Type::Kind::LogicalRecord ||
              (term.kind == Type::Kind::OracleProjection &&
               term.arguments.size() == 1) ||
              ((term.kind == Type::Kind::Associated ||
                !domainSort(term).empty()) &&
               !term.arguments.empty());
          return nullptr;
        },
        true, TypeWork::Copy);
    if (!cost) {
      accept(cost.takeError(), span);
      return {};
    }
    if (!charge(*cost, span))
      return {};
    // The preflight inspected every head and found no substitution, natural
    // normalization, projection or logical formation to perform. Preserve the
    // validated tree with one copy, rather than rebuilding and revalidating it.
    if (!normalizationNeeded && !bindingSelected)
      return input;
    // Selection and Natural arithmetic preserve every stored Type kind, child
    // count and level. Preflight checked their selected parent categories;
    // NaturalArithmetic admits every new polynomial allocation on this ledger
    // and the Natural branch restores canonical head metadata. Only projection
    // reduction can change the stored tree and require a fresh whole check.
    resultNeedsPreflight = reductionNeeded;
  }
  if (isDescriptor(input) && input.symbolic) {
    fail("source.descriptor", "descriptor contracts have no symbolic head",
         span);
    return {};
  }
  if (input.symbolic) {
    auto found = bindings.find(input.domain);
    if (found != bindings.end()) {
      // The owning selected-tree preflight already debited this exact copy,
      // including its complete metadata and its actual insertion depth.
      return found->second;
    }
  }
  // The whole selected-tree debit above pays for these shallow heads and
  // their child vectors. Never copy a subtree only to overwrite its children.
  Type result = typeHead(input);
  result.arguments.reserve(input.arguments.size());
  for (const auto &arg : input.arguments) {
    auto t = substitute(arg, bindings, span, depth + 1);
    if (!t)
      return {};
    result.arguments.push_back(std::move(*t));
  }
  // Natural owns a canonical polynomial. With no bindings there is no
  // arithmetic to perform or polynomial to materialize again.
  if (!bindings.empty() && !result.dimension.isClosed()) {
    // A projection of a bound asset atom is decided here, from the captured
    // asset or by renaming, before the polynomial is normalized.
    std::map<std::pair<std::string, std::string>, Natural> projections;
    bool bindingRelevant = false;
    for (const auto &[factors, coefficient] : result.dimension.terms()) {
      (void)coefficient;
      if (!charge(factors.size() + 1, span))
        return {};
      for (const auto &factor : factors) {
        auto found = bindings.find(factor.name);
        if (factor.kind != Natural::Factor::Kind::Projection) {
          bindingRelevant |= found != bindings.end() &&
                             found->second.kind == Type::Kind::Natural;
          continue;
        }
        if (found == bindings.end())
          continue;
        bindingRelevant = true;
        auto key = std::make_pair(factor.name, factor.member);
        if (projections.count(key))
          continue;
        auto value = assetProjection(found->second, factor.member, span);
        if (!value)
          return {};
        projections.emplace(std::move(key), std::move(value->dimension));
      }
    }
    if (bindingRelevant) {
      auto n = naturals.substitute(
          result.dimension,
          [&](const Natural::Factor &factor) -> const Natural * {
            if (factor.kind == Natural::Factor::Kind::Projection) {
              auto found =
                  projections.find(std::make_pair(factor.name, factor.member));
              return found == projections.end() ? nullptr : &found->second;
            }
            auto found = bindings.find(factor.name);
            return found != bindings.end() &&
                           found->second.kind == Type::Kind::Natural
                       ? &found->second.dimension
                       : nullptr;
          });
      if (!n) {
        accept(n.takeError(), span);
        return {};
      }
      result.dimension = std::move(*n);
    }
    if (result.kind == Type::Kind::Natural) {
      result.symbolic = !result.dimension.isClosed();
      if (!result.symbolic)
        result.domain.clear();
    }
  }
  if (result.kind == Type::Kind::OracleKind && !symbolic(result) &&
      !oracleKind(result, span))
    return {};
  if (result.kind == Type::Kind::OracleProjection &&
      result.arguments.size() == 1)
    return associated(result.arguments.front(), result.domain, span);
  if ((result.kind == Type::Kind::Associated || !domainSort(result).empty()) &&
      !result.arguments.empty()) {
    // Installed domain associations (for example G::Scalar) have catalog
    // member names, rather than source declaration IDs.
    if (result.arguments.front().kind != Type::Kind::Module)
      return associated(result.arguments.front(),
                        StringRef(result.domain).rsplit("::").second, span);
    auto found = index.qualified.find(result.domain);
    if (found == index.qualified.end()) {
      fail("source.type", "unknown associated declaration", span);
      return {};
    }
    return associated(result.arguments.front(), found->second, span);
  }
  // Substitution must not introduce a logical value into an ordinary product,
  // even when an array has no elements in its eventual native layout.
  if (result.kind == Type::Kind::Array || result.kind == Type::Kind::Tuple ||
      result.kind == Type::Kind::Builtin)
    for (const auto &argument : result.arguments)
      if (isLogicalValue(argument) &&
          (result.kind == Type::Kind::Builtin ||
           (argument.kind == Type::Kind::LogicalRecord &&
            typeDeclaration(argument)->roles.empty()))) {
        fail("source.oracle-aggregate",
             "ordinary aggregates cannot contain logical protocol values",
             span);
        return {};
      }
  if (result.kind == Type::Kind::LogicalRecord && !logicalRecord(result, span))
    return {};
  if (resultNeedsPreflight && (depth == 1 || normalizationDepth == 1) &&
      !chargeType(result, span))
    return {};
  return result;
}
bool Semantics::oracleKind(const Type &kind, Span span,
                           const Declaration *scope) {
  auto formed = builtinType(oracleConstructor(kind), kind.arguments);
  if (!formed) {
    accept(formed.takeError(), span);
    return false;
  }
  const auto &row = kind.arguments.front();
  return executableType(row, span) && mathematicalData(row, span, scope) &&
         admit(row, Boundary::Participants, span, scope);
}
std::optional<Type> Semantics::associated(const Type &base, StringRef member,
                                          Span span) {
  if (normalizationDepth >= work.limits.typeDepth) {
    fail("source.limit", "type normalization depth limit", span);
    return {};
  }
  ++normalizationDepth;
  auto restoreDepth = llvm::scope_exit([&] { --normalizationDepth; });

  if (!chargeType(base, span))
    return {};
  if (member.contains("::")) {
    Type current = base;
    unsigned depth = 0;
    while (!member.empty()) {
      if (++depth > work.limits.typeDepth) {
        fail("source.limit", "associated path depth limit", span);
        return {};
      }
      auto [head, tail] = member.split("::");
      auto next = associated(current, head, span);
      if (!next)
        return {};
      current = std::move(*next);
      member = tail;
    }
    return current;
  }
  if (base.kind == Type::Kind::OracleKind) {
    auto result = oracleMember(base, member);
    if (!result) {
      accept(result.takeError(), span);
      return {};
    }
    return std::move(*result);
  }
  if (base.kind == Type::Kind::Asset)
    return assetProjection(base, member, span);
  if (!domainSort(base).empty()) {
    auto result = domainMember(base, member);
    if (!result) {
      fail("source.type", toString(result.takeError()), span);
      return {};
    }
    return std::move(*result);
  }
  if (base.kind != Type::Kind::Module) {
    fail("source.type", "associated member requires a module or domain", span);
    return {};
  }
  const Declaration *owner = nullptr;
  if (base.symbolic) {
    if (auto p = parameter(base.domain); p && p->interface)
      owner = &declarations[p->interface->index];
    else if (StringRef(base.domain).starts_with("self:")) {
      auto found = index.qualified.find(base.domain.substr(5));
      if (found != index.qualified.end())
        owner = &declarations[found->second.index];
    }
  } else
    owner = typeDeclaration(base);
  if (!owner) {
    fail("source.type", "unknown associated module", span);
    return {};
  }
  if (!charge(owner->members.size(), span))
    return {};
  for (auto id : owner->members) {
    auto &decl = declarations[id.index];
    if (decl.name != member)
      continue;
    if (decl.kind != Declaration::Kind::Associated ||
        (complete && !complete(id))) {
      if (!diagnostic)
        fail("source.type", "member is not a type", span);
      return {};
    }
    return associated(base, id, span);
  }
  fail("source.type", "unknown associated type: " + member, span);
  return {};
}
std::optional<Semantics::Dispatch>
Semantics::dispatch(const std::optional<Type> &module, DeclarationId required,
                    ArrayRef<Type> arguments, Span span,
                    unsigned enclosingCalls) {
  auto refuse = [&](StringRef message) -> std::optional<Dispatch> {
    fail("source.conformance", message, span);
    return {};
  };
  if (!charge(arguments.size() + 1, span))
    return {};
  for (const auto &argument : arguments)
    if (!chargeType(argument, span))
      return {};
  if (required.index >= declarations.size())
    return refuse("dispatch member is outside declarations");
  if (complete && !complete(required))
    return {};
  auto parent = declarations[required.index].parent;
  if (parent && parent->index >= declarations.size())
    return refuse("dispatch interface owner is outside declarations");
  if (!module || !parent ||
      declarations[parent->index].kind != Declaration::Kind::Interface ||
      module->symbolic)
    return Dispatch{required, arguments.vec()};
  if (!chargeType(*module, span))
    return {};
  const auto *definition = typeDeclaration(*module);
  if (!definition || definition->kind != Declaration::Kind::Module)
    return refuse("static dispatch requires an implementing module");
  const auto owner = definition->id;
  if (complete && !complete(owner))
    return {};
  const auto &implementation = declarations[owner.index];
  if (!implementation.implementation ||
      implementation.parameters.size() != module->arguments.size())
    return refuse("static dispatch has no implementation instance");
  auto selected =
      substitute(*implementation.implementation,
                 substitution(implementation, module->arguments), span);
  if (!selected)
    return {};
  const auto *interface = typeDeclaration(*selected);
  const auto inherited = declarations[parent->index].parameters.size();
  if (!interface || interface->id.index != parent->index ||
      selected->arguments.size() != inherited || arguments.size() < inherited ||
      ArrayRef<Type>(selected->arguments) != arguments.take_front(inherited))
    return refuse("static dispatch interface instance differs");
  if (!charge(implementation.conformance.size() + 1, span))
    return {};
  std::optional<DeclarationId> provided;
  for (const auto &edge : implementation.conformance)
    if (edge.required.index == required.index) {
      if (provided)
        return refuse("duplicate static dispatch edge");
      provided = edge.provided;
    }
  if (!provided || provided->index >= declarations.size())
    return refuse("static dispatch edge missing");
  if (complete && !complete(*provided))
    return {};
  const auto &target = declarations[provided->index];
  if ((!target.parent || target.parent->index != owner.index) ||
      target.module.index != owner.index ||
      target.kind != declarations[required.index].kind)
    return refuse("static dispatch edge has a different owner or kind");
  std::vector<Type> actual = module->arguments;
  llvm::append_range(actual, arguments.drop_front(inherited));
  if (target.parameters.size() != actual.size())
    return refuse("static dispatch member arguments differ");
  const bool callable = target.kind == Declaration::Kind::Math ||
                        target.kind == Declaration::Kind::Local ||
                        target.kind == Declaration::Kind::Protocol ||
                        target.kind == Declaration::Kind::View;
  if (callable && completeDispatchBody &&
      !completeDispatchBody(*provided, enclosingCalls))
    return {};
  return Dispatch{*provided, std::move(actual)};
}
std::optional<Type> Semantics::associated(const Type &base,
                                          DeclarationId required, Span span) {
  if (required.index >= declarations.size()) {
    fail("source.type", "associated member is outside declarations", span);
    return {};
  }
  if (complete && !complete(required))
    return {};
  auto parent = declarations[required.index].parent;
  if (!parent || parent->index >= declarations.size() ||
      declarations[required.index].kind != Declaration::Kind::Associated) {
    fail("source.type", "projection is not an associated member", span);
    return {};
  }
  if (!base.symbolic &&
      declarations[parent->index].kind == Declaration::Kind::Module) {
    const auto *owner = typeDeclaration(base);
    if (!owner || owner->id.index != parent->index) {
      fail("source.conformance", "associated member belongs to another module",
           span);
      return {};
    }
  }
  std::vector<Type> arguments = base.arguments;
  if (!base.symbolic &&
      declarations[parent->index].kind == Declaration::Kind::Interface) {
    const auto *owner = typeDeclaration(base);
    if (!owner || (complete && !complete(owner->id)))
      return {};
    if (!owner->implementation) {
      fail("source.conformance", "associated module has no implementation",
           span);
      return {};
    }
    auto instance = substitute(*owner->implementation,
                               substitution(*owner, base.arguments), span);
    if (!instance)
      return {};
    arguments = std::move(instance->arguments);
  }
  auto selected = dispatch(base, required, arguments, span);
  if (!selected)
    return {};
  const auto &decl = declarations[selected->declaration.index];
  Type result(Type::Kind::Associated, decl.qualifiedName);
  result.arguments = {base};
  result.assumptions = decl.permissions.value_or(Permissions{});
  if (isDomainSort(decl.associatedSort)) {
    if (!decl.abstract)
      return substitute(
          decl.domain,
          substitution(declarations[decl.parent->index], selected->arguments),
          span);
    auto domain = domainType(decl.associatedSort, decl.qualifiedName);
    domain.arguments = {base};
    domain.assumptions = result.assumptions;
    result = std::move(domain);
    result.symbolic = true;
  }
  return result;
}
std::optional<Substitution>
Semantics::boundMemberSubstitution(const Declaration &callee,
                                   const Type &module, Span span) {
  if (!chargeType(module, span))
    return {};
  if (!callee.parent) {
    fail("source.call", "bound callable has no interface owner", span);
    return {};
  }
  const auto &parent = declarations[callee.parent->index];
  Type interface = module;
  if (!module.symbolic && parent.kind == Declaration::Kind::Interface) {
    const auto *owner = typeDeclaration(module);
    if (!owner || !owner->implementation) {
      fail("source.conformance", "bound callable requires a module", span);
      return {};
    }
    auto selected = substitute(*owner->implementation,
                               substitution(*owner, module.arguments), span);
    if (!selected)
      return {};
    interface = std::move(*selected);
  }
  if (interface.arguments.size() != parent.parameters.size() ||
      callee.parameters.size() < parent.parameters.size()) {
    fail("source.conformance", "bound member static arguments differ", span);
    return {};
  }
  Substitution result;
  for (unsigned i = 0; i < parent.parameters.size(); ++i)
    result.emplace(callee.parameters[i].atom, interface.arguments[i]);
  result.emplace("self:" + parent.qualifiedName, module);
  return result;
}

bool Semantics::checkArgumentSorts(const Declaration &target,
                                   ArrayRef<Type> args, Span span,
                                   const Substitution &extra) {
  if (!charge(args.size() + 1, span))
    return false;
  std::vector<std::optional<Type>> known(args.begin(), args.end());
  return checkKnownArgumentSorts(target, known, span, extra);
}
bool Semantics::checkKnownArgumentSorts(const Declaration &target,
                                        ArrayRef<std::optional<Type>> args,
                                        Span span, const Substitution &extra) {
  if (args.size() != target.parameters.size())
    return fail("source.generic", "static argument count differs", span);
  Substitution subst = extra;
  std::set<std::string> unknown;
  for (unsigned i = 0; i < args.size(); ++i)
    if (args[i])
      subst.insert_or_assign(target.parameters[i].atom, *args[i]);
    else
      unknown.insert(target.parameters[i].atom);
  std::function<bool(const Type &)> ready = [&](const Type &type) {
    if (unknown.count(type.domain))
      return false;
    for (const auto &[factors, coefficient] : type.dimension.terms()) {
      (void)coefficient;
      for (const auto &factor : factors)
        if (unknown.count(factor.name))
          return false;
    }
    return llvm::all_of(type.arguments, ready);
  };
  for (unsigned i = 0; i < args.size(); ++i) {
    if (!args[i])
      continue;
    auto &p = target.parameters[i];
    auto &a = *args[i];
    bool kind = false;
    switch (p.sort) {
    case Parameter::Sort::Domain:
      kind = domainSort(a) == p.domainSort;
      break;
    case Parameter::Sort::Asset:
      kind = assetSort(a) == p.domainSort;
      break;
    case Parameter::Sort::Natural:
      kind = a.kind == Type::Kind::Natural;
      break;
    case Parameter::Sort::OracleKind:
      kind = a.kind == Type::Kind::OracleKind;
      break;
    case Parameter::Sort::Type:
      kind = valueType(a);
      if (kind && !executableType(a, span))
        return false;
      break;
    case Parameter::Sort::Module: {
      kind = a.kind == Type::Kind::Module;
      if (!kind)
        break;
      const Declaration *actual = nullptr;
      std::vector<Type> actualArgs;
      if (a.symbolic) {
        auto param = parameter(a.domain);
        if (param && param->interface) {
          actual = &declarations[param->interface->index];
          actualArgs = param->arguments;
        }
      } else {
        auto module = typeDeclaration(a);
        if (module && module->implementation) {
          auto selected = substitute(*module->implementation,
                                     substitution(*module, a.arguments), span);
          if (!selected)
            return false;
          actual = typeDeclaration(*selected);
          actualArgs = selected->arguments;
        }
      }
      if (!actual || !p.interface || actual->id.index != p.interface->index)
        return fail("source.conformance",
                    "module does not implement required interface", span);
      if (actualArgs.size() != p.arguments.size())
        return fail("source.conformance", "interface static arguments differ",
                    span);
      for (unsigned j = 0; j < p.arguments.size(); ++j) {
        if (!chargeType(p.arguments[j], span))
          return false;
        if (!ready(p.arguments[j]))
          continue;
        auto expected = substitute(p.arguments[j], subst, span);
        if (!expected)
          return false;
        if (*expected != actualArgs[j])
          return fail("source.conformance", "interface static arguments differ",
                      span);
      }
      break;
    }
    }
    if (!kind)
      return fail("source.generic", "static argument has wrong sort", span);
  }
  return true;
}
bool Semantics::checkArguments(const Declaration &target, ArrayRef<Type> args,
                               Span span, const Declaration *context,
                               const Substitution &extra) {
  if (!checkArgumentSorts(target, args, span, extra))
    return false;
  auto subst = substitution(target, args);
  subst.insert(extra.begin(), extra.end());
  auto satisfies = [&](const Type &type, Permissions required,
                       StringRef message) {
    if (required.copy && !requireUsage(type, Usage::Copy, span, context,
                                       "source.permission", message))
      return false;
    if (required.drop && !required.copy &&
        !requireUsage(type, Usage::Drop, span, context, "source.permission",
                      message))
      return false;
    return true;
  };
  for (unsigned i = 0; i < args.size(); ++i) {
    const auto &p = target.parameters[i];
    const auto &a = args[i];
    if (valueType(a)) {
      if (!satisfies(a, p.permissions,
                     "static argument lacks required permission"))
        return false;
    }
  }
  for (const auto &bound : target.capabilityBounds) {
    CapabilityBound goal{bound.predicate, {}, span};
    for (const auto &argument : bound.arguments) {
      auto actual = substitute(argument, subst, span);
      if (!actual)
        return false;
      goal.arguments.push_back(std::move(*actual));
    }
    if (!entails(context, goal)) {
      if (diagnostic)
        diagnostic->related.push_back(bound.span);
      return false;
    }
  }
  for (const auto &bound : target.permissionBounds) {
    Type requirement = bound.type;
    requirement.assumptions = {};
    auto actual = substitute(requirement, subst, span);
    if (!actual)
      return false;
    if (!satisfies(*actual, bound.permissions,
                   "type lacks required usage property")) {
      if (diagnostic)
        diagnostic->related.push_back(bound.span);
      return false;
    }
  }
  for (const auto &obligation : target.admissions) {
    auto actual = substitute(obligation.type, subst, span);
    if (!actual || !charge(obligation.calls.size() + 1, span))
      return false;
    auto calls = obligation.calls;
    calls.push_back(span);
    if (!admit(*actual, obligation.boundary, obligation.span, context, calls))
      return false;
  }
  for (auto &bound : target.bounds) {
    Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
    lhs.dimension = bound.lhs;
    rhs.dimension = bound.rhs;
    auto l = substitute(lhs, subst, span), r = substitute(rhs, subst, span);
    if (!l || !r)
      return false;
    if (l->dimension.isClosed() && r->dimension.isClosed() &&
        l->dimension.closedValue() > r->dimension.closedValue())
      return fail("source.bound", "closed natural requirement does not hold",
                  span, {bound.span});
  }
  return true;
}
bool Semantics::structuralAssumptions(const Declaration &caller,
                                      const NaturalBound &bound,
                                      const Substitution &bindings, Span span,
                                      StringRef code) {
  if (!charge(2 * sizeof(Type), span))
    return false;
  auto leftCopy = naturals.add(bound.lhs, Natural{});
  if (!leftCopy)
    return accept(leftCopy.takeError(), span);
  auto rightCopy = naturals.add(bound.rhs, Natural{});
  if (!rightCopy)
    return accept(rightCopy.takeError(), span);
  Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
  lhs.dimension = std::move(*leftCopy);
  rhs.dimension = std::move(*rightCopy);
  auto l = substitute(lhs, bindings, span), r = substitute(rhs, bindings, span);
  if (!l || !r)
    return false;
  auto requested = naturals.cancelCommonTerms(l->dimension, r->dimension);
  if (!requested)
    return accept(requested.takeError(), span);
  auto dominates = [&](const Natural &a, const Natural &b) -> bool {
    auto result = naturals.dominatedBy(a, b);
    if (!result) {
      accept(result.takeError(), span);
      return false;
    }
    return *result;
  };
  const auto &[left, right] = *requested;
  if (dominates(left, right))
    return true;
  if (diagnostic)
    return false;
  // A closed contradiction cannot be licensed by an inconsistent premise.
  if (left.isClosed() && right.isClosed())
    return fail(code, "natural requirement is false", span, {bound.span});
  for (const auto &given : caller.bounds) {
    if (!charge(1, span))
      return false;
    auto premise = naturals.cancelCommonTerms(given.lhs, given.rhs);
    if (!premise)
      return accept(premise.takeError(), span);
    if (dominates(left, premise->first) && dominates(premise->second, right))
      return true;
    if (diagnostic)
      return false;
  }
  return fail(code, "contract does not establish structural View bound", span,
              {bound.span});
}
bool Semantics::assumptions(const Declaration &caller,
                            const NaturalBound &bound,
                            const Substitution &bindings, Span span) {
  Type lhs(Type::Kind::Natural), rhs(Type::Kind::Natural);
  lhs.dimension = bound.lhs;
  rhs.dimension = bound.rhs;
  auto l = substitute(lhs, bindings, span), r = substitute(rhs, bindings, span);
  if (!l || !r)
    return false;
  auto cancel =
      [&](const Natural &left,
          const Natural &right) -> std::optional<std::pair<Natural, Natural>> {
    auto result = naturals.cancelCommonTerms(left, right);
    if (!result) {
      accept(result.takeError(), span);
      return {};
    }
    return std::move(*result);
  };
  auto requested = cancel(l->dimension, r->dimension);
  if (!requested)
    return false;
  const auto &[requestedLeft, requestedRight] = *requested;
  if (requestedLeft.isClosed() && requestedRight.isClosed())
    return requestedLeft.closedValue() <= requestedRight.closedValue() ||
           fail("source.bound", "natural requirement is false", span);
  if (requestedLeft == requestedRight)
    return true;
  for (auto &given : caller.bounds) {
    if (!charge(1, span))
      return false;
    auto available = cancel(given.lhs, given.rhs);
    if (!available)
      return false;
    const auto &[givenLeft, givenRight] = *available;
    if (givenRight == requestedRight &&
        (givenLeft == requestedLeft ||
         (givenLeft.isClosed() && requestedLeft.isClosed() &&
          givenLeft.closedValue() >= requestedLeft.closedValue())))
      return true;
  }
  // Cancellation is only a comparison view. Preserve the substituted source
  // obligation when collecting an inferred contract.
  return (inferNatural &&
          inferNatural(caller, {l->dimension, r->dimension, span})) ||
         fail("source.bound", "contract does not establish natural bound", span,
              {bound.span});
}

} // namespace zkc::language::detail
