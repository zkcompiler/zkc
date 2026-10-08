#include "Checker.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/R1CS.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
bool Checker::relationData(const Declaration &scope, const Type &type,
                           Span span, unsigned depth) {
  if (depth > work.limits.typeDepth)
    return fail("source.limit", "relation data depth exceeded", span);
  if (!charge(1, span))
    return false;
  if (!depth) {
    if (!chargeType(type, span) || !executableType(type, span))
      return false;
    auto caps = permissions(type, span, &scope);
    if (!caps)
      return false;
    if (!caps->copy || !caps->drop)
      return fail("source.relation", "relation inputs require immutable data",
                  span);
  }
  if (symbolic(type))
    return true; // Closed instantiation rechecks the selected representation.
  using K = Type::Kind;
  if (isNativeData(type)) {
    auto native = builtinLayout(type);
    if (!native)
      return accept(native.takeError());
    protocol::TypeParseBudget budget;
    budget.remaining =
        std::min<uint64_t>(budget.remaining, work.limits.work - work.used);
    auto before = budget.remaining;
    auto result = protocol::logicalRelationData(*native, budget);
    if (!charge(before - budget.remaining, span))
      return false;
    if (result == protocol::RelationData::Limit)
      return fail("source.limit", "relation data work or depth limit exceeded",
                  span);
    return result == protocol::RelationData::Supported ||
           fail("source.relation", "type is not immutable relation data", span);
  }
  if (type.kind == K::Unit)
    return true;
  if (type.kind == K::Array)
    return relationData(scope, type.arguments.front(), span, depth + 1);
  if (type.kind == K::Variant) {
    auto arms = alternatives(type, span, depth + 1);
    if (!arms)
      return false;
    for (const auto &arm : *arms)
      for (const auto &field : arm.fields)
        if (!relationData(scope, field.type, span, depth + 1))
          return false;
    return true;
  }
  auto product = fields(type, span, depth);
  if (!product)
    return false;
  for (const auto &field : *product)
    if (!relationData(scope, field.type, span, depth + 1))
      return false;
  return true;
}
bool Checker::relationIdentities() {
  using Identity = std::tuple<std::string, std::string, std::string>;
  std::map<Identity, const Declaration *> identities;
  for (const auto &decl : output.declarations) {
    if (!decl.relation ||
        decl.relation->kind != RelationDefinition::Kind::Opaque)
      continue;
    const auto &definition = *decl.relation;
    if (!charge(definition.externalKind.size() + definition.key.size() +
                    definition.revision.size() + 1,
                decl.span))
      return false;
    auto [it, added] = identities.emplace(
        Identity{definition.externalKind, definition.key, definition.revision},
        &decl);
    if (added)
      continue;
    const auto &previous = *it->second;
    if (decl.inputs.size() != previous.inputs.size() ||
        definition.purposes != previous.relation->purposes)
      return fail("source.relation",
                  "one opaque identity has conflicting logical signatures",
                  decl.span, {previous.span});
    for (unsigned i = 0; i < decl.inputs.size(); ++i) {
      if (!chargeType(decl.inputs[i].type, decl.span) ||
          !chargeType(previous.inputs[i].type, previous.span))
        return false;
      if (decl.inputs[i].type != previous.inputs[i].type)
        return fail("source.relation",
                    "one opaque identity has conflicting logical signatures",
                    decl.span, {previous.span});
    }
  }
  return true;
}
bool Checker::relation(Declaration &decl) {
  auto &definition = *decl.relation;
  if (!charge(definition.purposes.size() + definition.externalKind.size() +
                  definition.key.size() + definition.revision.size() +
                  output.assets.size() + 1,
              decl.span))
    return false;
  for (const auto &port : decl.inputs)
    if (!relationData(decl, port.type, port.span))
      return false;
  using K = RelationDefinition::Kind;
  if (definition.kind == K::Formula)
    return true;
  if (definition.kind == K::Opaque) {
    if (!decl.parameters.empty())
      return fail("source.relation",
                  "opaque identities require a fixed logical signature",
                  decl.span);
    if (definition.externalKind.empty() || definition.key.empty() ||
        definition.revision.empty() ||
        StringRef(definition.externalKind).starts_with("zkc."))
      return fail("source.relation", "opaque identity is empty or source-owned",
                  decl.span);
    return true;
  }
  if (!decl.parameters.empty())
    return fail("source.relation", "captured relations have a fixed signature",
                decl.span);
  auto name = sources[decl.id.index]->relation->asset;
  auto found = llvm::find_if(
      output.assets, [&](const auto &asset) { return asset.name() == name; });
  if (found == output.assets.end() ||
      (definition.kind == K::R1CS ? !found->r1cs() : !found->air()))
    return fail("source.relation",
                "captured asset is absent or has a different kind", decl.span);
  definition.asset = found - output.assets.begin();
  std::string field = found->r1cs() ? found->r1cs()->field().str()
                                    : found->air()->field().str();
  auto array = [&](unsigned count) {
    Type n(Type::Kind::Natural);
    n.dimension = Natural::constant(count);
    Type t(Type::Kind::Builtin, "field_array");
    t.arguments = {Type(Type::Kind::Field, field), n};
    return t;
  };
  std::vector<Type> expected;
  if (auto *r1cs = found->r1cs())
    expected = {array(r1cs->publicCount()), array(r1cs->columns())};
  else {
    Type trace(Type::Kind::Builtin, "matrix");
    trace.arguments = {Type(Type::Kind::Field, field)};
    expected = {array(found->air()->publicInputs()), std::move(trace)};
  }
  if (decl.inputs.size() != 2 ||
      definition.purposes !=
          std::vector<RelationPurpose>{RelationPurpose::Statement,
                                       RelationPurpose::Witness} ||
      decl.inputs[0].type != expected[0] || decl.inputs[1].type != expected[1])
    return fail(
        "source.relation",
        "captured relation signature or purposes differ from its asset ABI",
        decl.span);
  return true;
}
std::optional<Type> Checker::selectedType(const Declaration &decl,
                                          const SpecificationSelector &value) {
  const auto &ports = value.output ? decl.outputs : decl.inputs;
  if (value.port >= ports.size() || value.role >= decl.roles.size() ||
      !llvm::is_contained(ports[value.port].roles, value.role)) {
    fail("source.specification",
         "selector does not name an available port component", value.span);
    return {};
  }
  return projectedType(decl, ports[value.port].type, value.path, value.span);
}
std::optional<SpecificationSelector>
Checker::selector(const Declaration &decl, const SyntaxSelector &source) {
  const auto &ports = source.output ? decl.outputs : decl.inputs;
  if (!charge(ports.size() + 1, source.span))
    return {};
  auto found = llvm::find_if(
      ports, [&](const Port &port) { return port.name == source.port; });
  if (found == ports.end()) {
    fail("source.specification", "selector must name a declared logical port",
         source.span);
    return {};
  }
  unsigned role;
  if (source.role) {
    auto selected = roles(decl, {*source.role}, source.span);
    if (!selected)
      return {};
    role = selected->front();
  } else if (found->roles.size() == 1)
    role = found->roles.front();
  else {
    fail("source.specification",
         "selector must name one actual participant component", source.span);
    return {};
  }
  SpecificationSelector result{
      source.output, unsigned(found - ports.begin()), role, {}, source.span};
  auto current = selectedType(decl, result);
  if (!current)
    return {};
  for (const auto &name : source.path) {
    auto index = fieldIndex(decl, *current, name, source.span);
    if (!index)
      return {};
    current = projectedType(decl, std::move(*current), {*index}, source.span);
    if (!current)
      return {};
    result.path.push_back(*index);
  }
  return result;
}

bool Checker::specifications(Declaration &decl) {
  auto apply =
      [&](const SyntaxSubject &source) -> std::optional<RelationApplication> {
    auto target =
        source.inlineMember
            ? std::optional<DeclarationId>(decl.members[*source.inlineMember])
            : resolve(decl, source.relation.name, source.span);
    if (!target)
      return {};
    const auto &relation = output.declarations[target->index];
    if (relation.kind != Declaration::Kind::Relation) {
      fail("source.specification", "clause requires a relation declaration",
           source.span);
      return {};
    }
    auto args =
        arguments(decl, relation, source.relation.arguments, source.span);
    if (!args)
      return {};
    const auto *inlined =
        source.inlineMember ? &inlineBindings[relation.id.index] : nullptr;
    if ((inlined ? inlined->size() : source.operands.size()) !=
        relation.inputs.size()) {
      fail("source.specification", "relation argument count differs",
           source.span);
      return {};
    }
    RelationApplication result{*target, std::move(*args), {}, source.span};
    auto bindings = substitution(relation, result.arguments);
    for (unsigned i = 0; i < relation.inputs.size(); ++i) {
      auto selected = inlined
                          ? std::optional<SpecificationSelector>((*inlined)[i])
                          : selector(decl, source.operands[i]);
      if (!selected)
        return {};
      auto actual = selectedType(decl, *selected);
      auto expected =
          substitute(relation.inputs[i].type, bindings, source.span);
      if (!actual || !expected)
        return {};
      if (*actual != *expected) {
        fail("source.specification",
             "relation operand has a different logical type", selected->span);
        return {};
      }
      result.operands.push_back(std::move(*selected));
    }
    return result;
  };
  std::set<std::string> names;
  for (const auto &source : sources[decl.id.index]->specifications) {
    if (!charge(source.name.size() + 1, source.span))
      return false;
    if (!names.insert(source.name).second)
      return fail("source.duplicate", "duplicate specification clause",
                  source.span);
    auto subject = apply(source.subject);
    if (!subject)
      return false;
    SpecificationClause clause{source.kind, source.name, std::move(*subject),
                               {},          {},          source.span};
    using K = SpecificationClause::Kind;
    auto hasOutput = [](const RelationApplication &subject) {
      return llvm::any_of(subject.operands,
                          [](const auto &operand) { return operand.output; });
    };
    if (((source.kind == K::Input || source.kind == K::Continuation) &&
         hasOutput(clause.subject)) ||
        (source.kind == K::Output && !hasOutput(clause.subject)))
      return fail("source.specification",
                  "clause has the wrong input/output direction", source.span);
    if (source.residual) {
      if (source.kind != K::Continuation)
        return fail("source.specification",
                    "only a continuation has a residual", source.span);
      auto residual = apply(*source.residual);
      if (!residual)
        return false;
      if (!hasOutput(*residual))
        return fail("source.specification",
                    "residual must bind an actual output", source.span);
      clause.residual = std::move(*residual);
    } else if (source.kind == K::Continuation)
      return fail("source.specification", "continuation requires a residual",
                  source.span);
    if (source.decision) {
      auto decision = selector(decl, *source.decision);
      if (!decision)
        return false;
      auto type = selectedType(decl, *decision);
      if (!type)
        return false;
      if (source.kind == K::Input || !decision->output ||
          type->kind != Type::Kind::Boolean)
        return fail("source.specification",
                    "decision must select one Boolean output", source.span);
      clause.decision = std::move(*decision);
    } else if (source.kind == K::Target)
      return fail("source.specification",
                  "target requires an explicit decision output", source.span);
    decl.specifications.push_back(std::move(clause));
  }
  return true;
}
} // namespace zkc::language::detail
