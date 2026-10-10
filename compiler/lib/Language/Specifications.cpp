#include "Checker.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Language/Builtins.h"
#include "zkc/Language/RelationABI.h"
#include "zkc/Relation/AIR.h"
#include "zkc/Relation/Bundle.h"
#include "zkc/Relation/R1CS.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {

bool Checker::relationIdentities() {
  using Identity = std::tuple<std::string, std::string, std::string>;
  std::map<Identity, const Declaration *> identities;
  for (const auto &decl : output.declarations) {
    if (!decl.relation ||
        decl.relation->kind != RelationDefinition::Kind::Opaque)
      continue;
    const auto &definition = *decl.relation;
    if (!types.charge(definition.externalKind.size() + definition.key.size() +
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
      return types.fail(
          "source.relation",
          "one opaque identity has conflicting logical signatures", decl.span,
          {previous.span});
    for (unsigned i = 0; i < decl.inputs.size(); ++i) {
      if (!types.chargeType(decl.inputs[i].type, decl.span) ||
          !types.chargeType(previous.inputs[i].type, previous.span))
        return false;
      if (decl.inputs[i].type != previous.inputs[i].type)
        return types.fail(
            "source.relation",
            "one opaque identity has conflicting logical signatures", decl.span,
            {previous.span});
    }
  }
  return true;
}
bool Checker::relation(Declaration &decl) {
  auto &definition = *decl.relation;
  if (!types.charge(definition.purposes.size() +
                        definition.externalKind.size() + definition.key.size() +
                        definition.revision.size() + output.assets.size() + 1,
                    decl.span))
    return false;
  for (const auto &port : decl.inputs)
    if (!types.relationData(decl, port.type, port.span))
      return false;
  using K = RelationDefinition::Kind;
  if (definition.kind == K::Formula)
    return true;
  if (definition.kind == K::Opaque) {
    if (!decl.parameters.empty())
      return types.fail("source.relation",
                        "opaque identities require a fixed logical signature",
                        decl.span);
    if (definition.externalKind.empty() || definition.key.empty() ||
        definition.revision.empty() ||
        StringRef(definition.externalKind).starts_with("zkc."))
      return types.fail("source.relation",
                        "opaque identity is empty or source-owned", decl.span);
    return true;
  }
  if (!decl.parameters.empty())
    return types.fail("source.relation",
                      "captured relations have a fixed signature", decl.span);
  auto name = sources[decl.id.index]->relation->asset;
  auto found = llvm::find_if(
      output.assets, [&](const auto &asset) { return asset.name() == name; });
  bool matched = found != output.assets.end() &&
                 (definition.kind == K::R1CS  ? found->r1cs() != nullptr
                  : definition.kind == K::AIR ? found->air() != nullptr
                                              : found->bundle() != nullptr);
  if (!matched)
    return types.fail("source.relation",
                      "captured asset is absent or has a different kind",
                      decl.span);
  definition.asset = found - output.assets.begin();
  if (definition.kind == K::Bundle) {
    // The bundle alone fixes the signature; the declaration must spell the
    // derived formals exactly, in order, with their purposes.
    auto derived = bundleRelationFormals(*found->bundle());
    if (!types.charge(derived.size() + 1, decl.span))
      return false;
    if (decl.inputs.size() != derived.size())
      return types.fail("source.relation",
                        "bundle relation declares " +
                            std::to_string(decl.inputs.size()) +
                            " formals but its asset ABI derives " +
                            std::to_string(derived.size()),
                        decl.span);
    for (unsigned i = 0; i < derived.size(); ++i) {
      if (!types.chargeType(decl.inputs[i].type, decl.inputs[i].span))
        return false;
      if (definition.purposes[i] != derived[i].purpose ||
          decl.inputs[i].type != derived[i].type)
        return types.fail("source.relation",
                          "bundle relation formal " + std::to_string(i) +
                              " differs from the derived asset ABI (" +
                              derived[i].label + ")",
                          decl.inputs[i].span);
    }
    return true;
  }
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
    return types.fail(
        "source.relation",
        "captured relation signature or purposes differ from its asset ABI",
        decl.span);
  return true;
}

std::optional<SpecificationSelector>
Checker::selector(const Declaration &decl, const SyntaxSelector &source) {
  const auto &ports = source.output ? decl.outputs : decl.inputs;
  if (!types.charge(ports.size() + 1, source.span))
    return {};
  auto found = llvm::find_if(
      ports, [&](const Port &port) { return port.name == source.port; });
  if (found == ports.end()) {
    types.fail("source.specification",
               "selector must name a declared logical port", source.span);
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
    types.fail("source.specification",
               "selector must name one actual participant component",
               source.span);
    return {};
  }
  SpecificationSelector result{
      source.output, unsigned(found - ports.begin()), role, {}, source.span};
  auto current = types.selectedType(decl, result);
  if (!current)
    return {};
  for (const auto &name : source.path) {
    auto index = types.fieldIndex(decl, *current, name, source.span);
    if (!index)
      return {};
    current =
        types.projectedType(decl, std::move(*current), {*index}, source.span);
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
      types.fail("source.specification",
                 "clause requires a relation declaration", source.span);
      return {};
    }
    auto args = arguments(decl, relation, source.relation.arguments,
                          source.span, source.relation.labels);
    if (!args)
      return {};
    const auto *inlined =
        source.inlineMember ? &inlineBindings[relation.id.index] : nullptr;
    if ((inlined ? inlined->size() : source.operands.size()) !=
        relation.inputs.size()) {
      types.fail("source.specification", "relation argument count differs",
                 source.span);
      return {};
    }
    RelationApplication result{*target, std::move(*args), {}, source.span};
    auto bindings = types.substitution(relation, result.arguments);
    for (unsigned i = 0; i < relation.inputs.size(); ++i) {
      auto selected = inlined
                          ? std::optional<SpecificationSelector>((*inlined)[i])
                          : selector(decl, source.operands[i]);
      if (!selected)
        return {};
      auto actual = types.selectedType(decl, *selected);
      auto expected =
          types.substitute(relation.inputs[i].type, bindings, source.span);
      if (!actual || !expected)
        return {};
      if (*actual != *expected) {
        types.fail("source.specification",
                   "relation operand has a different logical type",
                   selected->span);
        return {};
      }
      result.operands.push_back(std::move(*selected));
    }
    return result;
  };
  std::set<std::string> names;
  for (const auto &source : sources[decl.id.index]->specifications) {
    if (!types.charge(source.name.size() + 1, source.span))
      return false;
    if (!names.insert(source.name).second)
      return types.fail("source.duplicate", "duplicate specification clause",
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
      return types.fail("source.specification",
                        "clause has the wrong input/output direction",
                        source.span);
    if (source.residual) {
      if (source.kind != K::Continuation)
        return types.fail("source.specification",
                          "only a continuation has a residual", source.span);
      auto residual = apply(*source.residual);
      if (!residual)
        return false;
      if (!hasOutput(*residual))
        return types.fail("source.specification",
                          "residual must bind an actual output", source.span);
      clause.residual = std::move(*residual);
    } else if (source.kind == K::Continuation)
      return types.fail("source.specification",
                        "continuation requires a residual", source.span);
    if (source.decision) {
      auto decision = selector(decl, *source.decision);
      if (!decision)
        return false;
      auto type = types.selectedType(decl, *decision);
      if (!type)
        return false;
      if (source.kind == K::Input || !decision->output ||
          type->kind != Type::Kind::Boolean)
        return types.fail("source.specification",
                          "decision must select one Boolean output",
                          source.span);
      clause.decision = std::move(*decision);
    } else if (source.kind == K::Target)
      return types.fail("source.specification",
                        "target requires an explicit decision output",
                        source.span);
    decl.specifications.push_back(std::move(clause));
  }
  return true;
}
} // namespace zkc::language::detail
