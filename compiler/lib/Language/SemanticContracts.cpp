#include "Semantics.h"
#include "zkc/Contracts/NativePolicy.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
bool Semantics::relationData(const Declaration &scope, const Type &type,
                             Span span, unsigned depth) {
  if (depth > work.limits.typeDepth)
    return fail("source.limit", "relation data depth exceeded", span);
  if (!charge(1, span))
    return false;
  if (!depth) {
    if (!chargeType(type, span))
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
      return accept(native.takeError(), span);
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
std::optional<Type>
Semantics::selectedType(const Declaration &decl,
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
bool Semantics::checkProofEntry(const Declaration &entry,
                                const Declaration &protocol) {
  if (!entry.proof())
    return true;
  const auto &value = *entry.proof();
  if (!charge(protocol.inputs.size() + protocol.services.size() +
                  value.publicInputs.size() + value.acceptance.path.size() + 1,
              value.span))
    return false;
  if (protocol.roles.size() != 2 || value.prover >= protocol.roles.size() ||
      value.verifier >= protocol.roles.size() || value.prover == value.verifier)
    return fail("source.entry",
                "proof Entry requires two distinct participants", value.span);
  std::vector<unsigned> required;
  for (unsigned i = 0; i < protocol.inputs.size(); ++i)
    if (is_contained(protocol.inputs[i].roles, value.verifier))
      required.push_back(i);
  if (required != value.publicInputs) {
    std::string expected = "public {";
    for (auto index : required) {
      if (expected.back() != '{')
        expected += ", ";
      expected += protocol.inputs[index].name;
    }
    expected += "};";
    return fail(
        "source.entry",
        "public inputs must exactly authorize verifier data ports; expected " +
            expected,
        value.span);
  }
  auto bindings = substitution(protocol, entry.staticArguments);
  auto booleanOutput = [&](const SpecificationSelector &selected, unsigned role,
                           StringRef keyword) {
    if (!charge(selected.path.size() + 1, selected.span))
      return false;
    if (!selected.output || selected.role != role ||
        selected.port >= protocol.outputs.size() ||
        !is_contained(protocol.outputs[selected.port].roles, role))
      return fail("source.entry",
                  (keyword + " result is unavailable at its participant").str(),
                  selected.span);
    auto type = substitute(protocol.outputs[selected.port].type, bindings,
                           selected.span);
    if (!type)
      return false;
    type = projectedType(entry, std::move(*type), selected.path, selected.span);
    if (!type)
      return false;
    return type->kind == Type::Kind::Boolean ||
           fail("source.entry",
                (keyword + " must select a Boolean output").str(),
                selected.span);
  };
  const auto &acceptance = value.acceptance;
  if (!booleanOutput(acceptance, value.verifier, "accept") ||
      (value.completion &&
       !booleanOutput(*value.completion, value.prover, "complete")))
    return false;
  if (value.construction == ProofEntry::Construction::Authored) {
    if (!value.suite.empty() || value.service)
      return fail("source.entry",
                  "authored construction cannot derive a service", value.span);
  } else {
    auto field = protocol::nativeChallengeField(value.suite);
    if (field.empty() || !value.service ||
        *value.service >= protocol.services.size() ||
        protocol.services[*value.service].owner != value.verifier)
      return fail("source.entry",
                  "construction requires an installed suite and matching "
                  "verifier service",
                  value.span);
    auto selected = substitute(protocol.services[*value.service].field,
                               bindings, value.span);
    if (!selected)
      return false;
    if (selected->kind != Type::Kind::Field || selected->domain != field)
      return fail("source.entry", "construction field differs from service",
                  value.span);
  }
  for (unsigned i = 0; i < protocol.services.size(); ++i)
    if (protocol.services[i].owner == value.verifier && value.service != i)
      return fail("source.entry",
                  "verifier services must belong to the selected construction",
                  protocol.services[i].span);
  if (value.target) {
    if (*value.target >= protocol.specifications.size())
      return fail("source.entry", "selected target is absent", value.span);
    const auto &clause = protocol.specifications[*value.target];
    if (clause.kind != SpecificationClause::Kind::Target || !clause.decision ||
        clause.decision->port != acceptance.port ||
        clause.decision->path != acceptance.path ||
        clause.decision->role != value.verifier)
      return fail("source.entry",
                  "selected target must use the Entry acceptance", clause.span);
    const auto &relation = declarations[clause.subject.relation.index];
    for (auto [operand, purpose] :
         zip(clause.subject.operands, relation.relation->purposes)) {
      if (!charge(operand.path.size() + 1, operand.span))
        return false;
      if (operand.output || operand.port >= protocol.inputs.size())
        return fail("source.entry",
                    "native statement export requires entry inputs",
                    operand.span);
      bool visible =
          is_contained(protocol.inputs[operand.port].roles, value.verifier);
      if ((purpose == RelationPurpose::Witness) == visible)
        return fail("source.entry",
                    "target purpose disagrees with verifier input availability",
                    operand.span);
    }
  }
  return true;
}
} // namespace zkc::language::detail
