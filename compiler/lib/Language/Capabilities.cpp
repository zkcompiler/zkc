#include "Semantics.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include <cassert>
using namespace llvm;
namespace zkc::language::detail {
namespace {
const protocol::CapabilityDeclaration *declaration(StringRef name) {
  const auto &all = protocol::capabilityDeclarations();
  auto found =
      llvm::find_if(all, [&](const auto &d) { return d.name == name; });
  return found == all.end() ? nullptr : &*found;
}
StringRef sort(const protocol::StaticParameter &parameter) {
  using K = protocol::StaticKind;
  return parameter.kind == K::Type  ? StringRef("Type")
         : parameter.kind == K::Nat ? StringRef("Nat")
                                    : StringRef(parameter.sort);
}
std::string display(StringRef predicate) {
  for (const auto &entry : protocol::sourceCapabilityExports())
    if (entry.predicate == predicate)
      return entry.module + "::" + entry.name;
  return predicate.str() + " (no source export)";
}
} // namespace
Error checkCapabilityInstallation() {
  // Generic type bounds can disappear when aliases normalize. The installed
  // facts must therefore sustain the sort assumptions and implication rules.
  const auto &catalog = protocol::installedDomains();
  for (const auto &rule : protocol::boundCapabilityRules()) {
    const auto *premise = declaration(rule.premise);
    const auto *conclusion = declaration(rule.conclusion);
    if (!premise || !conclusion || premise->parameters.size() != 1 ||
        conclusion->parameters.size() != 1)
      return failure("source.installation",
                     "capability implications must be unary");
  }
  for (const auto &domain : catalog.allDomains()) {
    if ((domain.sort == "Field" || domain.sort == "Group") &&
        !catalog.hasFact(domain.sort, {domain.identity}))
      return failure("source.installation",
                     "domain lacks its inherent capability: " +
                         domain.identity);
    for (const auto &rule : protocol::boundCapabilityRules())
      if (catalog.hasFact(rule.premise, {domain.identity}) &&
          !catalog.hasFact(rule.conclusion, {domain.identity}))
        return failure(
            "source.installation",
            "domain facts are not closed under capability implications: " +
                domain.identity);
  }
  return Error::success();
}

bool Semantics::capabilityFormation(const CapabilityBound &bound) {
  const auto *definition = declaration(bound.predicate);
  if (!definition || definition->parameters.size() != bound.arguments.size())
    return fail("source.capability",
                "unknown capability or argument count differs", bound.span);
  for (unsigned i = 0; i < bound.arguments.size(); ++i) {
    if (!chargeType(bound.arguments[i], bound.span))
      return false;
    if (!matchesStaticSort(bound.arguments[i], sort(definition->parameters[i])))
      return fail("source.capability", "capability argument has the wrong sort",
                  bound.span);
  }
  return true;
}
bool Semantics::entails(const Declaration *context, const CapabilityBound &goal,
                        StringRef code) {
  if (!capabilityFormation(goal))
    return false;
  auto closed = [&](const CapabilityBound &bound) {
    return llvm::none_of(bound.arguments,
                         [&](const auto &t) { return symbolic(t); });
  };
  if (closed(goal)) {
    const auto *definition = declaration(goal.predicate);
    std::vector<std::string> identities;
    std::vector<unsigned> positions;
    for (unsigned i = 0; i < goal.arguments.size(); ++i) {
      auto identity =
          kernelArgument(goal.arguments[i], sort(definition->parameters[i]));
      if (!identity)
        return fail(code, toString(identity.takeError()), goal.span);
      identities.push_back(std::move(*identity));
      positions.push_back(i);
    }
    auto predicate = requirements::Predicate::holds(goal.predicate, positions);
    if (auto error =
            protocol::checkClosedRequirements({predicate}, identities)) {
      consumeError(std::move(error));
      return fail(code,
                  "closed catalog capability does not hold: " +
                      display(goal.predicate),
                  goal.span);
    }
    return true;
  }
  std::map<std::string, unsigned> indices;
  std::vector<requirements::Term> terms;
  std::vector<requirements::Predicate> assumptions;
  auto assume = [&](requirements::Predicate predicate) {
    if (assumptions.size() == 1024)
      return fail("source.limit", "capability assumption limit exceeded",
                  goal.span);
    assumptions.push_back(std::move(predicate));
    return true;
  };
  auto intern = [&](const Type &type) -> std::optional<unsigned> {
    if (!chargeType(type, goal.span))
      return {};
    auto key = typeIdentity(type);
    if (!charge(key.size(), goal.span))
      return {};
    if (auto found = indices.find(key); found != indices.end())
      return found->second;
    if (terms.size() == 128) {
      fail("source.limit", "capability term limit exceeded", goal.span);
      return {};
    }
    unsigned index = terms.size();
    indices.emplace(std::move(key), index);
    // Equality is the source normal form used to intern the term. The finite
    // checker needs short unique labels, not a second copy of that identity.
    terms.push_back({std::to_string(index)});
    auto domain = domainSort(type);
    if ((domain == "Field" || domain == "Group") &&
        !assume(requirements::Predicate::holds(domain.str(), {index})))
      return {};
    return index;
  };
  auto predicate = [&](const CapabilityBound &bound)
      -> std::optional<requirements::Predicate> {
    std::vector<unsigned> arguments;
    for (const auto &argument : bound.arguments) {
      auto position = intern(argument);
      if (!position)
        return {};
      arguments.push_back(*position);
    }
    return requirements::Predicate::holds(bound.predicate,
                                          std::move(arguments));
  };
  auto required = predicate(goal);
  if (!required)
    return false;
  if (context)
    for (const auto &bound : context->capabilityBounds) {
      assert(!closed(bound) && "closed requirements are checked at formation");
      if (!charge(bound.predicate.size() + 1, goal.span))
        return false;
      auto given = predicate(bound);
      if (!given)
        return false;
      if (!assume(std::move(*given)))
        return false;
    }
  uint64_t n = terms.size(), positions = required->arguments.size();
  for (const auto &assumption : assumptions)
    positions += assumption.arguments.size();
  uint64_t rules = protocol::boundCapabilityRules().size();
  // Flat interned roots and no equality assumptions leave only reflexivity.
  // Charge the quadratic scans, argument normalization and unary-rule worklist;
  // the shared checker does not enumerate a relation universe in this mode.
  if (!charge(2 * n * n + positions * n +
                  (assumptions.size() + n * rules) * (rules + 1),
              goal.span))
    return false;
  auto proof = requirements::derive(
      terms, assumptions, protocol::boundCapabilityRules(), {*required});
  if (!proof)
    return accept(proof.takeError(), goal.span);
  return proof->goals.front().has_value() ||
         fail(code,
              "declared bounds do not establish catalog capability: " +
                  display(goal.predicate),
              goal.span);
}
} // namespace zkc::language::detail
