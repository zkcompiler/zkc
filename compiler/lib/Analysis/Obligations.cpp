#include "zkc/Analysis/Obligations.h"
#include "zkc/Support/Json.h"
#include "llvm/ADT/STLExtras.h"

using namespace llvm;

namespace zkc::analysis {
namespace {
Error refused(StringRef code) { return zkc::error(code); }

// Bound storage before allocating a claim-indexed worklist. This is an analysis
// resource limit, not a restriction on the semantic universe of propositions.
constexpr uint32_t maxClaims = 1U << 20;
constexpr size_t maxRules = 1U << 20;
constexpr size_t maxPremises = 1U << 22;

Error validate(uint32_t claimCount, ArrayRef<ClaimId> required,
               ArrayRef<ClaimId> facts, ArrayRef<ReductionRule> rules) {
  if (claimCount > maxClaims || rules.size() > maxRules ||
      required.size() > maxClaims || facts.size() > maxClaims)
    return refused("claim-analysis-limit");
  auto valid = [claimCount](ClaimId id) { return id < claimCount; };
  if (!all_of(required, valid) || !all_of(facts, valid))
    return refused("claim-index");
  size_t premises = 0;
  for (const auto &rule : rules) {
    if (rule.premises.size() > maxPremises - premises)
      return refused("claim-analysis-limit");
    premises += rule.premises.size();
    if (!valid(rule.conclusion) || !all_of(rule.premises, valid))
      return refused("claim-index");
  }
  return Error::success();
}

Error covered(ArrayRef<ClaimId> required, const std::vector<bool> &available) {
  if (!all_of(required, [&](ClaimId id) { return available[id]; }))
    return refused("claim-unresolved");
  return Error::success();
}
} // namespace

Error checkObligations(uint32_t claimCount, ArrayRef<ClaimId> required,
                       ArrayRef<ClaimId> facts, ArrayRef<ReductionRule> rules,
                       ArrayRef<uint32_t> certificate) {
  if (auto error = validate(claimCount, required, facts, rules))
    return error;
  if (certificate.size() > maxRules)
    return refused("claim-analysis-limit");
  // Bound work over the expanded certificate, not only the stored rule table.
  // Logical reuse permits repeated rules, including ones with many premises.
  size_t premises = 0;
  for (uint32_t index : certificate) {
    if (index >= rules.size())
      return refused("claim-rule-index");
    if (rules[index].premises.size() > maxPremises - premises)
      return refused("claim-analysis-limit");
    premises += rules[index].premises.size();
  }
  std::vector<bool> available(claimCount, false);
  for (auto fact : facts)
    available[fact] = true;
  for (uint32_t index : certificate) {
    const auto &rule = rules[index];
    if (!all_of(rule.premises, [&](ClaimId id) { return available[id]; }))
      return refused("claim-premise-unavailable");
    available[rule.conclusion] = true;
  }
  return covered(required, available);
}

Expected<ObligationCertificate>
deriveObligations(uint32_t claimCount, ArrayRef<ClaimId> required,
                  ArrayRef<ClaimId> facts, ArrayRef<ReductionRule> rules) {
  if (auto error = validate(claimCount, required, facts, rules))
    return error;
  std::vector<bool> available(claimCount, false);
  std::vector<std::vector<uint32_t>> waiting(claimCount);
  std::vector<size_t> missing(rules.size());
  std::vector<ClaimId> worklist;
  ObligationCertificate certificate;

  auto add = [&](ClaimId id) {
    if (!available[id]) {
      available[id] = true;
      worklist.push_back(id);
    }
  };
  // Register every occurrence before adding facts. Repeated premises are
  // logically idempotent; processing their one fact satisfies all occurrences.
  for (size_t index = 0; index < rules.size(); ++index) {
    missing[index] = rules[index].premises.size();
    for (ClaimId premise : rules[index].premises)
      waiting[premise].push_back(static_cast<uint32_t>(index));
  }
  for (ClaimId fact : facts)
    add(fact);
  auto apply = [&](uint32_t index) {
    if (!available[rules[index].conclusion]) {
      certificate.push_back(index);
      add(rules[index].conclusion);
    }
  };
  // A premise-free rule is usable only because the caller admitted its law.
  // It is not an implicit axiom installed by the closure algorithm.
  for (size_t index = 0; index < rules.size(); ++index)
    if (!missing[index])
      apply(static_cast<uint32_t>(index));
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor)
    for (uint32_t index : waiting[worklist[cursor]])
      if (--missing[index] == 0)
        apply(index);

  if (auto error = covered(required, available))
    return error;
  if (auto error =
          checkObligations(claimCount, required, facts, rules, certificate))
    return error;
  return certificate;
}
} // namespace zkc::analysis
