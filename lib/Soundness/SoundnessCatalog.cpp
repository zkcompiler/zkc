//===- SoundnessCatalog.cpp - Immutable executable declarations ---------===//
#include "zkc/Soundness/SoundnessCatalog.h"

#include "SoundnessSchemaValidation.h"

#include "llvm/ADT/Twine.h"
#include "llvm/Support/Error.h"

#include <algorithm>
#include <set>
#include <string>
#include <utility>

namespace zkc::soundness {
namespace {

llvm::Error catalogError(const llvm::Twine &location,
                         const llvm::Twine &detail) {
  return llvm::createStringError("soundness catalog " + location + ": " +
                                 detail);
}

bool validExactRef(const ExactRef &ref) {
  return !ref.id.empty() && !ref.sourceRevision.empty();
}

bool validValueSort(ValueSort sort) {
  switch (sort) {
  case ValueSort::Integer:
  case ValueSort::Rational:
  case ValueSort::String:
  case ValueSort::Boolean:
  case ValueSort::Subject:
  case ValueSort::ReductionContract:
  case ValueSort::PathTransition:
  case ValueSort::RoundAdjacency:
  case ValueSort::AlgebraInstance:
  case ValueSort::SrsInstance:
  case ValueSort::FriDomainInstance:
    return true;
  }
  return false;
}

bool validIndexShape(const SecurityIndex &index) {
  switch (index.track) {
  case SecurityTrack::Soundness:
  case SecurityTrack::Knowledge:
  case SecurityTrack::Completeness:
    break;
  default:
    return false;
  }
  if ((index.notion == SecurityNotion::Completeness) !=
      (index.track == SecurityTrack::Completeness))
    return false;
  switch (index.notion) {
  case SecurityNotion::SpecialSoundness:
  case SecurityNotion::ComputationalSpecialSoundness:
    return index.variant.empty() && index.model.empty();
  case SecurityNotion::RoundByRound:
  case SecurityNotion::StateRestoration:
    return !index.variant.empty() && index.model.empty();
  case SecurityNotion::FiatShamir:
    return !index.variant.empty() && index.model == "duplex";
  case SecurityNotion::Completeness:
    return index.variant.empty() && index.model.empty();
  }
  return false;
}

llvm::Error validateSchemas(const SchemaContext &schemas) {
  for (size_t index = 0; index < schemas.securityIndices.size(); ++index) {
    const SecurityIndex &value = schemas.securityIndices[index];
    if (!validIndexShape(value))
      return catalogError("schemas.security_indices[" + llvm::Twine(index) +
                              "]",
                          "index has an impossible kernel shape");
    if (std::find(schemas.securityIndices.begin(),
                  schemas.securityIndices.begin() + index,
                  value) != schemas.securityIndices.begin() + index)
      return catalogError("schemas.security_indices[" + llvm::Twine(index) +
                              "]",
                          "duplicate security index");
  }

  for (const auto &[id, schema] : schemas.subjectSchemas) {
    if (!detail::validSubjectSchema(id, schema))
      return catalogError("schemas.subjects." + id,
                          "subject schema is not a canonical kernel entry");
  }

  for (const auto &[id, game] : schemas.primitiveGames) {
    if (!validExactRef(game.ref) || game.ref.id != id)
      return catalogError("schemas.primitive_games." + id,
                          "map key and exact game reference disagree");
    if (std::any_of(game.instanceArgumentTypes.begin(),
                    game.instanceArgumentTypes.end(),
                    [](ValueSort sort) { return !validValueSort(sort); }))
      return catalogError("schemas.primitive_games." + id,
                          "primitive game has an unknown argument sort");
    std::set<std::string, std::less<>> resources;
    for (const TypedDeclaration &resource : game.resources) {
      if (resource.name.empty() || !resources.insert(resource.name).second)
        return catalogError("schemas.primitive_games." + id + ".resources",
                            "empty or duplicate resource declaration");
      if (resource.sort != ValueSort::Integer &&
          resource.sort != ValueSort::Rational)
        return catalogError("schemas.primitive_games." + id + ".resources",
                            "game resources must be numeric");
    }
  }

  for (const auto &[id, decider] : schemas.machineDeciders) {
    if (!detail::validMachineDecider(id, decider))
      return catalogError("schemas.machine_deciders." + id,
                          "machine decider is not a canonical kernel entry");
  }

  for (const auto &[id, proposition] : schemas.propositions) {
    if (!validExactRef(proposition.ref) || proposition.ref.id != id)
      return catalogError("schemas.propositions." + id,
                          "map key and exact proposition reference disagree");
    if (std::any_of(proposition.argumentTypes.begin(),
                    proposition.argumentTypes.end(),
                    [](ValueSort sort) { return !validValueSort(sort); }))
      return catalogError("schemas.propositions." + id,
                          "proposition has an unknown argument sort");
  }
  return llvm::Error::success();
}

} // namespace

llvm::Expected<SoundnessCatalog> freezeSoundnessCatalog(
    SchemaContext schemas,
    std::map<std::string, SoundnessRule, std::less<>> rules,
    std::map<std::string, RuleBinding, std::less<>> bindings) {
  if (llvm::Error error = validateSchemas(schemas))
    return std::move(error);

  for (const auto &[id, rule] : rules) {
    if (id.empty() || rule.ref.id != id)
      return catalogError("rules." + id,
                          "map key and exact rule reference disagree");
    RuleWfResult wf = checkRuleWellFormed(schemas, rule);
    if (!wf.accepted())
      return catalogError("rules." + id + "." + wf.refusal->location,
                          llvm::Twine(ruleWfRefusalCodeName(wf.refusal->code)) +
                              ": " + wf.refusal->detail);
  }

  for (const auto &[id, binding] : bindings) {
    if (id.empty() || binding.ref.id != id)
      return catalogError("bindings." + id,
                          "map key and exact binding reference disagree");
    auto rule = rules.find(binding.ruleRef.id);
    if (rule == rules.end() || rule->second.ref != binding.ruleRef)
      return catalogError("bindings." + id + ".rule_ref",
                          "binding names no exact rule in this catalog");
    RuleWfResult wf =
        checkRuleBindingWellFormed(schemas, rule->second, binding);
    if (!wf.accepted())
      return catalogError("bindings." + id + "." + wf.refusal->location,
                          llvm::Twine(ruleWfRefusalCodeName(wf.refusal->code)) +
                              ": " + wf.refusal->detail);
  }

  return SoundnessCatalog(std::move(schemas), std::move(rules),
                          std::move(bindings));
}

} // namespace zkc::soundness
