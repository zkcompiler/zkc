#include "Internal.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"
#include <set>

using namespace llvm;
namespace zkc::claims {
namespace {
// Preflight caller-owned typed records before encoding or building indexes.
// The codec then checks the same schema for both programmatic and file clients.
Error budget(const Contract &c) {
  size_t bytes = 0, items = 0;
  bool valid = true;
  auto str = [&](const std::string &s) {
    if (s.empty() || s.size() > 4096 || bytes > 1024 * 1024 - s.size() ||
        !json::isUTF8(s) || s.find('\0') != std::string::npos)
      valid = false;
    else
      bytes += s.size();
  };
  auto list = [&](const auto &values) {
    if (values.size() > maxRecords || items > maxItems - values.size())
      valid = false;
    else
      items += values.size();
  };
  auto strings = [&](const source::Names &values) {
    list(values);
    if (valid)
      for (const auto &s : values)
        str(s);
  };
  str(c.sourceDigest);
  str(c.entry);
  str(c.validator);
  list(c.kinds);
  list(c.claims);
  list(c.terminals);
  list(c.laws);
  list(c.rules);
  strings(c.required);
  if (!valid)
    return error("claim-contract-format");
  for (const auto &k : c.kinds) {
    str(k.name);
    strings(k.types);
    str(k.meaning);
  }
  for (const auto &p : c.claims) {
    str(p.name);
    str(p.kind);
    strings(p.values);
  }
  for (const auto &t : c.terminals) {
    str(t.claim);
    str(t.guard);
  }
  for (const auto &l : c.laws) {
    str(l.name);
    str(l.premise);
  }
  for (const auto &r : c.rules) {
    str(r.name);
    str(r.law);
    str(r.invocation);
    str(r.callee);
    strings(r.inputs);
    strings(r.outputs);
    strings(r.guards);
    strings(r.premises);
    str(r.conclusion);
  }
  return valid ? Error::success() : error("claim-contract-format");
}
bool within(StringRef path, StringRef invocation) {
  return path.starts_with(invocation) && path.size() > invocation.size() &&
         path[invocation.size()] == '/';
}
} // namespace
Expected<Checked> admit(const source::Module &module,
                        const Contract &contract) {
  if (auto e = budget(contract))
    return e;
  auto decoded = decodeContract(encode(contract));
  if (!decoded)
    return decoded.takeError();
  auto actual = trace(module, contract.entry);
  if (!actual)
    return actual.takeError();
  if (actual->digest != contract.sourceDigest)
    return error("claim-source-mismatch");
  if (!is_contained(actual->roles, contract.validator))
    return error("claim-validator");
  Checked out;
  out.source = std::move(*actual);
  out.contractDigest =
      digest("zkc.execution-claims.contract/1\n", encode(contract));
  std::map<std::string, source::Names> kinds{{"guard", {"bool"}}};
  for (const auto &k : contract.kinds) {
    if (!kinds.emplace(k.name, k.types).second)
      return error("claim-kind");
    for (const auto &type : k.types) {
      auto parsed = protocol::parseBoundType(type, false);
      if (!parsed) {
        consumeError(parsed.takeError());
        return error("claim-kind");
      }
      if (protocol::affine(type) ||
          protocol::typeKind(type) == "opening_state" ||
          protocol::typeKind(type) == "opening_states")
        return error("claim-resource-subject");
    }
  }
  std::map<std::pair<std::string, source::Names>, uint32_t> propositions;
  std::map<std::string, const Claim *> claims;
  for (const auto &p : contract.claims) {
    const auto kind = kinds.find(p.kind);
    if (kind == kinds.end())
      return error("claim-kind");
    if (kind->second.size() != p.values.size())
      return error("claim-subject");
    for (size_t i = 0; i < p.values.size(); ++i) {
      auto value = out.source.values.find(p.values[i]);
      if (value == out.source.values.end() ||
          value->second.type != kind->second[i])
        return error("claim-subject");
      if (protocol::affine(value->second.type) ||
          protocol::typeKind(value->second.type) == "opening_state" ||
          protocol::typeKind(value->second.type) == "opening_states")
        return error("claim-resource-subject");
    }
    auto [same, inserted] = propositions.emplace(
        std::make_pair(p.kind, p.values), propositions.size());
    (void)inserted;
    if (!out.claimIds.emplace(p.name, same->second).second)
      return error("claim-duplicate");
    claims.emplace(p.name, &p);
  }
  for (const auto &name : contract.required) {
    auto id = out.claimIds.find(name);
    if (id == out.claimIds.end())
      return error("claim-reference");
    out.required.push_back(id->second);
  }
  auto guard = [&](const std::string &path) -> const source::ExecutionGuard * {
    auto g = out.source.guards.find(path);
    return g != out.source.guards.end() && g->second.role == contract.validator
               ? &g->second
               : nullptr;
  };
  for (const auto &t : contract.terminals) {
    const auto p = claims.find(t.claim);
    const auto *g = guard(t.guard);
    if (p == claims.end() || !g || p->second->kind != "guard" ||
        p->second->values != source::Names{g->value})
      return error("claim-guard");
    out.facts.push_back(out.claimIds.at(t.claim));
  }
  std::set<std::string> laws;
  for (const auto &l : contract.laws)
    if (!laws.insert(l.name).second)
      return error("claim-duplicate");
  for (const auto &r : contract.rules) {
    if (!laws.count(r.law))
      return error("claim-authority");
    auto invocation = out.source.invocations.find(r.invocation);
    if (invocation == out.source.invocations.end() ||
        invocation->second.callee != r.callee ||
        invocation->second.inputs != r.inputs ||
        invocation->second.outputs != r.outputs)
      return error("claim-invocation");
    for (const auto &path : r.guards)
      if (!guard(path) || !within(path, r.invocation))
        return error("claim-guard");
    analysis::ReductionRule rule;
    for (const auto &p : r.premises) {
      auto id = out.claimIds.find(p);
      if (id == out.claimIds.end())
        return error("claim-reference");
      rule.premises.push_back(id->second);
    }
    auto conclusion = out.claimIds.find(r.conclusion);
    if (conclusion == out.claimIds.end())
      return error("claim-reference");
    if (claims.at(r.conclusion)->kind == "guard")
      return error("claim-guard");
    rule.conclusion = conclusion->second;
    if (!out.ruleIds.emplace(r.name, out.rules.size()).second)
      return error("claim-duplicate");
    out.rules.push_back(std::move(rule));
  }
  return out;
}
Expected<std::vector<uint32_t>> steps(const Checked &checked,
                                      const Certificate &certificate) {
  if (certificate.sourceDigest != checked.source.digest ||
      certificate.contractDigest != checked.contractDigest)
    return error("claim-certificate-mismatch");
  if (certificate.steps.size() > maxRecords)
    return error("claim-certificate-format");
  std::vector<uint32_t> result;
  size_t premises = 0;
  for (const auto &name : certificate.steps) {
    if (name.empty() || name.size() > 4096)
      return error("claim-certificate-format");
    auto rule = checked.ruleIds.find(name);
    if (rule == checked.ruleIds.end())
      return error("claim-rule");
    // claim.apply materializes every premise as an SSA operand. A compact
    // certificate must not expand repeated wide rules beyond the trace budget.
    auto count = checked.rules[rule->second].premises.size();
    if (count > maxItems - premises)
      return error("claim-analysis-limit");
    premises += count;
    result.push_back(rule->second);
  }
  if (auto e =
          analysis::checkObligations(checked.claimIds.size(), checked.required,
                                     checked.facts, checked.rules, result))
    return e;
  return result;
}
Expected<Certificate> derive(const source::Module &module,
                             const Contract &contract) {
  auto checked = admit(module, contract);
  if (!checked)
    return checked.takeError();
  auto proof =
      analysis::deriveObligations(checked->claimIds.size(), checked->required,
                                  checked->facts, checked->rules);
  if (!proof)
    return proof.takeError();
  Certificate certificate{checked->source.digest, checked->contractDigest, {}};
  for (auto index : *proof)
    certificate.steps.push_back(contract.rules[index].name);
  return certificate;
}
Error check(const source::Module &module, const Contract &contract,
            const Certificate &certificate) {
  auto checked = admit(module, contract);
  if (!checked)
    return checked.takeError();
  auto proof = steps(*checked, certificate);
  return proof ? Error::success() : proof.takeError();
}
} // namespace zkc::claims
