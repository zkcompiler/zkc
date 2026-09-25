#include "zkc/Compiler/Requirements.h"
#include "RequirementChecks.h"
#include "zkc/Target/Json.h"
#include "llvm/ADT/STLExtras.h"
#include <map>
#include <set>
#include <tuple>
#include <utility>

using namespace llvm;
namespace zkc::requirements {

Predicate Predicate::equal(unsigned left, unsigned right) {
  return {Kind::Equal, {}, {left, right}};
}
Predicate Predicate::holds(std::string relation,
                           std::vector<unsigned> arguments) {
  return {Kind::Relation, std::move(relation), std::move(arguments)};
}
bool Predicate::operator==(const Predicate &other) const {
  return kind == other.kind && relation == other.relation &&
         arguments == other.arguments;
}

namespace {
Error invalid(StringRef code) { return zkc::error(code); }

// Indexed application DAGs can denote exponentially large trees. Independent
// proof replay uses structural terms, so bound their expanded work as well as
// the transport's node count. Called only after backward indices are checked.
Expected<std::vector<uint64_t>> termWork(ArrayRef<Term> terms) {
  std::vector<uint64_t> weights;
  uint64_t total = 0;
  for (const auto &term : terms) {
    uint64_t weight = 1;
    if (term.parent)
      weight += weights[*term.parent];
    if (term.arguments)
      for (auto child : *term.arguments)
        weight += weights[child];
    total += weight;
    if (total > 16384)
      return invalid("requirements-work-limit");
    weights.push_back(weight);
  }
  return weights;
}
uint64_t predicateWork(const Predicate &p, ArrayRef<uint64_t> weights) {
  uint64_t work = 1;
  for (auto argument : p.arguments)
    work += weights[argument];
  return work;
}

class Closure {
  ArrayRef<Term> terms;
  ArrayRef<Implication> implications;
  Result result;
  std::vector<std::vector<std::optional<unsigned>>> equalities;
  std::map<std::pair<std::string, std::vector<unsigned>>, unsigned> relations;

  unsigned append(Predicate predicate, Rule rule,
                  std::vector<unsigned> premises = {},
                  unsigned declaration = 0) {
    unsigned index = result.steps.size();
    result.steps.push_back(
        {std::move(predicate), rule, std::move(premises), declaration});
    return index;
  }
  bool connect(unsigned left, unsigned right, Rule rule,
               std::vector<unsigned> premises = {}, unsigned declaration = 0) {
    if (equalities[left][right])
      return false;
    unsigned proof = append(Predicate::equal(left, right), rule,
                            std::move(premises), declaration);
    equalities[left][right] = proof;
    if (left != right)
      equalities[right][left] =
          append(Predicate::equal(right, left), Rule::Symmetry, {proof});
    return true;
  }
  std::vector<unsigned> normalize(ArrayRef<unsigned> arguments) const {
    std::vector<unsigned> out;
    for (unsigned term : arguments) {
      unsigned representative = 0;
      while (!equalities[term][representative])
        ++representative;
      out.push_back(representative);
    }
    return out;
  }
  unsigned transport(unsigned proof, const Predicate &target) {
    const auto original = result.steps[proof].conclusion;
    if (original == target)
      return proof;
    std::vector<unsigned> premises{proof};
    for (auto [left, right] : zip(original.arguments, target.arguments))
      premises.push_back(*equalities[left][right]);
    return append(target, Rule::Transport, std::move(premises));
  }

public:
  Closure(ArrayRef<Term> terms, ArrayRef<Implication> implications)
      : terms(terms), implications(implications),
        equalities(terms.size(),
                   std::vector<std::optional<unsigned>>(terms.size())) {}

  Result run(ArrayRef<Predicate> assumptions, ArrayRef<Predicate> goals) {
    for (unsigned i = 0; i < terms.size(); ++i)
      connect(i, i, Rule::Reflexivity);
    for (auto [index, p] : enumerate(assumptions))
      if (p.kind == Predicate::Kind::Equal)
        connect(p.arguments[0], p.arguments[1], Rule::Assumption, {}, index);

    // Reachability closure followed by congruence. New congruences may connect
    // existing paths; repeat to a fixed point without generating new terms.
    bool changed;
    do {
      changed = false;
      for (unsigned k = 0; k < terms.size(); ++k)
        for (unsigned i = 0; i < terms.size(); ++i)
          if (equalities[i][k])
            for (unsigned j = 0; j < terms.size(); ++j)
              if (!equalities[i][j] && equalities[k][j])
                changed |= connect(i, j, Rule::Transitivity,
                                   {*equalities[i][k], *equalities[k][j]});
      for (unsigned i = 0; i < terms.size(); ++i)
        if (terms[i].parent)
          for (unsigned j = i + 1; j < terms.size(); ++j)
            if (terms[j].parent && terms[i].name == terms[j].name &&
                !equalities[i][j] &&
                equalities[*terms[i].parent][*terms[j].parent])
              changed |=
                  connect(i, j, Rule::Projection,
                          {*equalities[*terms[i].parent][*terms[j].parent]});
      for (unsigned i = 0; i < terms.size(); ++i)
        if (terms[i].arguments)
          for (unsigned j = i + 1; j < terms.size(); ++j) {
            if (!terms[j].arguments || terms[i].name != terms[j].name ||
                terms[i].arguments->size() != terms[j].arguments->size() ||
                equalities[i][j])
              continue;
            std::vector<unsigned> premises;
            for (auto [a, b] : zip(*terms[i].arguments, *terms[j].arguments)) {
              if (!equalities[a][b])
                break;
              premises.push_back(*equalities[a][b]);
            }
            if (premises.size() == terms[i].arguments->size())
              changed |= connect(i, j, Rule::Application, std::move(premises));
          }
    } while (changed);

    for (auto [index, p] : enumerate(assumptions)) {
      if (p.kind != Predicate::Kind::Relation)
        continue;
      auto key = std::make_pair(p.relation, normalize(p.arguments));
      if (relations.count(key))
        continue;
      unsigned proof = append(p, Rule::Assumption, {}, index);
      proof = transport(proof, Predicate::holds(key.first, key.second));
      relations.emplace(std::move(key), proof);
    }
    // A worklist keeps cycles/duplicate implication declarations harmless.
    std::vector<unsigned> work;
    for (const auto &[key, proof] : relations) {
      (void)key;
      work.push_back(proof);
    }
    for (size_t cursor = 0; cursor < work.size(); ++cursor) {
      unsigned proof = work[cursor];
      const auto p = result.steps[proof].conclusion;
      if (p.arguments.size() != 1)
        continue;
      for (auto [index, rule] : enumerate(implications)) {
        auto key = std::make_pair(rule.conclusion, p.arguments);
        if (rule.premise != p.relation || relations.count(key))
          continue;
        unsigned next = append(Predicate::holds(rule.conclusion, p.arguments),
                               Rule::Implication, {proof}, index);
        relations.emplace(std::move(key), next);
        work.push_back(next);
      }
    }
    for (const auto &goal : goals) {
      if (goal.kind == Predicate::Kind::Equal) {
        result.goals.push_back(
            equalities[goal.arguments[0]][goal.arguments[1]]);
        continue;
      }
      auto found = relations.find({goal.relation, normalize(goal.arguments)});
      result.goals.push_back(
          found == relations.end()
              ? std::nullopt
              : std::optional<unsigned>(transport(found->second, goal)));
    }
    return std::move(result);
  }
};
} // namespace

Error checkFormation(ArrayRef<Term> terms, ArrayRef<Predicate> assumptions,
                     ArrayRef<Implication> implications,
                     ArrayRef<Predicate> goals) {
  // These bounds make worst-case closure and certificate size predictable.
  if (terms.size() > 128 || assumptions.size() > 1024 || goals.size() > 1024 ||
      implications.size() > 128)
    return invalid("requirements-limit");
  std::set<std::tuple<std::optional<unsigned>, std::string,
                      std::optional<std::vector<unsigned>>>>
      identities;
  for (unsigned index = 0; index < terms.size(); ++index) {
    const auto &term = terms[index];
    if (term.name.empty() || term.name.size() > 256 ||
        (term.parent && *term.parent >= index) ||
        (term.parent && term.arguments) ||
        (term.arguments &&
         (term.arguments->size() > 16 ||
          !all_of(*term.arguments,
                  [index = index](unsigned a) { return a < index; }))) ||
        !identities.emplace(term.parent, term.name, term.arguments).second)
      return invalid("requirements-term");
  }
  auto valid = [&](const Predicate &p) {
    return (p.kind == Predicate::Kind::Equal ||
            p.kind == Predicate::Kind::Relation) &&
           p.arguments.size() <= 16 &&
           all_of(p.arguments, [&](unsigned a) { return a < terms.size(); }) &&
           (p.kind == Predicate::Kind::Equal
                ? p.arguments.size() == 2 && p.relation.empty()
                : !p.relation.empty() && p.relation != "=" &&
                      p.relation.size() <= 256);
  };
  if (!all_of(assumptions, valid) || !all_of(goals, valid))
    return invalid("requirements-predicate");
  auto weights = termWork(terms);
  if (!weights)
    return weights.takeError();
  uint64_t work = 0;
  for (const auto &p : assumptions)
    work += predicateWork(p, *weights);
  for (const auto &p : goals)
    work += predicateWork(p, *weights);
  if (work > 262144)
    return invalid("requirements-work-limit");
  for (const auto &rule : implications)
    if (rule.premise.empty() || rule.conclusion.empty() ||
        rule.premise == "=" || rule.conclusion == "=" ||
        rule.premise.size() > 256 || rule.conclusion.size() > 256)
      return invalid("requirements-implication");
  return Error::success();
}

Error checkCertificate(ArrayRef<Term> terms, ArrayRef<Predicate> assumptions,
                       ArrayRef<Implication> implications,
                       ArrayRef<Predicate> goals, const Result &certificate) {
  if (auto e = checkFormation(terms, assumptions, implications, goals))
    return e;
  if (certificate.steps.size() > 65536)
    return invalid("requirements-certificate-limit");
  if (certificate.goals.size() != goals.size())
    return invalid("requirements-goal-count");
  auto weights = termWork(terms);
  if (!weights)
    return weights.takeError();
  uint64_t work = 0;
  for (auto indexed : enumerate(certificate.steps)) {
    const auto index = indexed.index();
    const auto &step = indexed.value();
    if (auto e = checkFormation(terms, {step.conclusion}, implications, {}))
      return e;
    work += predicateWork(step.conclusion, *weights);
    if (work > 262144)
      return invalid("requirements-work-limit");
    if (step.premises.size() > 17 ||
        !all_of(step.premises, [&](unsigned p) { return p < index; }) ||
        (step.rule != Rule::Assumption && step.rule != Rule::Implication &&
         step.declaration != 0))
      return invalid("requirements-invalid-derivation");
    const auto &p = step.conclusion;
    auto premise = [&](unsigned i) -> const Predicate & {
      return certificate.steps[step.premises[i]].conclusion;
    };
    auto pairs = [&](ArrayRef<unsigned> left, ArrayRef<unsigned> right,
                     unsigned offset) {
      if (left.size() != right.size() ||
          step.premises.size() != left.size() + offset)
        return false;
      for (unsigned i = 0; i < left.size(); ++i)
        if (!(premise(i + offset) == Predicate::equal(left[i], right[i])))
          return false;
      return true;
    };
    bool valid = false;
    switch (step.rule) {
    case Rule::Assumption:
      valid = step.premises.empty() && step.declaration < assumptions.size() &&
              p == assumptions[step.declaration];
      break;
    case Rule::Reflexivity:
      valid = step.premises.empty() && p.kind == Predicate::Kind::Equal &&
              p.arguments[0] == p.arguments[1];
      break;
    case Rule::Symmetry:
      valid = step.premises.size() == 1 && p.kind == Predicate::Kind::Equal &&
              premise(0) == Predicate::equal(p.arguments[1], p.arguments[0]);
      break;
    case Rule::Transitivity:
      if (step.premises.size() == 2 && p.kind == Predicate::Kind::Equal &&
          premise(0).kind == Predicate::Kind::Equal)
        valid = premise(0).arguments[0] == p.arguments[0] &&
                premise(1) ==
                    Predicate::equal(premise(0).arguments[1], p.arguments[1]);
      break;
    case Rule::Projection:
    case Rule::Application:
      if (p.kind == Predicate::Kind::Equal) {
        const auto &a = terms[p.arguments[0]], &b = terms[p.arguments[1]];
        if (a.name != b.name)
          break;
        if (step.rule == Rule::Projection)
          valid = a.parent && b.parent && step.premises.size() == 1 &&
                  premise(0) == Predicate::equal(*a.parent, *b.parent);
        else
          valid = a.arguments && b.arguments &&
                  pairs(*a.arguments, *b.arguments, 0);
      }
      break;
    case Rule::Transport:
      if (!step.premises.empty() && p.kind == Predicate::Kind::Relation &&
          premise(0).kind == Predicate::Kind::Relation &&
          premise(0).relation == p.relation)
        valid = pairs(premise(0).arguments, p.arguments, 1);
      break;
    case Rule::Implication:
      if (step.premises.size() == 1 && p.kind == Predicate::Kind::Relation &&
          p.arguments.size() == 1 && step.declaration < implications.size()) {
        const auto &rule = implications[step.declaration];
        valid = p.relation == rule.conclusion &&
                premise(0) == Predicate::holds(rule.premise, p.arguments);
      }
      break;
    }
    if (!valid)
      return invalid("requirements-invalid-derivation");
  }
  for (auto [goal, proof] : zip(goals, certificate.goals))
    if (proof && (*proof >= certificate.steps.size() ||
                  !(certificate.steps[*proof].conclusion == goal)))
      return invalid("requirements-wrong-conclusion");
  return Error::success();
}

Expected<Result> derive(ArrayRef<Term> terms, ArrayRef<Predicate> assumptions,
                        ArrayRef<Implication> implications,
                        ArrayRef<Predicate> goals) {
  if (auto e = checkFormation(terms, assumptions, implications, goals))
    return e;
  auto result = Closure(terms, implications).run(assumptions, goals);
  if (result.steps.size() > 65536)
    return invalid("requirements-certificate-limit");
  auto weights = termWork(terms);
  if (!weights)
    return weights.takeError();
  uint64_t work = 0;
  for (const auto &step : result.steps)
    work += predicateWork(step.conclusion, *weights);
  if (work > 262144)
    return invalid("requirements-work-limit");
  return result;
}
} // namespace zkc::requirements
