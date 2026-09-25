#include "zkc/Compiler/Requirements.h"
#include "zkc/Target/Json.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>

using namespace llvm;
using namespace zkc::requirements;
namespace {
Error invalid() {
  return createStringError(inconvertibleErrorCode(), "requirements-format");
}
Expected<unsigned> index(const json::Value &value) {
  auto digits = zkc::natural(value);
  if (!digits)
    return digits.takeError();
  unsigned n;
  if (StringRef(*digits).getAsInteger(10, n) || n > 65536)
    return invalid();
  return n;
}
Expected<std::vector<unsigned>> indices(const json::Value &value) {
  auto *array = value.getAsArray();
  if (!array || array->size() > 1024)
    return invalid();
  std::vector<unsigned> out;
  for (const auto &v : *array) {
    auto n = index(v);
    if (!n)
      return n.takeError();
    out.push_back(*n);
  }
  return out;
}
Expected<std::vector<Predicate>> predicates(const json::Value &value) {
  auto *array = value.getAsArray();
  if (!array || array->size() > 1024)
    return invalid();
  std::vector<Predicate> out;
  for (const auto &v : *array) {
    auto *p = v.getAsArray();
    if (!p || p->size() != 2 || !(*p)[0].getAsString())
      return invalid();
    auto args = indices((*p)[1]);
    if (!args)
      return args.takeError();
    auto name = *(*p)[0].getAsString();
    out.push_back(
        {name == "=" ? Predicate::Kind::Equal : Predicate::Kind::Relation,
         name == "=" ? "" : name.str(), std::move(*args)});
  }
  return out;
}
json::Array numbers(ArrayRef<unsigned> values) {
  json::Array out;
  for (auto n : values)
    out.push_back(int64_t(n));
  return out;
}
Expected<json::Value> run(const json::Value &value) {
  const auto *request = value.getAsArray();
  if (!request || request->size() != 5 ||
      (*request)[0].getAsString() != "zkc.requirements/1")
    return invalid();
  const auto *rawTerms = (*request)[1].getAsArray();
  const auto *rawRules = (*request)[3].getAsArray();
  if (!rawTerms || !rawRules || rawTerms->size() > 128 ||
      rawRules->size() > 128)
    return invalid();
  std::vector<Term> terms;
  for (const auto &v : *rawTerms) {
    const auto *t = v.getAsArray();
    if (t && t->size() == 3 && (*t)[0].getAsString() == "apply" &&
        (*t)[1].getAsString()) {
      auto args = indices((*t)[2]);
      if (!args)
        return args.takeError();
      terms.push_back(
          {(*t)[1].getAsString()->str(), std::nullopt, std::move(*args)});
      continue;
    }
    if (!t || t->size() != 2 || !(*t)[1].getAsString())
      return invalid();
    std::optional<unsigned> parent;
    if ((*t)[0].kind() != json::Value::Null) {
      auto p = index((*t)[0]);
      if (!p)
        return p.takeError();
      parent = *p;
    }
    terms.push_back({(*t)[1].getAsString()->str(), parent});
  }
  std::vector<Implication> rules;
  for (const auto &v : *rawRules) {
    const auto *r = v.getAsArray();
    if (!r || r->size() != 2 || !(*r)[0].getAsString() ||
        !(*r)[1].getAsString())
      return invalid();
    rules.push_back(
        {(*r)[0].getAsString()->str(), (*r)[1].getAsString()->str()});
  }
  auto assumptions = predicates((*request)[2]);
  if (!assumptions)
    return assumptions.takeError();
  auto goals = predicates((*request)[4]);
  if (!goals)
    return goals.takeError();
  auto result = derive(terms, *assumptions, rules, *goals);
  if (!result)
    return result.takeError();
  if (auto e = checkCertificate(terms, *assumptions, rules, *goals, *result))
    return e;
  json::Array steps, answers;
  constexpr StringLiteral names[] = {"assumption",   "reflexivity", "symmetry",
                                     "transitivity", "projection",  "transport",
                                     "implication",  "application"};
  for (const auto &step : result->steps)
    steps.push_back(
        json::Array{json::Array{step.conclusion.kind == Predicate::Kind::Equal
                                    ? "="
                                    : step.conclusion.relation,
                                numbers(step.conclusion.arguments)},
                    names[unsigned(step.rule)], numbers(step.premises),
                    int64_t(step.declaration)});
  for (const auto &goal : result->goals)
    answers.push_back(goal ? json::Value(int64_t(*goal))
                           : json::Value(nullptr));
  return json::Value(json::Array{"zkc.requirements-certificate/1",
                                 std::move(steps), std::move(answers)});
}
// Run with --self-test. Failures remain named even in Release/NDEBUG builds.
Error selfTest() {
  std::vector<Term> terms{{"F"},
                          {"G"},
                          {"S"},
                          {"Poly", {}, std::vector<unsigned>{0, 2}},
                          {"Poly", {}, std::vector<unsigned>{1, 2}},
                          {"Poly", {}, std::vector<unsigned>{2, 1}},
                          {"Other", {}, std::vector<unsigned>{1, 2}},
                          {"Commitment", 3},
                          {"Commitment", 4},
                          {"Seal", {}, std::vector<unsigned>{}},
                          {"Seal"}};
  std::vector<Predicate> assumptions{Predicate::equal(0, 1),
                                     Predicate::holds("Ready", {7, 2})};
  std::vector<Predicate> goals{Predicate::equal(3, 4),
                               Predicate::equal(3, 5),
                               Predicate::equal(3, 6),
                               Predicate::equal(0, 2),
                               Predicate::equal(0, 1),
                               Predicate::equal(7, 8),
                               Predicate::holds("Ready", {8, 2}),
                               Predicate::equal(9, 10)};
  auto result = derive(terms, assumptions, {}, goals);
  if (!result)
    return result.takeError();
  std::vector<bool> expected{true, false, false, false,
                             true, true,  true,  false};
  for (unsigned i = 0; i < expected.size(); ++i)
    if (result->goals[i].has_value() != expected[i])
      return createStringError(inconvertibleErrorCode(),
                               "static application answers");
  if (auto e = checkCertificate(terms, assumptions, {}, goals, *result))
    return e;
  auto refused = [](Error e, StringRef code) -> Error {
    if (!e)
      return createStringError(inconvertibleErrorCode(),
                               "expected refusal: " + code);
    auto actual = toString(std::move(e));
    if (actual != code)
      return createStringError(inconvertibleErrorCode(),
                               "wrong refusal: " + actual);
    return Error::success();
  };
  unsigned application = *result->goals[0];
  for (std::vector<unsigned> bad :
       {std::vector<unsigned>{}, std::vector<unsigned>{application},
        std::vector<unsigned>{65536, 0}, std::vector<unsigned>{0, 0, 0}}) {
    auto damaged = *result;
    damaged.steps[application].premises = std::move(bad);
    if (auto e =
            refused(checkCertificate(terms, assumptions, {}, goals, damaged),
                    "requirements-invalid-derivation"))
      return e;
  }
  {
    auto damaged = *result;
    std::swap(damaged.steps[application].premises[0],
              damaged.steps[application].premises[1]);
    if (auto e =
            refused(checkCertificate(terms, assumptions, {}, goals, damaged),
                    "requirements-invalid-derivation"))
      return e;
  }
  for (unsigned target : {5u, 6u, 0u}) {
    auto damaged = *result;
    damaged.steps[application].conclusion = Predicate::equal(3, target);
    // All steps must replay, even with no goal proofs requested.
    damaged.goals.assign(goals.size(), std::nullopt);
    if (auto e =
            refused(checkCertificate(terms, assumptions, {}, goals, damaged),
                    "requirements-invalid-derivation"))
      return e;
  }
  {
    auto damaged = *result;
    damaged.steps[application].declaration = 1;
    if (auto e =
            refused(checkCertificate(terms, assumptions, {}, goals, damaged),
                    "requirements-invalid-derivation"))
      return e;
    damaged = *result;
    damaged.goals[0] = 0;
    if (auto e =
            refused(checkCertificate(terms, assumptions, {}, goals, damaged),
                    "requirements-wrong-conclusion"))
      return e;
  }
  for (const Term &bad :
       std::vector<Term>{{"", {}, std::vector<unsigned>{0}},
                         {std::string(257, 'x'), {}, std::vector<unsigned>{0}},
                         {"Poly", {}, std::vector<unsigned>{3}},
                         {"Poly", {}, std::vector<unsigned>{4}},
                         {"Poly", 0, std::vector<unsigned>{0}},
                         {"Poly", {}, std::vector<unsigned>(17, 0)},
                         {"F"}}) {
    auto malformed = terms;
    malformed[3] = bad;
    auto answer = derive(malformed, assumptions, {}, goals);
    if (auto e = refused(answer.takeError(), "requirements-term"))
      return e;
  }
  {
    auto malformed = terms;
    malformed[4] = malformed[3];
    auto answer = derive(malformed, assumptions, {}, goals);
    if (auto e = refused(answer.takeError(), "requirements-term"))
      return e;
    Result nullary{{{Predicate::equal(9, 9), Rule::Application, {}, 0}}, {0}};
    if (auto e =
            checkCertificate(terms, {}, {}, {Predicate::equal(9, 9)}, nullary))
      return e;
  }
  // Enumerate all partitions of seven identities, then retain exactly models
  // of F=G and pure application functions. This does not replay proof search.
  std::vector<unsigned> values(7);
  std::vector<bool> universal(5, true);
  unsigned models = 0;
  std::function<void(unsigned, unsigned)> visit = [&](unsigned cursor,
                                                      unsigned largest) {
    if (cursor < values.size()) {
      for (unsigned n = 0; n <= largest + 1; ++n) {
        values[cursor] = n;
        visit(cursor + 1, std::max(largest, n));
      }
      return;
    }
    if (values[0] != values[1])
      return;
    for (unsigned i = 3; i < 7; ++i)
      for (unsigned j = 3; j < 7; ++j) {
        bool same = terms[i].name == terms[j].name;
        for (unsigned k = 0; k < 2; ++k)
          same &= values[(*terms[i].arguments)[k]] ==
                  values[(*terms[j].arguments)[k]];
        if (same && values[i] != values[j])
          return;
      }
    ++models;
    for (unsigned i = 0; i < universal.size(); ++i)
      universal[i] = universal[i] && values[goals[i].arguments[0]] ==
                                         values[goals[i].arguments[1]];
  };
  visit(1, 0);
  if (!models)
    return createStringError(inconvertibleErrorCode(),
                             "no static semantic models");
  for (unsigned i = 0; i < universal.size(); ++i)
    if (universal[i] != result->goals[i].has_value())
      return createStringError(inconvertibleErrorCode(),
                               "static semantic mismatch");
  outs() << "static applications: " << models
         << " finite models and certificate regressions passed\n";
  return Error::success();
}
} // namespace

// Test transport only. Production callers use the typed derive API directly.
int main(int argc, char **argv) {
  if (argc == 2 && StringRef(argv[1]) == "--self-test") {
    if (auto e = selfTest()) {
      errs() << toString(std::move(e)) << '\n';
      return 1;
    }
    return 0;
  }
  auto input = MemoryBuffer::getSTDIN();
  if (!input)
    return 1;
  auto parsed = zkc::parseJson((*input)->getBuffer());
  if (!parsed) {
    errs() << toString(parsed.takeError()) << '\n';
    return 1;
  }
  auto result = run(*parsed);
  if (!result) {
    errs() << toString(result.takeError()) << '\n';
    return 1;
  }
  outs() << *result << '\n';
}
