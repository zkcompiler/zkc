#include "zkc/Analysis/PolynomialDomains.h"
#include "zkc/Contracts/Operations.h"
#include "llvm/ADT/STLExtras.h"
#include <tuple>

using namespace llvm;
namespace zkc {
namespace {
using Result = DomainComparison::Result;
std::string fieldOf(StringRef type) {
  auto parts = type.split(':');
  return parts.first == "field" ? parts.second.str() : std::string{};
}

class Analysis {
  PolynomialDomains report;
  using TermKey =
      std::tuple<std::string, std::string, std::string, std::vector<unsigned>>;
  std::map<TermKey, unsigned> interned;
  std::map<std::string, unsigned> exact, lengths;
  std::map<std::tuple<std::string, std::string, unsigned, unsigned>, unsigned>
      classes;

  unsigned term(std::string kind, std::string type, std::string atom = {},
                std::vector<unsigned> args = {}) {
    auto [it, inserted] =
        interned.emplace(TermKey{kind, type, atom, args}, report.terms.size());
    if (inserted)
      report.terms.push_back(
          {std::move(kind), std::move(type), std::move(atom), std::move(args)});
    return it->second;
  }
  unsigned value(const std::string &id) {
    auto found = exact.find(id);
    if (found != exact.end())
      return found->second;
    return exact
        .emplace(id, term("value", report.execution.values.at(id).type, id))
        .first->second;
  }
  unsigned length(const std::string &id) {
    auto found = lengths.find(id);
    if (found != lengths.end())
      return found->second;
    return lengths.emplace(id, term("length", "index", {}, {value(id)}))
        .first->second;
  }
  unsigned half(unsigned n) {
    const auto &t = report.terms[n];
    uint64_t literal;
    if (t.kind == "constant" && !StringRef(t.atom).getAsInteger(10, literal))
      return term("constant", "index", std::to_string(literal / 2));
    return term("half", "index", {}, {n});
  }
  unsigned square(unsigned s) {
    return term("square", report.terms[s].type, {}, {s});
  }
  void transfer(const source::ExecutionOperation &op,
                const protocol::DomainValueContract &facet) {
    const auto &out = op.outputs.at(facet.output);
    const auto &type = report.execution.values.at(out).type;
    using Rule = protocol::DomainValueRule;
    switch (facet.rule) {
    case Rule::Constant:
      exact[out] = term("constant", type, op.attributes.at(0));
      break;
    case Rule::Length:
      exact[out] = length(op.inputs.at(facet.input));
      break;
    case Rule::Multiply: {
      unsigned a = value(op.inputs.at(facet.input));
      unsigned b = value(op.inputs.at(facet.otherInput));
      // Only the needed square law; no broad arithmetic canonicalization.
      if (a == b)
        exact[out] = square(a);
      break;
    }
    case Rule::Divide: {
      unsigned a = value(op.inputs.at(facet.input));
      unsigned b = value(op.inputs.at(facet.otherInput));
      const auto &denominator = report.terms[b];
      if (denominator.kind == "constant" && denominator.atom == "2")
        exact[out] = half(a);
      break;
    }
    }
  }
  unsigned add(PolynomialDomain d) {
    if (!d.field.empty() && !d.convention.empty()) {
      auto [it, inserted] = classes.emplace(
          std::make_tuple(d.field, d.convention, d.size, d.shift),
          classes.size());
      (void)inserted;
      d.congruenceClass = it->second;
    }
    unsigned id = report.domains.size();
    report.domains.push_back(std::move(d));
    return id;
  }

public:
  explicit Analysis(source::Execution execution) {
    report.execution = std::move(execution);
  }
  PolynomialDomains run() {
    for (const auto &path : report.execution.order) {
      const auto &op = report.execution.operations.at(path);
      auto *contracts = protocol::operationContracts(op.callee);
      // A reception is a fresh exact value, never a copy of its sender.
      if (!contracts)
        continue;
      if (contracts->domainValue)
        transfer(op, *contracts->domainValue);
      if (!contracts->coset)
        continue;
      const auto &c = *contracts->coset;
      PolynomialDomain d;
      d.path = path;
      d.operation = op.callee;
      d.role = op.role;
      d.association = "operation";
      d.shiftOrigin = op.inputs.at(c.shiftInput);
      d.sizeOrigin = op.inputs.at(c.sizeInput);
      d.sizeOriginIsLength = c.sizeIsLength;
      d.field = fieldOf(report.execution.values.at(d.shiftOrigin).type);
      if (auto *convention = protocol::cosetConvention(d.field))
        d.convention = convention->identity.str();
      d.shift = value(d.shiftOrigin);
      d.size = c.sizeIsLength ? length(d.sizeOrigin) : value(d.sizeOrigin);
      unsigned domain = add(d);
      if (c.sizeIsLength) {
        DomainUse use;
        use.value = d.sizeOrigin;
        use.domain = domain;
        auto found = report.vectorDomains.find(use.value);
        if (found != report.vectorDomains.end()) {
          use.producerDomain = found->second;
          use.compatibility =
              comparePolynomialDomains(report, found->second, domain);
        } else {
          const auto &v = report.execution.values.at(use.value);
          bool reception =
              v.origin != "$" &&
              !report.execution.operations.at(v.origin).receiver.empty();
          use.compatibility.reasons.push_back(
              reception ? "reception-has-no-trusted-domain"
                        : "no-producer-domain-fact");
        }
        report.uses.push_back(std::move(use));
      }
      if (c.vectorOutput) {
        if (c.foldedOutput) {
          d.association = "fold-result";
          d.size = half(d.size);
          d.shift = square(d.shift);
          domain = add(d);
        }
        const auto &output = op.outputs.at(*c.vectorOutput);
        report.vectorDomains[output] = domain;
        lengths[output] = d.size;
      }
    }
    return std::move(report);
  }
};

DomainComparison compareTerm(const PolynomialDomains &r, unsigned a, unsigned b,
                             StringRef component) {
  if (a == b)
    return {Result::Same, {(component + "-exact-expression").str()}};
  const auto &left = r.terms.at(a), &right = r.terms.at(b);
  if (left.kind == "constant" && right.kind == "constant" &&
      left.type == right.type && left.atom != right.atom)
    return {Result::Different,
            {(component + "-distinct-canonical-constants").str()}};
  if (component == "size" &&
      ((left.kind == "half" && left.arguments.at(0) == b) ||
       (right.kind == "half" && right.arguments.at(0) == a)))
    return {Result::Different, {"size-positive-domain-versus-half"}};
  return {Result::Unknown, {(component + "-equality-unproved").str()}};
}
json::Array strings(const source::Names &names) {
  json::Array result;
  for (const auto &name : names)
    result.push_back(name);
  return result;
}
} // namespace

PolynomialDomains analyzePolynomialDomains(source::Execution e) {
  return Analysis(std::move(e)).run();
}
Expected<PolynomialDomains> inspectPolynomialDomains(const source::Module &m,
                                                     StringRef entry) {
  auto e = source::inspectExecution(m, entry);
  if (!e)
    return e.takeError();
  return analyzePolynomialDomains(std::move(*e));
}
DomainComparison comparePolynomialDomains(const PolynomialDomains &r,
                                          unsigned left, unsigned right) {
  if (left >= r.domains.size() || right >= r.domains.size())
    return {Result::Unknown, {"domain-id-out-of-range"}};
  const auto &a = r.domains[left], &b = r.domains[right];
  if (!a.field.empty() && !b.field.empty() && a.field != b.field)
    return {Result::Different, {"distinct-nominal-fields"}};
  auto size = compareTerm(r, a.size, b.size, "size");
  auto shift = compareTerm(r, a.shift, b.shift, "shift");
  if (size.result == Result::Different)
    return size;
  if (shift.result == Result::Different)
    return shift;
  if (a.field.empty() || b.field.empty())
    return {Result::Unknown, {"nominal-field-unavailable"}};
  if (a.convention.empty() || b.convention.empty())
    return {Result::Unknown, {"root-convention-unavailable"}};
  if (a.convention != b.convention)
    return {Result::Unknown, {"root-convention-compatibility-unproved"}};
  DomainComparison result;
  result.result = size.result == Result::Same && shift.result == Result::Same
                      ? Result::Same
                      : Result::Unknown;
  result.reasons = {"same-nominal-field-and-installed-order"};
  llvm::append_range(result.reasons, size.reasons);
  llvm::append_range(result.reasons, shift.reasons);
  return result;
}

json::Value encodeDomainComparison(const DomainComparison &c) {
  return json::Object{{"relation", c.result == Result::Same        ? "same"
                                   : c.result == Result::Different ? "different"
                                                                   : "unknown"},
                      {"reasons", strings(c.reasons)}};
}
json::Value encodePolynomialDomains(const PolynomialDomains &r) {
  json::Array terms, domains, uses, values;
  for (auto [id, t] : llvm::enumerate(r.terms)) {
    json::Array args;
    for (unsigned a : t.arguments)
      args.push_back(a);
    terms.push_back(json::Object{{"id", id},
                                 {"kind", t.kind},
                                 {"type", t.type},
                                 {"atom", t.atom},
                                 {"arguments", std::move(args)}});
  }
  for (auto [id, d] : llvm::enumerate(r.domains)) {
    json::Object object{{"id", id},
                        {"path", d.path},
                        {"operation", d.operation},
                        {"role", d.role},
                        {"association", d.association},
                        {"field", d.field},
                        {"family", "two-adic-multiplicative-coset"},
                        {"shift", d.shift},
                        {"size", d.size},
                        {"shift_origin", d.shiftOrigin},
                        {"size_origin", d.sizeOrigin},
                        {"size_origin_is_length", d.sizeOriginIsLength}};
    object["congruence_class"] = d.congruenceClass
                                     ? json::Value(*d.congruenceClass)
                                     : json::Value(nullptr);
    if (const auto *c = protocol::cosetConvention(d.field))
      object["convention"] = json::Object{
          {"identity", c->identity},
          {"root_field", c->rootField},
          {"maximal_root", c->maximalRoot},
          {"max_log_size", c->maxLogSize},
          {"root_formula", "embed(maximal_root^(2^max_log_size / size))"},
          {"order", c->order}};
    else
      object["convention"] = nullptr;
    domains.push_back(std::move(object));
  }
  for (const auto &u : r.uses) {
    json::Object object{
        {"value", u.value},
        {"domain", u.domain},
        {"compatibility", encodeDomainComparison(u.compatibility)}};
    object["producer_domain"] = u.producerDomain
                                    ? json::Value(*u.producerDomain)
                                    : json::Value(nullptr);
    uses.push_back(std::move(object));
  }
  for (const auto &[id, v] : r.execution.values) {
    json::Object object{{"id", id},
                        {"name", v.name},
                        {"origin", v.origin},
                        {"role", v.role},
                        {"type", v.type}};
    auto found = r.vectorDomains.find(id);
    object["domain"] = found == r.vectorDomains.end()
                           ? json::Value(nullptr)
                           : json::Value(found->second);
    std::string reason = "entry-has-no-domain-fact";
    json::Array dependencies;
    if (v.origin != "$") {
      const auto &op = r.execution.operations.at(v.origin);
      reason = op.receiver.empty() ? "no-installed-domain-transfer"
                                   : "reception-has-no-trusted-domain";
      if (op.receiver.empty())
        dependencies = strings(op.inputs);
      else
        object["authored_sender_value"] = op.inputs.at(0);
    }
    object["may_depend_on"] = std::move(dependencies);
    if (found == r.vectorDomains.end())
      object["unknown_reason"] = reason;
    values.push_back(std::move(object));
  }
  return json::Object{
      {"format", "zkc.polynomial-domains/1"},
      {"scope",
       "ordered nominal domains, conditional on successful operations"},
      {"terms", std::move(terms)},
      {"domains", std::move(domains)},
      {"uses", std::move(uses)},
      {"values", std::move(values)}};
}
} // namespace zkc
