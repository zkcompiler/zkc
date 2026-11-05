#include "../lib/Language/BindingWitness.h"
#include "../lib/Language/Checker.h"
#include "../lib/Language/Conformance.h"
#include "../lib/Language/DescriptorClosure.h"
#include "../lib/Language/DescriptorWitness.h"
#include "../lib/Language/FiniteCardinality.h"
#include "../lib/Language/SignatureWitness.h"
#include "../lib/Language/TypeInference.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Language/SourceTerms.h"
#include <cstdlib>
#include <limits>
#include <new>

namespace {
bool observeAllocations = false;
uint64_t observedAllocationBytes = 0;
struct AllocationObservation {
  AllocationObservation() {
    observedAllocationBytes = 0;
    observeAllocations = true;
  }
  ~AllocationObservation() { observeAllocations = false; }
};
} // namespace
// Count real allocations in one bounded traversal, including discarded strings
// and argument vectors. The observer never changes allocation or refusal
// policy.
void *operator new(std::size_t size) {
  if (observeAllocations)
    observedAllocationBytes += size;
  if (void *result = std::malloc(size ? size : 1))
    return result;
  throw std::bad_alloc();
}
void operator delete(void *value) noexcept { std::free(value); }
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
using K = Type::Kind;
Type leaf(Type item = Type(K::Index)) {
  return descriptorType({DescriptorFamily::Finite, {std::move(item)}});
}
Type product(std::vector<Type> children = {}) {
  Type result(K::DescriptorProduct);
  result.arguments = std::move(children);
  return result;
}
Type natural(uint64_t value) {
  Type result(K::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
Type atom(StringRef name) {
  Type result(K::Natural, name.str());
  result.symbolic = true;
  result.dimension = take(Natural::atom(name));
  return result;
}
Type sequence(Type element, std::optional<Type> extent = {}) {
  Type result(K::DescriptorSequence);
  result.arguments.push_back(std::move(element));
  if (extent)
    result.arguments.push_back(std::move(*extent));
  return result;
}
struct Context {
  Limits limits;
  Work work;
  std::vector<Declaration> declarations;
  Semantics types;
  explicit Context(Limits limits = {})
      : limits(limits), work{this->limits}, types(declarations, {}, work) {}
};
void refused(Context &context, bool accepted, StringRef code) {
  require(!accepted && context.types.diagnostic &&
              context.types.diagnostic->code == code,
          "unexpected admission: " + (context.types.diagnostic
                                          ? context.types.diagnostic->code
                                          : "no diagnostic"));
}
} // namespace
int main() {
  Cases cases;
  cases.run("recursive round trip and Finite identity", [] {
    auto f = leaf();
    // Captured from the existing key framing; existing enum ordinals stay put.
    require(typeIdentity(f) == "22:0:0:0:1:01:11:3:0:0:1:00:",
            "Finite canonical identity changed");
    std::string framed;
    frameTypeIdentity(framed, f);
    require(framed == std::string("\x1c\0\0\0\0\0\0\0", 8) +
                          "22:0:0:0:1:01:11:3:0:0:1:00:",
            "Finite enclosing u64 frame changed");
    auto tree =
        product({sequence(product({f, leaf(Type(K::Boolean))}), natural(0)),
                 sequence(f), product(), product({f})});
    Context c;
    require(c.types.chargeType(tree, {}), "valid recursive contract refused");
    auto contract = *descriptorContract(tree);
    require(descriptorType(contract) == tree &&
                descriptorContract(descriptorType(contract)) == contract,
            "round trip lost a structural child or extent");
    require(&descriptorType(contract) == &contract.type,
            "projection copied the contract");
  });
  cases.run(
      "actual specialization preserves framed static instance identity", [] {
        auto project =
            take(analyze(take(capture({{"m",
                                        "module m; pub protocol P<T:Type> "
                                        "roles(P)()->(){return ();}",
                                        "identity.zkc"}})))
                     .checkedProject());
        auto entry =
            take(closeNativeRun(project, "m::P", {}, {Type(K::Index)}));
        // Existing instance preimage: u64-LE frames of m::P, the Index
        // lookup key, domains, input-aliases, and capture-inputs.
        require(entry.protocol().symbol ==
                    "zkl_d50d43442a207d9e91539889e7d3852b006b09d69be36a920"
                    "8e28e8535af91e8",
                "specialization changed its static argument framing");
      });
  cases.run("order arity zero singleton and optional extent are identity", [] {
    auto a = leaf(), b = leaf(Type(K::Boolean));
    std::vector<Type> terms{product(),
                            product({a}),
                            product({a, b}),
                            product({b, a}),
                            sequence(a),
                            sequence(a, natural(0)),
                            sequence(a, natural(1)),
                            Type(K::Unit)};
    Type tuple(K::Tuple);
    tuple.arguments = {Type(K::Index)};
    terms.push_back(tuple);
    Type array(K::Array);
    array.arguments = {Type(K::Index)};
    terms.push_back(array);
    for (unsigned i = 0; i < terms.size(); ++i)
      for (unsigned j = 0; j < i; ++j)
        require(terms[i] != terms[j] &&
                    typeIdentity(terms[i]) != typeIdentity(terms[j]),
                "category, order, arity or extent presence collapsed");
  });
  cases.run("nested provider statics and nominal authority remain exact", [] {
    Type provider(K::Module, "m::Provider");
    provider.arguments = {domainType("Field", "f17"), natural(3),
                          assetType("Ring", "ring-a")};
    Type item(K::Record, "m::Item");
    item.arguments = {provider};
    auto tree = product({leaf(), sequence(leaf(item), natural(2))});
    auto key = [&](StringRef revision) {
      return take(canonicalTypeKey(
          tree, [&](StringRef path) -> Expected<std::optional<std::string>> {
            require(path == "m::Item" || path == "m::Provider",
                    "missing nominal");
            return std::optional<std::string>(
                std::string(64, revision.front()));
          }));
    };
    require(key("a") != key("b"), "nested source authority was erased");
    auto changed = tree;
    changed.arguments.back()
        .arguments.front()
        .arguments.front()
        .arguments.front()
        .arguments.back() = assetType("Ring", "ring-b");
    require(changed != tree && typeIdentity(changed) != typeIdentity(tree),
            "nested provider static identity was erased");
  });
  cases.run(
      "substitution visits every element and extent and normalizes naturals",
      [] {
        Context c;
        Type parameter(K::Parameter, "owner::T");
        parameter.symbolic = true;
        auto count = atom("owner::N");
        count.domain.clear();
        count.dimension = take(c.types.naturals.add(
            count.dimension, take(c.types.naturals.multiply(
                                 Natural::constant(2), count.dimension))));
        auto tree =
            product({leaf(parameter),
                     sequence(product({leaf(), leaf(parameter)}), count)});
        require(c.types.symbolic(tree), "nested symbols classified closed");
        auto result = c.types.substitute(
            DescriptorContract(tree),
            {{"owner::T", Type(K::Boolean)}, {"owner::N", natural(4)}}, {});
        auto expected = product(
            {leaf(Type(K::Boolean)),
             sequence(product({leaf(), leaf(Type(K::Boolean))}), natural(12))});
        require(result && descriptorType(*result) == expected &&
                    !c.types.symbolic(descriptorType(*result)),
                "substitution skipped a later child or natural normalization");
      });
  cases.run(
      "inference solves nested ordinary parameters and natural extents", [] {
        Context c;
        TypeInference solver(c.types);
        auto item = solver.fresh({}), extent = solver.fresh({});
        Type parameter(K::Parameter, "owner::T");
        parameter.symbolic = true;
        auto pattern =
            product({leaf(), sequence(leaf(parameter), atom("owner::N"))});
        auto wanted =
            product({leaf(), sequence(leaf(Type(K::Boolean)), natural(5))});
        auto variable = solver.instantiate(
            pattern, {{"owner::T", item}, {"owner::N", extent}}, {});
        require(solver.equal(variable, solver.known(wanted, {}), {}) &&
                    solver.solve({}) &&
                    solver.get(item, {}) == Type(K::Boolean) &&
                    solver.get(extent, {}) == natural(5) &&
                    solver.get(variable, {}) == wanted,
                "inference skipped nested contracts or extent");
      });
  for (unsigned mutation = 0; mutation < 5; ++mutation)
    cases.run(
        "inference rejects complete structural conflict " + Twine(mutation),
        [&] {
          Context c;
          TypeInference solver(c.types);
          auto original =
              product({leaf(), sequence(leaf(Type(K::Boolean)), natural(0))});
          auto changed = original;
          if (mutation == 0)
            std::reverse(changed.arguments.begin(), changed.arguments.end());
          if (mutation == 1)
            changed.arguments.pop_back();
          if (mutation == 2)
            changed.arguments.back().arguments.pop_back();
          if (mutation == 3)
            changed.arguments.back().arguments.back() = natural(1);
          if (mutation == 4)
            changed.arguments.back().arguments.front() = leaf();
          refused(c,
                  solver.equal(solver.known(original, {}),
                               solver.known(changed, {}), {}),
                  "source.type");
        });
  for (unsigned mutation = 0; mutation < 15; ++mutation)
    cases.run("malformed structural candidate " + Twine(mutation), [&] {
      Context c;
      auto tree = sequence(product({leaf()}), natural(0));
      require(c.types.chargeContract(DescriptorContract(tree), {}),
              "valid original contract refused before mutation");
      if (mutation == 0)
        tree.arguments.clear();
      if (mutation == 1)
        tree.arguments.push_back(natural(0));
      if (mutation == 2)
        tree.arguments.front() = Type(K::Tuple);
      if (mutation == 3)
        tree.arguments.front().arguments.push_back(Type(K::Boolean));
      if (mutation == 4)
        tree.arguments.back() = leaf();
      if (mutation == 5)
        tree.arguments.back().arguments.push_back(natural(0));
      if (mutation == 6)
        tree.dimension = Natural::constant(1);
      if (mutation == 7)
        tree.domain = "foreign";
      if (mutation == 8)
        tree.sort = "foreign";
      if (mutation == 9)
        tree.symbolic = true;
      if (mutation == 10)
        tree.family = static_cast<DescriptorFamily>(99);
      if (mutation == 11)
        tree.arguments.back().domain = "foreign";
      if (mutation == 12)
        tree.arguments.back().symbolic = true;
      if (mutation == 13)
        tree.arguments.front().arguments.front().arguments.clear();
      if (mutation == 14)
        tree.arguments.back().assumptions.copy = true;
      refused(c, c.types.chargeContract(DescriptorContract(tree), {}),
              "source.descriptor");
      refuses(canonicalTypeKey(
                  tree,
                  [](StringRef) -> Expected<std::optional<std::string>> {
                    return std::nullopt;
                  }),
              "source.descriptor");
    });
  for (unsigned mutation = 0; mutation < 6; ++mutation)
    cases.run("nested natural candidate metadata " + Twine(mutation), [&] {
      Type item(K::Record, "m::Item");
      item.arguments = {natural(0)};
      auto tree = product({leaf(item)});
      Context c;
      require(c.types.chargeContract(DescriptorContract(tree), {}),
              "valid nominal static refused");
      auto &term = tree.arguments.front().arguments.front().arguments.front();
      if (mutation == 0)
        term.arguments.push_back(Type(K::Index));
      if (mutation == 1)
        term.sort = "foreign";
      if (mutation == 2)
        term.family = static_cast<DescriptorFamily>(99);
      if (mutation == 3)
        term.domain = "foreign";
      if (mutation == 4)
        term.symbolic = true;
      if (mutation == 5)
        term.assumptions.copy = true;
      refused(c, c.types.chargeContract(DescriptorContract(tree), {}),
              "source.descriptor");
      refuses(encodeStaticTerm(tree), "source.descriptor");
    });
  cases.run("descriptor children cannot hide in scalar static arguments", [] {
    for (auto kind : {K::Boolean, K::Field, K::Natural, K::Associated}) {
      Context c;
      Type ordinary(kind);
      ordinary.arguments = {product()};
      refused(c, c.types.chargeType(ordinary, {}), "source.descriptor");
    }
  });
  cases.run("open ordinary parameters remain symbolic without a candidate flag",
            [] {
              Context c;
              Type parameter(K::Parameter, "owner::T");
              require(c.types.symbolic(product({leaf(parameter)})),
                      "candidate flag concealed an unresolved type parameter");
            });
  cases.run(
      "ordinary Type admission cannot capture structural descriptors", [] {
        for (auto tree :
             {product(), sequence(leaf()), sequence(leaf(), natural(0))}) {
          Context c;
          Declaration target{};
          Parameter parameter{};
          parameter.sort = Parameter::Sort::Type;
          parameter.atom = "owner::T";
          target.parameters = {parameter};
          refused(c, c.types.checkArgumentSorts(target, {tree}, {}),
                  "source.generic");
          Context replacement;
          tree.symbolic = true;
          tree.domain = "forged::D";
          refused(
              replacement,
              replacement.types.substitute(tree, {{"forged::D", leaf()}}, {})
                  .has_value(),
              "source.descriptor");
        }
      });
  cases.run("unchanged Finite source schema and malformed leaf refusal", [] {
    auto encoded = take(encodeStaticTerm(leaf()));
    require(encoded ==
                json::Value(json::Array{"builtin", "finite",
                                        json::Array{json::Array{"index"}}}),
            "Finite source term schema changed");
    auto malformed = leaf();
    malformed.arguments.clear();
    Context c;
    refused(c, c.types.chargeContract(DescriptorContract(malformed), {}),
            "source.descriptor");
    require(!finiteDescriptorItem(DescriptorContract(malformed)),
            "raw empty Finite tag acquired leaf authority");
  });
  cases.run("substitution cannot introduce descriptor data arguments", [] {
    Type parameter(K::Parameter, "owner::T");
    parameter.symbolic = true;
    for (auto kind : {K::Tuple, K::Array, K::Record, K::Builtin}) {
      Context c;
      Type data(kind);
      data.arguments = {parameter};
      refused(
          c,
          c.types.substitute(data, {{"owner::T", product()}}, {}).has_value(),
          "source.descriptor");
    }
  });
  cases.run(
      "structural descriptors have no ordinary Type or native authority", [] {
        for (const auto &tree : {product(), product({leaf()}), sequence(leaf()),
                                 sequence(leaf(), natural(0))}) {
          Context c;
          require(isDescriptor(tree) && isStaticOnly(tree) &&
                      !valueType(tree) && !isLogicalValue(tree) &&
                      !finiteDescriptorItem(DescriptorContract(tree)) &&
                      frontendTypeConstructor(tree).empty(),
                  "structural category acquired installed or data authority");
          require(c.types.admission(tree, Boundary::Construction, {}) ==
                      Semantics::Admission::Rejected,
                  "structural descriptor acquired native construction");
          refuses(c.types.nativeLayout(tree), "source.layout");
          refuses(encodeStaticTerm(tree), "source.static-term");
        }
      });
  cases.run(
      "whole contract depth node and work limits include optional extent", [] {
        auto tree = product({sequence(leaf(), natural(0)), product()});
        // product -> sequence -> Finite -> index is four levels, six nodes.
        auto cost = take(typeComplexity(tree, 6, 4));
        require(take(typeComplexity(tree, 6, 4, cost)) == cost,
                "exact work refused");
        refuses(typeComplexity(tree, 5, 4), "source.limit");
        refuses(typeComplexity(tree, 6, 3), "source.limit");
        refuses(typeComplexity(tree, 6, 4, cost - 1), "source.limit");
        Limits limits;
        limits.work = cost;
        Context exact(limits);
        require(exact.types.chargeIdentity(tree, {}), "exact identity failed");
        require(exact.work.used == cost, "whole identity charge omitted root");
        limits.work = cost - 1;
        Context shortBudget(limits);
        refused(shortBudget, shortBudget.types.chargeIdentity(tree, {}),
                "source.limit");
        require(exact.types.charge(0, {}),
                "zero charge changed exhausted budget");
        refused(exact, exact.types.chargeIdentity(tree, {}), "source.limit");
        Context retry;
        require(retry.types.chargeContract(DescriptorContract(tree), {}),
                "fresh retry failed");
        require(retry.work.used ==
                        take(typeComplexity(tree, 6, 4, UINT64_MAX, nullptr,
                                            true, TypeWork::Copy)) &&
                    retry.work.used < cost,
                "copy charged identity construction work");
      });
  cases.run("extent identity is charged without expanding payload length", [] {
    auto huge = sequence(leaf(), natural(std::numeric_limits<uint64_t>::max()));
    Context c;
    require(c.types.chargeContract(DescriptorContract(huge), {}),
            "finite scalar extent refused");
    require(c.work.used < 10000, "contract expanded a payload");
    auto projected = atom("n");
    projected.domain.clear();
    projected.dimension =
        take(Natural::projection("asset", std::string(1000, 'x')));
    require(take(typeComplexity(sequence(leaf(), projected), 5, 4)) >
                take(typeComplexity(sequence(leaf(), atom("n")), 5, 4)) + 1000,
            "nested projection member omitted from identity budget");
  });
  cases.run(
      "selected substitution is bounded before expanding child copies", [] {
        Type parameter(K::Parameter, "owner::T");
        parameter.symbolic = true;
        auto tree = product({leaf(parameter), leaf(parameter)});
        Type large(K::Tuple);
        large.arguments = {Type(K::Boolean), Type(K::Boolean)};
        Limits limits;
        limits.typeNodes = 8;
        Context nodes(limits);
        refused(
            nodes,
            nodes.types.substitute(tree, {{"owner::T", large}}, {}).has_value(),
            "source.limit");
        require(nodes.work.used < 10,
                "expanded candidate was copied before refusal");
        limits = Limits{};
        limits.typeDepth = 3;
        Context depth(limits);
        refused(
            depth,
            depth.types.substitute(tree, {{"owner::T", large}}, {}).has_value(),
            "source.limit");
        limits.typeDepth = 4;
        Context nested(limits);
        refused(nested,
                nested.types.substitute(tree, {{"owner::T", large}}, {}, 2)
                    .has_value(),
                "source.limit");
        require(nested.work.used < 10,
                "explicit starting depth bypassed expanded preflight");
      });
  cases.run(
      "default depth limit refuses deep structure and permits fresh retry", [] {
        auto tree = product();
        for (unsigned i = 0; i < 40; ++i)
          tree = product({tree});
        Context deep;
        refused(deep, deep.types.chargeContract(DescriptorContract(tree), {}),
                "source.limit");
        Context retry;
        require(retry.types.chargeContract(DescriptorContract(product()), {}),
                "failed structural attempt poisoned a fresh invocation");
      });
  cases.run(
      "inference bounds shared child expansion before reconstruction", [] {
        Limits limits;
        limits.typeNodes = 3;
        Context c(limits);
        TypeInference solver(c.types);
        auto child = solver.known(leaf(), {});
        auto repeated = solver.shape(product(), {child, child}, {});
        auto before = c.work.used;
        refused(c, solver.get(repeated, {}).has_value(), "source.limit");
        require(c.work.used - before < 10,
                "inference copied expanded children before refusal");
        Context retry(limits);
        TypeInference fresh(retry.types);
        auto single = fresh.shape(product(), {fresh.known(leaf(), {})}, {});
        require(fresh.get(single, {}) == product({leaf()}),
                "bounded inference retry failed");
      });
  for (unsigned mutation = 0; mutation < 6; ++mutation)
    cases.run(
        "ordinary descriptor leaf metadata mutant " + Twine(mutation), [&] {
          auto original = leaf();
          Context valid;
          require(valid.types.chargeContract(DescriptorContract(original), {}),
                  "valid original refused");
          take(canonicalTypeKey(
              original, [](StringRef) -> Expected<std::optional<std::string>> {
                return std::optional<std::string>{};
              }));
          take(encodeStaticTerm(original));
          auto mutant = original;
          auto &item = mutant.arguments.front();
          if (mutation == 0)
            item.sort = "foreign";
          if (mutation == 1)
            item.domain = "foreign";
          if (mutation == 2)
            item.arguments = {Type(K::Boolean)};
          if (mutation == 3)
            item.dimension = Natural::constant(1);
          if (mutation == 4)
            item.symbolic = true;
          if (mutation == 5)
            item.family = static_cast<DescriptorFamily>(99);
          require(mutant != original || mutation == 5,
                  "mutant did not change candidate");
          Context invalid;
          refused(invalid,
                  invalid.types.chargeContract(DescriptorContract(mutant), {}),
                  "source.descriptor");
          refuses(canonicalTypeKey(
                      mutant,
                      [](StringRef) -> Expected<std::optional<std::string>> {
                        return std::optional<std::string>{};
                      }),
                  "source.descriptor");
          refuses(encodeStaticTerm(mutant), "source.descriptor");
        });
  cases.run("Array reconstruction counts stored nodes and depth", [] {
    Type array(K::Array);
    array.arguments = {Type(K::Index)};
    auto term = leaf(array);
    Limits limits;
    limits.typeNodes = 3;
    limits.typeDepth = 3;
    Context c(limits);
    require(c.types.chargeContract(DescriptorContract(term), {}),
            "exact stored cap refused");
    TypeInference solver(c.types);
    auto variable = solver.known(term, {});
    require(solver.get(variable, {}) == term,
            "synthetic dimension consumed stored cap");
  });
  cases.run("empty substitution respects explicit depth before copying", [] {
    Limits limits;
    limits.typeDepth = 4;
    auto tree = product({product({leaf()})});
    Context c(limits);
    refused(c, c.types.substitute(tree, {}, {}, 2).has_value(), "source.limit");
    require(c.work.used == 1,
            "empty bindings copied before absolute-depth refusal");
    Context exact(limits);
    require(exact.types.substitute(tree, {}, {}, 1) == tree,
            "valid explicit depth refused");
  });
  cases.run("inference allocates shallow heads without discarded subtrees", [] {
    Type item(K::Record, std::string(4096, 'x'));
    auto tree = leaf(item);
    for (unsigned i = 0; i < 8; ++i)
      tree = product({std::move(tree)});
    Limits limits;
    limits.work = 4200;
    Context c(limits);
    TypeInference solver(c.types);
    {
      AllocationObservation observing;
      solver.known(tree, {});
    }
    require(!c.types.diagnostic && c.work.used <= 4200,
            "bounded inference refused");
    require(observedAllocationBytes < 24000,
            "inference materialized discarded recursive arguments: " +
                Twine(observedAllocationBytes));
    // The same path also has a real resolved nominal source control.
    take(analyze(take(capture({{"m",
                                "module m; struct Item{pub value:index} math "
                                "fn id(x:Item)->Item{return x;}",
                                "nominal.zkc"}})))
             .checkedProject());
  });
  cases.run(
      "admission witness debits Identity before allocation and cumulatively",
      [] {
        Type item(K::Record, std::string(2048, 'x'));
        auto tree = product({sequence(leaf(item), natural(3))});
        Declaration written;
        written.admissions.push_back({tree, Boundary::Construction, {}, {}});
        auto identity = take(typeComplexity(tree, 100, 10));
        auto copy = take(typeComplexity(tree, 100, 10, UINT64_MAX, nullptr,
                                        true, TypeWork::Copy));
        auto expected = 2 * (identity + 1);
        for (uint64_t allowance :
             {copy + 1, expected, expected - 1, 2 * expected}) {
          Limits limits;
          Context c(limits);
          uint64_t remaining = allowance;
          c.work.allowance = &remaining;
          bool result;
          {
            AllocationObservation observing;
            result =
                requiredAdmissionsIncluded(c.types, written, written, true);
          }
          if (allowance < expected) {
            refused(c, result, "source.limit");
            if (allowance == copy + 1)
              require(observedAllocationBytes < 2048,
                      "key was allocated before Identity debit");
          } else {
            require(result && c.work.used == expected,
                    "witness key work omitted or reset");
            require(
                requiredAdmissionsIncluded(c.types, written, written, true) ==
                    (allowance == 2 * expected),
                "repeated witness call reset allowance");
            if (allowance == 2 * expected)
              require(remaining == 0, "repeated key work undercharged");
          }
        }
      });
  cases.run("pure selection validates changed parent categories before copying",
            [] {
              Type parameter(K::Parameter, "T");
              parameter.symbolic = true;
              auto tree = product({leaf(parameter)});
              Context valid;
              auto selected =
                  valid.types.substitute(tree, {{"T", Type(K::Index)}}, {});
              require(selected && *selected == product({leaf()}),
                      "valid selection failed");
              for (const auto &bad : {natural(0), product({leaf()})}) {
                Context mutant;
                std::optional<Type> result;
                {
                  AllocationObservation observing;
                  result = mutant.types.substitute(tree, {{"T", bad}}, {});
                }
                refused(mutant, bool(result), "source.descriptor");
              }
            });
  cases.run("exhausted inference never allocates fresh nodes", [] {
    Context c;
    TypeInference solver(c.types);
    uint64_t remaining = 1;
    c.work.allowance = &remaining;
    require(solver.fresh({}) == 0, "first variable not allocated");
    auto refusedId = solver.fresh({});
    require(c.types.diagnostic && refusedId == 1, "fresh did not refuse");
    {
      AllocationObservation observing;
      for (unsigned i = 0; i < 20; ++i)
        require(solver.fresh({}) == refusedId,
                "exhaustion allocated a hidden inference node");
    }
    require(observedAllocationBytes == 0,
            "exhaustion allocated before a successful debit");
    require(!solver.structure(refusedId, {}) &&
                !solver.allows(refusedId, K::Index),
            "failed node sentinel was dereferenced");
  });
  cases.run("generic record cache refuses before copying bindings", [] {
    Context c;
    Declaration record;
    record.id = {0};
    record.kind = Declaration::Kind::Record;
    record.qualifiedName = "m::Record";
    record.parameters.push_back(
        {Parameter::Sort::Type, "T", "m::Record::T", {}, {}, {}, {}, {}});
    record.fields.push_back({"value", Type(K::Index), true, {}});
    c.declarations.push_back(record);
    c.types.indexDeclaration(c.declarations.front());
    Type term(K::Record, "m::Record");
    term.arguments.push_back(Type(K::Record, std::string(4096, 'x')));
    require(bool(c.types.fields(term, {}, 1)), "cache prime failed");
    uint64_t remaining = 1;
    c.work.allowance = &remaining;
    std::shared_ptr<const std::vector<TypeField>> result;
    {
      AllocationObservation observing;
      result = c.types.fields(term, {}, 1);
    }
    refused(c, bool(result), "source.limit");
    require(observedAllocationBytes < 4096,
            "cache lookup copied a binding before its current debit");
  });
  cases.run(
      "Natural normalization reuses bounds of an unchanged stored tree", [] {
        NaturalArithmetic algebra;
        Type extent(K::Natural);
        extent.dimension =
            take(algebra.add(take(Natural::atom("N")), Natural::constant(1)));
        extent.symbolic = true;
        Type item(K::Record, std::string(4096, 'x'));
        auto input = sequence(leaf(item), extent);
        for (unsigned i = 0; i < 6; ++i)
          input = product({input});
        Context c;
        uint64_t remaining = 4300;
        c.work.allowance = &remaining;
        auto output = c.types.substitute(input, {{"N", natural(4)}}, {});
        require(output && !c.types.diagnostic, "bounded normalization failed");
        auto expected = sequence(leaf(item), natural(5));
        for (unsigned i = 0; i < 6; ++i)
          expected = product({expected});
        require(*output == expected, "normalization changed stored structure");
        Context independent;
        require(
            independent.types.chargeContract(DescriptorContract(*output), {}),
            "normalized result is not complete");
      });
  cases.run(
      "selected Natural heads do not schedule an unreplaced normalization", [] {
        Context c;
        auto input = sequence(leaf(), atom("N"));
        auto selected = sequence(leaf(), natural(4));
        auto copy = take(typeComplexity(selected, 100, 10, UINT64_MAX, nullptr,
                                        true, TypeWork::Copy));
        auto output = c.types.substitute(input, {{"N", natural(4)}}, {});
        require(output && *output == selected && c.work.used == copy + 4,
                "pure selected result was traversed again: " +
                    Twine(c.work.used));
      });
  cases.run("irrelevant bindings do not rematerialize canonical polynomials",
            [] {
              Context c;
              auto input = sequence(leaf(), atom("N"));
              auto before = c.types.naturals.remainingWork();
              auto output = c.types.substitute(input, {{"M", natural(4)}}, {});
              require(output && *output == input &&
                          c.types.naturals.remainingWork() == before,
                      "unrelated substitution rebuilt the polynomial");
            });
  cases.run("empty substitution reuses the canonical Natural polynomial", [] {
    Context c;
    auto input = sequence(leaf(), atom("N"));
    auto before = c.types.naturals.remainingWork();
    auto output = c.types.substitute(input, {}, {});
    require(output && *output == input &&
                c.types.naturals.remainingWork() == before,
            "unchanged polynomial was normalized again");
  });
  cases.run(
      "record field cache compares complete owned candidates cumulatively", [] {
        Context c;
        Declaration record;
        record.id = {0};
        record.kind = Declaration::Kind::Record;
        record.qualifiedName = "m::Record";
        record.fields.push_back({"value", Type(K::Index), true, {}});
        c.declarations.push_back(record);
        c.types.indexDeclaration(c.declarations.front());
        Type term(K::Record, "m::Record");
        require(bool(c.types.fields(term, {}, 1)), "record cache prime failed");
        auto copy = take(typeComplexity(term, 100, 10, UINT64_MAX, nullptr,
                                        true, TypeWork::Copy));
        auto expected = 6 + term.domain.size() + copy;
        uint64_t remaining = 2 * expected;
        c.work.allowance = &remaining;
        for (unsigned i = 0; i < 2; ++i) {
          auto before = c.work.used;
          require(c.types.fields(term, {}, 1) &&
                      c.work.used - before == expected,
                  "cache comparison did not debit the current candidate");
        }
        require(remaining == 0, "record cache did not consume exact allowance");
        refused(c, bool(c.types.fields(term, {}, 1)), "source.limit");
      });
  cases.run(
      "Layout lookup and second canonical key share the actual allowance", [] {
        auto project = take(
            analyze(take(capture(
                        {{"m",
                          "module m; pub protocol P roles(P)()->(){return ();}",
                          "layout.zkc"}})))
                .checkedProject());
        auto entry = take(closeNativeRun(project, "m::P"));
        Limits limits;
        Type term(K::Index);
        auto identity =
            take(typeComplexity(term, limits.typeNodes, limits.typeDepth));
        auto keyBytes = typeIdentity(term).size();
        uint64_t remaining = limits.work;
        Layouts layouts(entry, limits, remaining);
        auto layout = take(layouts.get(term));
        auto first = limits.work - remaining;
        auto copy =
            take(typeComplexity(term, limits.typeNodes, limits.typeDepth,
                                UINT64_MAX, nullptr, true, TypeWork::Copy));
        auto expectedHit = 1 + 2 * copy;
        for (unsigned i = 0; i < 2; ++i) {
          auto before = remaining;
          require(take(layouts.get(term)) == layout &&
                      before - remaining == expectedHit,
                  "Layout cache comparison escaped cumulative Copy debit");
        }
        remaining = expectedHit - 1;
        refuses(layouts.get(term), "source.limit");
        // For Index the second key is the final operation: its materialization
        // debit must precede both allocation and the subsequent hash-byte
        // debit.
        remaining = first - keyBytes - 1;
        Layouts shortSecond(entry, limits, remaining);
        refuses(shortSecond.get(term), "source.limit");
        require(remaining == identity - 1,
                "second canonical key allocated before its debit");
        remaining = first;
        Layouts exact(entry, limits, remaining);
        take(exact.get(term));
        require(remaining == 0, "exact Layout boundary changed");
        remaining = first - 1;
        Layouts oneShort(entry, limits, remaining);
        refuses(oneShort.get(term), "source.limit");
      });
  cases.run(
      "budgeted canonical keys and export refuse before materialization", [] {
        Type item(K::Record, "m::Item");
        auto term = leaf(item);
        Limits limits;
        auto cost = take(typeComplexity(term, limits.typeNodes,
                                        limits.typeDepth, UINT64_MAX, nullptr,
                                        true, TypeWork::CanonicalIdentity));
        unsigned authorities = 0, debits = 0;
        auto authority =
            [&](StringRef) -> Expected<std::optional<std::string>> {
          ++authorities;
          return std::optional<std::string>(std::string(64, 'a'));
        };
        uint64_t remaining = 2 * cost;
        auto debit = [&](uint64_t amount) -> Error {
          ++debits;
          require(amount <= remaining, "debit ignored remaining");
          remaining -= amount;
          return Error::success();
        };
        auto key =
            take(canonicalTypeKey(term, authority, limits, remaining, debit));
        require(take(canonicalTypeKey(term, authority, limits, remaining,
                                      debit)) == key &&
                    remaining == 0 && authorities == 2 && debits == 2,
                "canonical call reset ledger");
        refuses(canonicalTypeKey(term, authority, limits, cost - 1, debit),
                "source.limit");
        require(authorities == 2 && debits == 2,
                "authority ran before admission");
        remaining = take(typeComplexity(term, limits.typeNodes,
                                        limits.typeDepth, UINT64_MAX, nullptr,
                                        true, TypeWork::StaticExport));
        take(encodeStaticTerm(term, limits, remaining, debit));
        require(remaining == 0 && debits == 3,
                "export started default allowance");
        refuses(encodeStaticTerm(term, limits, remaining, debit),
                "source.limit");
        require(debits == 3, "failed export debit was accepted");
      });
  cases.run(
      "unchanged substitution copies one completely preflighted tree", [] {
        Type item(K::Record, std::string(4096, 'x'));
        auto tree = leaf(item);
        for (unsigned i = 0; i < 8; ++i)
          tree = product({std::move(tree)});
        Limits limits;
        limits.work = 4200;
        Context c(limits);
        std::optional<Type> result;
        {
          AllocationObservation observing;
          result = c.types.substitute(tree, {{"unused", Type(K::Index)}}, {});
        }
        require(result == tree && observedAllocationBytes < 24000,
                "unchanged substitution repeatedly copied a subtree");
        require(c.work.used ==
                    1 + take(typeComplexity(tree, limits.typeNodes,
                                            limits.typeDepth, UINT64_MAX,
                                            nullptr, true, TypeWork::Copy)),
                "unchanged substitution traversed again or charged Identity");
      });
  cases.run("key construction writes recursive material only once", [] {
    auto tree = leaf(Type(K::Record, std::string(4096, 'x')));
    for (unsigned i = 0; i < 8; ++i)
      tree = product({std::move(tree)});
    auto key = typeIdentity(tree);
    std::string framed = "prefix:";
    {
      AllocationObservation observing;
      frameTypeIdentity(framed, tree);
    }
    std::string expected = "prefix:";
    frame(expected, key);
    require(framed == expected && observedAllocationBytes < 20000,
            "key construction materialized recursive ancestor strings");
  });
  cases.run("standalone export retains its existing source-tree depth bound",
            [] {
              Type term(K::Index);
              for (unsigned i = 0; i < 33; ++i) {
                Type array(K::Array);
                array.arguments.push_back(std::move(term));
                term = std::move(array);
              }
              take(encodeStaticTerm(leaf(term)));
              Limits limits;
              bool debited = false;
              refuses(encodeStaticTerm(leaf(term), limits, limits.work,
                                       [&](uint64_t) {
                                         debited = true;
                                         return Error::success();
                                       }),
                      "source.limit");
              require(!debited,
                      "budgeted export exceeded its caller depth before debit");
            });
  cases.run(
      "inference reconstruction cache is owned and cumulatively bounded", [] {
        auto tree = product({leaf(Type(K::Record, std::string(2048, 'x')))});
        Context c;
        TypeInference solver(c.types);
        auto variable = solver.known(tree, {});
        require(solver.get(variable, {}) == tree, "cache prime failed");
        auto copy =
            take(typeComplexity(tree, c.limits.typeNodes, c.limits.typeDepth,
                                UINT64_MAX, nullptr, true, TypeWork::Copy));
        uint64_t remaining = 2 * copy;
        c.work.allowance = &remaining;
        auto first = solver.get(variable, {});
        require(first == tree && remaining == copy,
                "cache hit redid equation traversal or lost copy debit");
        first->arguments.clear();
        require(solver.get(variable, {}) == tree && remaining == 0,
                "caller mutation changed trusted cached candidate");
        remaining = copy - 1;
        {
          AllocationObservation observing;
          refused(c, solver.get(variable, {}).has_value(), "source.limit");
        }
        require(observedAllocationBytes < 2048,
                "cache copied before current debit");
        c.types.diagnostic.reset();
        c.work.allowance = nullptr;
        c.limits.typeNodes = 2;
        refused(c, solver.get(variable, {}).has_value(), "source.limit");
      });
  cases.run("extent normalization preserves overflow refusal", [] {
    Context c;
    auto extent = atom("owner::N");
    extent.domain.clear();
    extent.dimension =
        take(c.types.naturals.multiply(Natural::constant(2), extent.dimension));
    refused(c,
            c.types
                .substitute(sequence(leaf(), extent),
                            {{"owner::N",
                              natural(std::numeric_limits<uint64_t>::max())}},
                            {})
                .has_value(),
            "source.natural");
  });
  cases.run(
      "inference checkpoint retains every child without refunding work", [] {
        Context c;
        TypeInference solver(c.types);
        auto extent = solver.fresh({});
        auto pattern =
            product({sequence(leaf(), atom("owner::N")), sequence(leaf())});
        auto a = product({sequence(leaf(), natural(3)), sequence(leaf())});
        auto b = product({sequence(leaf(), natural(5)), sequence(leaf())});
        auto variable = solver.instantiate(pattern, {{"owner::N", extent}}, {});
        auto checkpoint = solver.checkpoint({});
        require(checkpoint && solver.equal(variable, solver.known(a, {}), {}),
                "initial structural inference failed");
        auto spent = c.work.used;
        require(solver.restore(*checkpoint, {}) && c.work.used > spent &&
                    solver.equal(variable, solver.known(b, {}), {}) &&
                    solver.get(variable, {}) == b &&
                    solver.get(extent, {}) == natural(5),
                "retry retained old extent or refunded work");
      });
  cases.run("bound module member substitution reaches all nested extents", [] {
    Parameter owner{}, member{}, implementation{};
    owner.sort = member.sort = implementation.sort = Parameter::Sort::Natural;
    owner.atom = "interface::N";
    member.atom = "member::N";
    implementation.atom = "implementation::Width";
    std::vector<Declaration> declarations(3);
    auto &interface = declarations[0], &callee = declarations[1],
         &module = declarations[2];
    interface.id = {0};
    interface.kind = Declaration::Kind::Interface;
    interface.qualifiedName = "m::Interface";
    interface.parameters = {owner};
    callee.id = {1};
    callee.kind = Declaration::Kind::View;
    callee.parent = interface.id;
    callee.qualifiedName = "m::Interface::advance";
    callee.parameters = {member};
    module.id = {2};
    module.kind = Declaration::Kind::Module;
    module.qualifiedName = "m::Implementation";
    module.parameters = {implementation};
    Type implemented(K::Module, interface.qualifiedName);
    implemented.arguments = {atom(implementation.atom)};
    module.implementation = implemented;
    Type selected(K::Module, module.qualifiedName);
    selected.arguments = {natural(7)};
    Limits limits;
    Work work{limits};
    Semantics types(declarations, {}, work);
    auto bindings = types.boundMemberSubstitution(callee, selected, {});
    require(bindings.has_value(),
            "bound module did not select its public interface");
    auto pattern = product({sequence(leaf(), atom(member.atom)),
                            sequence(sequence(leaf(), atom(member.atom)))});
    auto actual = types.substitute(pattern, *bindings, {});
    require(actual == product({sequence(leaf(), natural(7)),
                               sequence(sequence(leaf(), natural(7)))}),
            "owner/member substitution skipped a nested extent");
  });
  cases.run("conformance substitutes every structural input and result", [] {
    Context c;
    Declaration required{}, provided{};
    required.kind = provided.kind = Declaration::Kind::View;
    auto pattern = product({leaf(), sequence(leaf(), atom("owner::N"))});
    auto closed = product({leaf(), sequence(leaf(), natural(3))});
    required.descriptorInputs.push_back(
        {"context", DescriptorContract(pattern), {}});
    provided.descriptorInputs.push_back(
        {"context", DescriptorContract(closed), {}});
    required.descriptorResult = DescriptorContract(pattern);
    provided.descriptorResult = DescriptorContract(closed);
    require(memberInputs(c.types, required, provided,
                         {{"owner::N", natural(3)}}, "source.conformance"),
            "valid conformance refused");
    provided.descriptorResult->type.arguments.back().arguments.back() =
        natural(4);
    refused(c,
            memberInputs(c.types, required, provided,
                         {{"owner::N", natural(3)}}, "source.conformance"),
            "source.conformance");
  });
  cases.run(
      "Finite closure witness and cardinality reject structural contracts", [] {
        for (const auto &tree : {product(), product({leaf()}), sequence(leaf()),
                                 sequence(leaf(), natural(0))}) {
          Context c;
          Body body{};
          DescriptorBinding binding{};
          binding.kind = DescriptorBinding::Kind::Product;
          binding.contract = DescriptorContract(tree);
          body.descriptorBindings.push_back(binding);
          require(cardinalityNode(binding).kind ==
                      zkc::facts::DomainKind::Unknown,
                  "structural product entered Finite cardinality opcode");
          auto closed =
              closeDescriptor(c.types, c.declarations, body, 0, {}, {});
          refused(c, closed.has_value(), "source.finite-domain");
          Context witness;
          auto shape = std::make_shared<DescriptorShape>();
          shape->nodes.push_back(binding);
          shape->result = 0;
          DescriptorEnvironment candidate{shape, {}};
          refused(witness,
                  checkDescriptorClosure(witness.types, witness.declarations,
                                         body, 0, {}, {}, candidate),
                  "source.domain-witness");
        }
      });
  cases.run(
      "immutable field results survive deeper queries and owner lifetime", [] {
        std::shared_ptr<const std::vector<TypeField>> retained;
        {
          Context c;
          Declaration record;
          record.id = {0};
          record.kind = Declaration::Kind::Record;
          record.qualifiedName = "m::Record";
          record.fields.push_back(
              {"value", Type(K::Record, std::string(4096, 'x')), true, {}});
          c.declarations.push_back(std::move(record));
          c.types.indexDeclaration(c.declarations.front());
          Type term(K::Record, "m::Record");
          retained = c.types.fields(term, {});
          require(bool(retained), "field expansion failed");
          const auto *address = retained->data();
          auto deeper = c.types.fields(term, {}, 2);
          require(deeper && retained->data() == address && deeper != retained &&
                      deeper->front().type == retained->front().type,
                  "deeper query replaced a borrowed immutable field result");
          auto copy = take(typeComplexity(term, 100, 10, UINT64_MAX, nullptr,
                                          true, TypeWork::Copy));
          uint64_t remaining = 6 + term.domain.size() + copy;
          c.work.allowance = &remaining;
          {
            AllocationObservation observing;
            auto hit = c.types.fields(term, {});
            require(hit == deeper, "cache hit did not share immutable fields");
          }
          require(remaining == 0 && observedAllocationBytes < 4096,
                  "field borrow copied its large retained Type");
          remaining = 100;
          auto projected = c.types.projectionType(term, "value", {});
          refused(c, bool(projected), "source.limit");
        }
        require(retained && retained->front().type.domain.size() == 4096,
                "field result borrowed destroyed semantic storage");
      });
  cases.run("Identity formula covers actual framed key and Natural text", [] {
    NaturalArithmetic arithmetic;
    auto polynomial = atom("N");
    polynomial.dimension =
        take(arithmetic.add(polynomial.dimension, Natural::constant(123)));
    polynomial.domain.clear();
    polynomial.symbolic = true;
    auto tree = sequence(product({leaf(Type(K::Record, "m::Item")), leaf()}),
                         polynomial);
    auto key = typeIdentity(tree);
    uint64_t expected = key.size() + 8;
    std::function<void(const Type &)> inspect = [&](const Type &term) {
      expected += 4 + term.dimension.spelling().size();
      if (term.kind == K::Natural)
        expected += term.domain.size() + term.sort.size();
      else if (term.kind != K::Domain && term.kind != K::Asset)
        expected += term.sort.size();
      for (const auto &child : term.arguments)
        inspect(child);
    };
    inspect(tree);
    require(take(typeComplexity(tree, 100, 20, UINT64_MAX, nullptr, true,
                                TypeWork::Identity)) == expected,
            "Identity disagrees with actual output/auxiliary text sizes");
    Context c;
    uint64_t remaining = expected - 1;
    c.work.allowance = &remaining;
    refused(c, c.types.chargeIdentity(tree, {}), "source.limit");
  });
  cases.run(
      "capability intern cache hits share cumulative Identity allowance", [] {
        Type field(K::Field, std::string(4096, 'F'));
        field.symbolic = true;
        CapabilityBound goal{"Field", {field}, {}};
        Declaration context;
        context.capabilityBounds.push_back(goal);
        auto run = [&](Context &c) {
          return c.types.entails(&context, goal, "source.capability");
        };
        Context measure;
        uint64_t allocated;
        {
          AllocationObservation observing;
          require(run(measure), "valid symbolic capability failed");
        }
        allocated = observedAllocationBytes;
        auto total = measure.work.used;
        Context exact;
        uint64_t remaining = 2 * total;
        exact.work.allowance = &remaining;
        require(run(exact) && run(exact) && remaining == 0,
                "repeated capability queries did not spend the same allowance");
        {
          AllocationObservation observing;
          refused(exact, run(exact), "source.limit");
        }
        require(observedAllocationBytes < 4096,
                "exhausted capability query materialized a key");
        auto copy = take(typeComplexity(field, 100, 10, UINT64_MAX, nullptr,
                                        true, TypeWork::Copy));
        auto identity = take(typeComplexity(field, 100, 10, UINT64_MAX, nullptr,
                                            true, TypeWork::Identity));
        Context shortHit;
        remaining = copy + identity + typeIdentity(field).size() +
                    goal.predicate.size() + 1 + identity - 1;
        shortHit.work.allowance = &remaining;
        {
          AllocationObservation observing;
          refused(shortHit, run(shortHit), "source.limit");
        }
        require(allocated > observedAllocationBytes + 4096,
                "intern hit materialized its second key before Identity debit");
      });
  cases.run("checked comparison continues validation after an early mismatch",
            [] {
              auto expected = product({leaf(), leaf()});
              auto candidate = product({leaf(Type(K::Boolean)), leaf()});
              TypeComparison valid{expected};
              take(typeComplexity(candidate, 100, 20, UINT64_MAX, nullptr, true,
                                  TypeWork::Copy, &valid));
              require(!valid.equal,
                      "checked comparison lost a differing first child");
              candidate.arguments.back().arguments.front().sort = "foreign";
              TypeComparison invalid{expected};
              refuses(typeComplexity(candidate, 100, 20, UINT64_MAX, nullptr,
                                     true, TypeWork::Copy, &invalid),
                      "source.descriptor");
            });
  cases.run("record routing collisions compare full current candidates", [] {
    Context c;
    Declaration record;
    record.id = {0};
    record.kind = Declaration::Kind::Record;
    record.qualifiedName = "m::Record";
    record.parameters.push_back(
        {Parameter::Sort::Type, "T", "m::Record::T", {}, {}, {}, {}, {}});
    Type parameter(K::Parameter, "m::Record::T");
    parameter.symbolic = true;
    record.fields.push_back({"value", parameter, true, {}});
    c.declarations.push_back(std::move(record));
    c.types.indexDeclaration(c.declarations.front());
    Type first(K::Record, "m::Record");
    first.arguments.push_back(Type(K::Field, "abcdefghij"));
    auto second = first;
    second.arguments.front().domain[1] = 'Z';
    // Same lengths and sampled positions deliberately collide. A hash cannot
    // authorize reuse of the first field's distinct static argument.
    auto a = c.types.fields(first, {}), b = c.types.fields(second, {});
    require(a && b && a != b && a->front().type == first.arguments.front() &&
                b->front().type == second.arguments.front() &&
                c.types.fields(first, {}) == a,
            "record routing hash replaced full equality");
    c.limits.typeNodes = 1;
    refused(c, bool(c.types.fields(first, {})), "source.limit");
  });
  cases.run(
      "inference unions move known heads without discarded Type copies", [] {
        Context c;
        TypeInference solver(c.types);
        Type input(K::Record, std::string(4096, 'x'));
        auto known = solver.known(input, {});
        auto unknown = solver.fresh({});
        uint64_t remaining = 8;
        c.work.allowance = &remaining;
        {
          AllocationObservation observing;
          require(solver.equal(known, unknown, {}), "bounded union failed");
        }
        require(observedAllocationBytes < 4096,
                "union copied retained head metadata before discarding it");
        remaining = c.limits.work;
        require(solver.get(unknown, {}) == input, "moved head lost metadata");
        auto another = solver.known(input, {});
        auto copy = take(typeComplexity(input, 100, 10, UINT64_MAX, nullptr,
                                        false, TypeWork::Copy));
        remaining = copy + 8;
        {
          AllocationObservation observing;
          require(solver.equal(known, another, {}), "head comparison failed");
        }
        require(observedAllocationBytes < 4096,
                "head comparison copied either retained Type");
      });
  cases.run(
      "native queries borrow the index without checking hooks or rebuilding it",
      [] {
        auto measured = [](unsigned unused) {
          Limits limits;
          Work work{limits};
          std::vector<Declaration> declarations(3);
          auto &module = declarations[0];
          module.id = {0};
          module.kind = Declaration::Kind::Module;
          module.qualifiedName = "m::M";
          auto &associated = declarations[1];
          associated.id = {1};
          associated.kind = Declaration::Kind::Associated;
          associated.parent = DeclarationId{0};
          associated.qualifiedName = "m::M::Item";
          associated.domain = Type(K::Index);
          auto &record = declarations[2];
          record.id = {2};
          record.kind = Declaration::Kind::Record;
          record.qualifiedName = "m::Record";
          Type item(K::Associated, "m::M::Item");
          item.arguments.push_back(Type(K::Module, "m::M"));
          record.fields.push_back({"value", item, true, {}});
          for (unsigned i = 0; i < unused; ++i) {
            Declaration extra;
            extra.id = {unsigned(declarations.size())};
            extra.kind = Declaration::Kind::Record;
            extra.qualifiedName = "m::Unused" + std::to_string(i);
            declarations.push_back(std::move(extra));
          }
          unsigned hooks = 0;
          Semantics semantics(declarations, {}, work, [&](DeclarationId) {
            ++hooks;
            return false;
          });
          Type type(K::Record, "m::Record");
          require(take(semantics.nativeMessagePayload(type)),
                  "native query inherited an incomplete checking hook");
          auto first = work.used;
          uint64_t remaining = first;
          work.allowance = &remaining;
          require(take(semantics.nativeMessagePayload(type)) && remaining == 0,
                  "native query did not debit the actual cumulative ledger");
          refuses(semantics.nativeMessagePayload(type), "source.limit");
          require(hooks == 0, "native query invoked owner completion hooks");
          return first;
        };
        require(
            measured(0) == measured(96),
            "native query rebuilt the unchanged semantic declaration index");
      });
  cases.run("lexical operator keys retain immutable independent ownership", [] {
    auto captured = take(capture({{"test", "module test;", "test.zkc"}}));
    CheckedStorage storage(captured, "test");
    Declaration callee;
    callee.id = {0};
    callee.kind = Declaration::Kind::Math;
    callee.qualifiedName = "test::add";
    callee.inputs = {{"a", Type(K::Index), {}, {}},
                     {"b", Type(K::Index), {}, {}}};
    callee.outputs = {{"out", Type(K::Index), {}, {}}};
    storage.declarations.push_back(callee);
    auto notation = std::make_shared<NotationDescriptor>();
    notation->position = NotationDescriptor::Position::Infix;
    notation->association = NotationDescriptor::Association::Left;
    notation->symbol = "+";
    notation->arity = 2;
    notation->precedence = 65;
    SyntaxDeclaration syntax;
    syntax.bodies.resize(1);
    auto environment = std::make_shared<NotationEnvironment>();
    environment->emplace(notation->key(), NotationSyntax{notation, {}});
    syntax.bodies[0].notationEnvironment = environment;
    OperatorBinding binding{"+", {{0}, {}}, {}, {}, notation};
    Type module(K::Module, "test::M");
    module.arguments.push_back(Type(K::Record, std::string(4096, 'a')));
    binding.target.module = module;
    syntax.bodies[0].resolvedOperators.push_back(binding);
    Expression expression;
    expression.kind = Expression::Kind::NotationCall;
    expression.notation = notation;
    expression.scope = 0;
    expression.children = {0, 0};
    syntax.expressions.push_back(expression);
    Limits limits;
    Work work{limits};
    std::shared_ptr<const AuthoredOperatorFamily> family;
    {
      Checker checker(storage, work, ImportBindingAccess{{0}, UINT32_MAX});
      family = checker.operatorWitnessFamily(callee, syntax, 0);
      require(bool(family), "independent lexical family refused");
    }
    // Source and solver-owned candidates cannot mutate the frozen bindings.
    syntax.bodies[0].resolvedOperators[0].target.module->domain = "changed";
    notation->precedence = 70;
    require(family->entries()[0].target.module == binding.target.module &&
                family->entries()[0].notation->precedence == 65,
            "frozen family retained a mutable source alias");
    notation->precedence = 65;
    CallBinding witness;
    witness.target = binding.target;
    witness.symbol = "+";
    witness.notation = *notation;
    witness.origin = binding.span;
    witness.operands = {{0}, {1}};
    witness.family = family->keys().vec();
    Semantics types(storage.declarations, {}, work);
    auto check = [&] {
      return checkOperatorWitness(
          types, storage.declarations, *family, *notation, witness,
          {Type(K::Index), Type(K::Index)}, Type(K::Index), {});
    };
    auto before = work.used;
    require(check(), "frozen family did not survive checker lifetime");
    uint64_t cost = work.used - before, remaining = cost;
    work.allowance = &remaining;
    require(check() && remaining == 0,
            "frozen witness did not charge cumulatively");
    remaining = cost - 1;
    require(!check() && types.diagnostic &&
                types.diagnostic->code == "source.limit",
            "frozen witness admitted exhausted actual Work");
    types.diagnostic.reset();
    remaining = limits.work;
    witness.family[0].back() ^= 1;
    require(!check() && types.diagnostic &&
                types.diagnostic->code == "source.binding-witness",
            "frozen key admitted a mutable candidate key mutation");
    witness.family = family->keys().vec();
    types.diagnostic.reset();
    limits.typeNodes = 1;
    require(!check() && types.diagnostic &&
                types.diagnostic->code == "source.limit",
            "frozen family skipped this consumer's complete current bounds");
  });
  cases.run(
      "projection paths borrow intermediates and copy only the result", [] {
        Context c;
        Declaration owner;
        Type root(K::Tuple);
        Type inner(K::Tuple);
        inner.arguments = {Type(K::Record, std::string(4096, 'x')),
                           Type(K::Index)};
        root.arguments = {std::move(inner), Type(K::Index)};
        std::optional<Type> selected;
        {
          AllocationObservation observing;
          selected = c.types.projectedType(owner, root, {0, 1}, {});
        }
        require(selected == Type(K::Index),
                "borrowed projection selected the wrong Type");
        require(
            observedAllocationBytes < 4096,
            "projection copied an unselected or intermediate owned subtree");
        root.arguments[0].arguments[1] = Type(K::Unit);
        require(selected == Type(K::Index),
                "projection result retained an input alias");
        require(!c.types.projectedType(owner, root, {2}, {}) &&
                    c.types.diagnostic &&
                    c.types.diagnostic->code == "source.index",
                "borrowed projection admitted an out-of-range tuple index");
      });
  cases.run(
      "record projection checks complete phantom arguments on every query", [] {
        std::vector<Declaration> declarations(1);
        auto &record = declarations[0];
        record.id = {0};
        record.kind = Declaration::Kind::Record;
        record.qualifiedName = "m::Record";
        record.fields.push_back({"value", Type(K::Index), true, {}});
        Limits limits;
        Work work{limits};
        Semantics types(declarations, {}, work);
        Type candidate(K::Record, record.qualifiedName);
        candidate.arguments.push_back(Type(K::Index));
        require(types.projectedType(record, candidate, {0}, {}) ==
                    Type(K::Index),
                "valid record projection refused");
        candidate.arguments[0] = product({Type(K::Index)});
        require(
            !types.projectedType(record, candidate, {0}, {}) &&
                types.diagnostic &&
                types.diagnostic->code == "source.descriptor",
            "projection cache concealed invalid unselected candidate metadata");
      });
  cases.run(
      "maximal inherent permissions avoid parameter scans but check bound "
      "Types",
      [] {
        auto measured = [](unsigned count) {
          std::vector<Declaration> declarations(1);
          auto &record = declarations[0];
          record.id = {0};
          record.kind = Declaration::Kind::Record;
          record.qualifiedName = "m::Copyable";
          record.fields.push_back({"value", Type(K::Index), true, {}});
          Declaration scope;
          for (unsigned i = 0; i < count; ++i) {
            Parameter parameter;
            parameter.sort = Parameter::Sort::Type;
            parameter.atom = "parameter:m::Unused::T" + std::to_string(i);
            scope.parameters.push_back(std::move(parameter));
          }
          Limits limits;
          Work work{limits};
          Semantics types(declarations, {}, work);
          Type candidate(K::Parameter, "parameter:m::Scope::T");
          candidate.symbolic = true;
          candidate.assumptions = {true, false};
          auto result = types.permissions(candidate, {}, &scope);
          require(result && result->copy && result->drop,
                  "inherent permissions lost");
          auto cost = work.used;
          candidate.assumptions = {};
          Parameter matching;
          matching.sort = Parameter::Sort::Type;
          matching.atom = candidate.domain;
          matching.permissions = {true, true};
          scope.parameters.push_back(matching);
          auto granted = types.permissions(candidate, {}, &scope);
          require(granted && granted->copy && granted->drop,
                  "nonmaximal permissions skipped the matching parameter");
          candidate.assumptions = {true, false};
          auto malformed = leaf();
          malformed.arguments[0].sort = "foreign";
          scope.permissionBounds.push_back({malformed, {true, true}, {}});
          require(
              !types.permissions(candidate, {}, &scope) && types.diagnostic &&
                  types.diagnostic->code == "source.descriptor",
              "maximal permissions skipped a required complete bound check");
          return cost;
        };
        require(measured(0) == measured(96),
                "inherent Copy still scanned irrelevant parameter names");
      });
  return cases.result();
}
