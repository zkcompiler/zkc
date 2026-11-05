#include "../lib/Language/Conformance.h"
#include "../lib/Language/DescriptorClosure.h"
#include "../lib/Language/DescriptorWitness.h"
#include "../lib/Language/FiniteCardinality.h"
#include "../lib/Language/TypeInference.h"
#include "support/NativeCases.h"
#include "zkc/Language/SourceTerms.h"
#include <limits>

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
                      frontendTypeConstructor(tree) ==
                          (tree.kind == K::DescriptorProduct
                               ? "descriptor_product"
                               : "descriptor_sequence"),
                  "structural category or installed head projection differs");
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
  return cases.result();
}
