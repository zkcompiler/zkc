#include "../lib/Frontend/Library/Internal.h"
#include "../lib/Frontend/Model/Module.h"
#include "../lib/Frontend/Static/Domains.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/TypeProperties.h"
#include "zkc/Frontend/Analysis.h"
#include "zkc/Frontend/Protocol.h"
#include "zkc/Protocol/Instantiation.h"
#include "zkc/Source/Codec.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace zkc;
using namespace zkc::frontend;
namespace lib = zkc::frontend::library;
namespace {
unsigned checks = 0, failures = 0;
void expect(bool condition, const Twine &description) {
  ++checks;
  if (!condition) {
    ++failures;
    errs() << "FAIL: " << description << '\n';
  }
}
bool complete(const Analysis &analysis) {
  expect(analysis.complete(), "source completes");
  if (!analysis.complete())
    for (const auto &d : analysis.diagnostics())
      errs() << d.code << ": " << d.message << '\n';
  return analysis.complete();
}
void refused(StringRef text, StringRef code, StringRef message = {}) {
  auto analysis = analyzeProtocol(text, "static-refusal.pir");
  expect(!analysis.complete(), "invalid static source refuses");
  expect(any_of(analysis.diagnostics(),
                [&](const auto &d) {
                  return d.code == code &&
                         StringRef(d.message).contains(message);
                }),
         "refusal identifies " + code + " and " + message);
  if (analysis.complete() ||
      none_of(analysis.diagnostics(), [&](const auto &d) {
        return d.code == code && StringRef(d.message).contains(message);
      }))
    for (const auto &d : analysis.diagnostics())
      errs() << d.code << ": " << d.message << '\n';
}
void refusal(Error error, StringRef code) {
  expect(bool(error), "expected " + code);
  if (error) {
    auto message = toString(std::move(error));
    expect(StringRef(message).split(':').first == code,
           "expected " + code + ", got " + message);
  }
}
void noForgedDomains(const Analysis &analysis) {
  expect(none_of(analysis.domains(),
                 [](const auto &domain) {
                   return domain.sort == "Type" || domain.sort == "Nat" ||
                          domain.name == "F";
                 }),
         "Type/Nat arguments and callee field names create no caller domains");
}
void modelArguments() {
  model::Module model;
  auto owner = model.add(Declaration::Kind::Function, {0}, "Owner");
  auto scope = model.declarations[owner.index].members;
  auto parameter = [&](StringRef name, StringRef sort) {
    auto id = model.add(Declaration::Kind::Parameter, scope, name);
    model.declarations[id.index].sort = sort.str();
    return id;
  };
  auto element = parameter("Element", "Type");
  auto length = parameter("Length", "Nat");
  auto field = parameter("Scalar", "Field");
  auto symbolic = model.logical("fixed_vector<Element,Length>", scope);
  auto boolean = model.logical("bool", {0});
  auto koala = model.internDomain("koala-bear", {0});
  auto selected =
      model.substitute(symbolic, {{element, StaticArgument::typeOf(boolean)},
                                  {length, StaticArgument::natural(7)}});
  expect(model.spelling(selected) == "fixed_vector<bool,7>",
         "kinded substitution preserves nested Type and Nat actuals");
  auto typeRoot = model.logical("Element", scope);
  auto domainRoot = model.internDomain("Scalar", scope);
  auto naturalRoot = StaticArgument::natural(0, length);
  expect(model.substitute(typeRoot, {{element, koala}}) == typeRoot,
         "wrong-kind Type replacement never returns an invalid TypeId");
  expect(model.substitute(domainRoot,
                          {{field, StaticArgument::typeOf(boolean)}}) ==
             domainRoot,
         "wrong-kind Domain replacement never returns an invalid DomainId");
  auto natural = model.substitute(naturalRoot, {{length, koala}});
  expect(natural.kind == StaticArgument::Kind::Natural &&
             natural.parameter == length,
         "wrong-kind Nat replacement preserves its kind");
  expect(
      model.diagnostics.size() == 3 &&
          all_of(model.diagnostics,
                 [](const auto &d) { return d.code == "source-static-sort"; }),
      "each wrong-kind substitution records a refusal");
  auto invalidType =
      model.substitute(typeRoot, {{element, StaticArgument::typeOf({})}});
  expect(invalidType == typeRoot && model.diagnostics.size() == 4,
         "invalid replacement IDs refuse explicitly");
  model.diagnostics.clear();
  expect(model.substitute(typeRoot, {{element, StaticArgument::natural(1)}}) ==
             typeRoot,
         "Nat cannot replace a Type parameter");
  expect(model.substitute(domainRoot, {{field, StaticArgument::natural(1)}}) ==
             domainRoot,
         "Nat cannot replace a Domain parameter");
  auto wrongNatural = model.substitute(
      naturalRoot, {{length, StaticArgument::typeOf(boolean)}});
  expect(wrongNatural.kind == StaticArgument::Kind::Natural &&
             wrongNatural.parameter == length,
         "Type cannot replace a Nat parameter");
  expect(model.diagnostics.size() == 3,
         "all six kind mismatch directions diagnose");
  model.diagnostics.clear();
  auto product = model.product({symbolic});
  auto unchanged =
      model.substitute(product, {{length, StaticArgument::typeOf(boolean)}});
  expect(
      unchanged == product &&
          model.leaves({"x", {}, unchanged, {}}).size() == 1 &&
          model.diagnostics.size() == 1,
      "nested mismatch records a refusal without corrupting product layouts");
  auto missing = model.logical("fixed_vector<bool,Missing>", scope);
  expect(!missing.valid() &&
             model.diagnostics.back().code == "source-static-sort",
         "unbound natural refuses without a fatal error");
  auto unknown = model.logical("Uninstalled", scope);
  expect(!unknown.valid() && model.diagnostics.back().code == "source-type",
         "unknown constructor is not interned as a logical type");
}
void domainProducts() {
  auto analysis = analyzeProtocol(R"(
    use zkc::algebra::{Vector, Field, vector_split};
    fn Split<G: Field>(x: Vector<G::Element>) -> (Vector<G::Element>, Vector<G::Element>) {
      let pair = vector_split::<G>(x);
      return pair;
    }
  )",
                                  "domain-product.pir");
  if (!complete(analysis))
    return;
  expect(none_of(analysis.domains(),
                 [](const auto &d) {
                   return d.name == "F" && d.kind == Domain::Kind::Identity;
                 }),
         "multi-output calls do not intern phantom callee domains");
  bool product = false;
  for (const auto &binding : analysis.bindings())
    if (binding.name == "pair")
      product = analysis.display(binding.type) == "(vector:G, vector:G)";
  expect(product, "packed multi-output result uses solved caller statics");
}
lib::Environment environment() {
  lib::Environment env;
  lib::LibraryId owner{"test", "static-arguments", "1", "captured"};
  lib::QualifiedDecl field{owner, {}, "Field"};
  env.libraries.push_back({owner, {field}});
  env.statics.push_back(
      {field, lib::Sort::domainOf("Field"), {}, {}, {}, {}, true});
  for (const auto &operation : protocol::boundOperationContracts())
    env.operations.push_back(
        {operation, {protocol::operationEffect(operation.name).str()}});
  return env;
}
void constants() {
  auto env = environment();
  for (StringRef value : {"resource_unit:A", "resource_unit:B",
                          "fixed_vector<resource_unit:A,4>"}) {
    auto result = lib::staticConstant("Type", value, env);
    refusal(result.takeError(), "library-static-sort");
  }
  auto accepted = lib::staticConstant("Type", "fixed_vector<bool,4>", env);
  expect(bool(accepted), "common Type constants preserve their arguments");
  if (!accepted)
    consumeError(accepted.takeError());
}
void literals() {
  auto env = environment();
  auto field = lib::StaticTerm::root(env.statics.front().id);
  lib::LogicalCall call{"field.constant", {field}};
  for (StringRef value : {"0", "1"}) {
    auto generic =
        protocol::checkGenericParameters(call.operation, {value.str()});
    expect(!generic, "Contracts validates the field-independent literal");
    if (generic)
      errs() << toString(std::move(generic)) << '\n';
    auto error = lib::detail::checkAttributes(call, {value.str()}, env);
    expect(!error, "generic literal " + value + " is field independent");
    if (error)
      errs() << toString(std::move(error)) << '\n';
  }
  refusal(lib::detail::checkAttributes(call, {"2"}, env),
          "library-attribute-bound");
  refusal(lib::detail::checkAttributes(call, {"01"}, env),
          "library-attribute-bound");
  refusal(lib::detail::checkAttributes(call, {}, env),
          "library-operation-attributes");
  refusal(lib::detail::checkAttributes(call, {"0", "1"}, env),
          "library-operation-attributes");
  auto vector = lib::detail::checkAttributes({"vector.constant", {field}},
                                             {"0", "1", "0"}, env);
  expect(!vector,
         "generic literal vectors use the same field-independent validation");
  if (vector)
    errs() << toString(std::move(vector)) << '\n';
  refusal(protocol::checkParameters("field.constant", {"2"}),
          "interactive-constant");
  refusal(protocol::checkParameters("field.constant", {"0"}),
          "interactive-constant");
  env.statics.front().parameter = false;
  env.statics.front().capturedSubject = "koala-bear";
  refusal(lib::detail::checkAttributes(call, {"2130706433"}, env),
          "library-operation-attributes");
  refusal(protocol::checkParameters("field.constant", {"1"}, "unknown-field"),
          "interactive-constant");
}
void protocolTemplates() {
  auto analysis = analyzeProtocol(R"(
    use zkc::algebra::FixedVector;
    fn Keep<V: Type, L: nat>(x: FixedVector<V,L>) -> FixedVector<V,L> { x }
    protocol Bulk<T: Type, N: nat> {
      roles(P); inputs(P x: FixedVector<T,N>); outputs(P FixedVector<T,N>);
      local [keep] P: let y = Keep::<T,N>(x);
      let [place] z = local P { y };
      return z;
    }
    protocol Root<T: Type, N: Nat> {
      roles(P); inputs(P x: T); outputs(P T);
      let [place] y = local P { x };
      return y;
    }
    protocol Outer<U: Type, K: nat> {
      roles(P); inputs(P x: FixedVector<U,K>); outputs(P FixedVector<U,K>);
      dependencies(child: Bulk::<T=U,N=K>());
      invoke [child] child(x) -> (y);
      return y;
    }
  )",
                                  "protocol-static-templates.pir");
  if (!complete(analysis))
    return;
  noForgedDomains(analysis);
  bool type = false, natural = false;
  for (const auto &use : analysis.uses())
    for (const auto &binding : use.bindings) {
      type |= binding.argument.kind == StaticArgument::Kind::Type;
      natural |= binding.argument.kind == StaticArgument::Kind::Natural;
    }
  expect(type && natural,
         "template calls and placement preserve both static kinds");
  auto lowered = analysis.lower();
  expect(bool(lowered), "checked generic protocol templates lower");
  if (!lowered)
    consumeError(lowered.takeError());
}
void protocols() {
  constexpr StringLiteral text = R"(
    use zkc::algebra::FixedVector;
    fn Keep<V: Type, L: nat>(x: FixedVector<V, L>) -> FixedVector<V, L> { x }
    protocol Child<T: Type, N: nat> {
      roles (P); inputs (P x: FixedVector<T, N>); outputs (P FixedVector<T, N>);
      local [copy] P: let y = Keep::<T, N>(x);
      let [place] z = local P { y };
      return z;
    }
    protocol Parent<U: Type, K: Nat> {
      roles (P); inputs (P x: FixedVector<U, K>); outputs (P FixedVector<U, K>);
      dependencies (child: Child::<T=U, N=K>());
      invoke [child] child(x) -> (y);
      return y;
    }
    configure Selected = Parent(U=bool, K=4);
    instance child: Selected::child { roles (P=Prover); }
    instance run: Selected { dependencies(child=child); roles (P=Prover); }
    entry main = run;
  )";
  for (auto choice : {std::pair<StringRef, StringRef>{"bool", "bool"},
                      {"\"koala-bear\"::Element", "field:koala-bear"},
                      {"FixedVector<\"koala-bear\"::Element,2>",
                       "fixed_vector<field:koala-bear,2>"}}) {
    std::string selected = text.str();
    selected.replace(selected.find("U=bool"), 6, "U=" + choice.first.str());
    selected.replace(selected.find("K=4"), 3, "K=WIDTH");
    selected.insert(0, "const WIDTH: index = 4; const K: index = 9;");
    auto analysis = analyzeProtocol(selected, "protocol-statics.pir");
    if (!complete(analysis))
      continue;
    noForgedDomains(analysis);
    bool typed = false, natural = false;
    for (const auto &origin : analysis.instantiations())
      for (const auto &binding : origin.bindings) {
        typed |= binding.argument.kind == StaticArgument::Kind::Type;
        natural |= binding.argument.kind == StaticArgument::Kind::Natural;
      }
    expect(typed && natural,
           "specialization provenance retains argument kinds");
    auto lowered = analysis.lower();
    expect(bool(lowered), "kinded protocols lower");
    if (!lowered) {
      consumeError(lowered.takeError());
      continue;
    }
    auto formatted = formatProtocol(selected);
    expect(bool(formatted), "kinded protocol source formats");
    if (formatted) {
      auto roundtrip = analyzeProtocol(*formatted, "formatted-statics.pir");
      if (complete(roundtrip)) {
        auto again = roundtrip.lower();
        expect(bool(again), "formatted protocol lowers");
        if (again)
          expect(source::encode(*lowered) == source::encode(*again),
                 "formatting preserves kinded protocol lowering");
        else
          consumeError(again.takeError());
      }
    } else
      consumeError(formatted.takeError());
    const auto &module = std::get<source::Module>(*lowered);
    expect(
        any_of(module.protocols,
               [&](const auto &protocol) {
                 return protocol.name == "Selected" &&
                        protocol.arguments.size() == 1 &&
                        protocol.arguments.front().type ==
                            "fixed_vector<" + choice.second.str() + ",4>";
               }),
        "configured protocol ports have the exact nested Type/Nat selection");
    auto specialized = generic::elaborateLibrary(module);
    expect(bool(specialized),
           "Type/Nat placement helpers specialize through common generics");
    if (!specialized)
      errs() << toString(specialized.takeError()) << '\n';
  }
  for (auto selection :
       {std::pair<StringRef, StringRef>{"U=4, K=4", "source-static-sort"},
        {"U=bool, K=bool", "source-static-sort"},
        {"U=bool, K=\"4\"", "source-name-unresolved"},
        {"U=FixedVector<bool,04>, K=4", "source-number"}}) {
    auto invalid = text.str();
    invalid.replace(invalid.find("U=bool, K=4"), 11, selection.first.str());
    refused(invalid, selection.second);
  }
}
void diagnostics() {
  refused(R"(
    use zkc::algebra::{Field, Vector, FixedVector, fixed_vector_from_vector};
    fn Produce<F: Field, N: nat>(x: Vector<F::Element>) -> FixedVector<F::Element,N> {
      fixed_vector_from_vector::<F,N>(x)
    }
    fn Caller(x: Vector<"koala-bear"::Element>) -> () {
      let value = Produce(x); return;
    }
  )",
          "source-static-unresolved", "annotate this call's result type");
  refused(R"( use zkc::algebra::{Vector, FixedVector};
    fn Bad(x: Vector<FixedVector<bool,4>>) -> () { return; }
  )",
          "source-type", "fixed_vector<bool,4>");
  refused(R"( protocol Bad<T: Type + nat> { roles(P); return; } )",
          "source-bound-sort");
}
} // namespace
int main() {
  auto catalog = protocol::DomainCatalog::create(
      {{"F", "Field", {}, {"Field"}}}, {}, {}, {});
  expect(bool(catalog), "identifier-shaped installed domain is legal");
  if (catalog) {
    expect(!representableStaticBinder("F", *catalog),
           "static binder cannot capture an installed exact identity");
    expect(representableStaticBinder("G", *catalog),
           "a distinct static binder remains representable");
  } else
    consumeError(catalog.takeError());

  modelArguments();
  domainProducts();
  constants();
  literals();
  protocolTemplates();
  protocols();
  diagnostics();
  outs() << checks << " checks, " << failures << " failures\n";
  return failures ? 1 : 0;
}
