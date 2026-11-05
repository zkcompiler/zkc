#include "../lib/Language/Semantics.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include <algorithm>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::language::detail;
using namespace zkc::test;
namespace {
Expected<CheckedProject> check(const Twine &source, bool layout = true,
                               Limits limits = {}) {
  CaptureOptions options;
  options.format = layout ? "zkc-layout" : "zkc";
  auto captured = capture({{"m", source.str(), "members.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return const_cast<Declaration &>(decl);
  throw std::runtime_error("missing declaration " + name.str());
}
void witness(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
Type natural(unsigned n) {
  Type type(Type::Kind::Natural);
  type.dimension = Natural::constant(n);
  return type;
}
Type module(StringRef name, std::vector<Type> arguments = {}) {
  Type type(Type::Kind::Module, name.str());
  type.arguments = std::move(arguments);
  return type;
}
const char *mathSource = R"(domain Fr = field("koala-bear")
interface Scalars<F: Field>:
    type Scalar: Field
module ScalarImpl<F: Field>: Scalars<F>:
    type Scalar = F
interface Ops<F: Field>:
    type Scalar: Field
    def echo<T: Type + Copy + Drop, N: nat, C: Scalars<F>>(x: T, xs: [C::Scalar; N]) -> T
module Impl<K: nat, F: Field>: Ops<F>:
    type Scalar = F
    def echo<U: Type + Copy + Drop, M: nat, D: Scalars<F>>(x: U, xs: [D::Scalar; M]) -> U:
        x
def apply<F: Field, C: Ops<F>, T: Type + Copy + Drop, N: nat, B: Scalars<F>>(x: T, xs: [B::Scalar; N]) -> T:
    C::echo<T, N, B>(x, xs)
pub protocol Demo roles(P)(x: bool @P, xs: [Fr; 2] @P) -> bool @P:
    return apply<Fr, Impl<7, Fr>, bool, 2, ScalarImpl<Fr>>(x, xs)
)";
const char *protocolSource = R"(domain Fr = field("koala-bear")
interface Wire<F: Field>:
    type Scalar: Field
    protocol pass<T: Type + Copy + Drop, N: nat> roles(A)(x: [T; N] @A, y: Scalar @A) -> [T; N] @A effects()
module WireImpl<K: nat, F: Field>: Wire<F>:
    type Scalar = F
    protocol pass<U: Type + Copy + Drop, M: nat> roles(B)(x: [U; M] @B, y: Scalar @B) -> [U; M] @B:
        return x
pub protocol Demo<F: Field, C: Wire<F>, T: Type + Copy + Drop, N: nat> roles(P)(x: [T; N] @P, y: C::Scalar @P) -> [T; N] @P:
    result <- C::pass<T, N>(x, y) @P
    return result
)";
} // namespace
int main() {
  Cases cases;
  cases.run("alpha renamed type natural module and associated paths", [] {
    auto project = take(check(mathSource));
    witness(project);
    auto closed = take(closeNativeRun(project, "m::Demo"));
    take(prepareOriginal(closed));
    bool selected = false;
    for (const auto &decl : closed.declarations())
      if (decl.origin &&
          decl.origin->index == named(project, "m::Impl::echo").id.index) {
        selected = true;
        require(
            decl.staticArguments.size() == 5 &&
                decl.staticArguments[0] == natural(7) &&
                decl.staticArguments[2] == Type(Type::Kind::Boolean) &&
                decl.staticArguments[3] == natural(2) &&
                decl.staticArguments[4] ==
                    module("m::ScalarImpl", {named(project, "m::Fr").domain}),
            "closed implementation lost owner or member arguments");
      }
    require(selected, "no implementing member was instantiated");
  });
  cases.run("generic Protocol dispatch closes owner and member arguments", [] {
    auto project = take(check(protocolSource));
    witness(project);
    auto field = named(project, "m::Fr").domain;
    auto closed =
        take(closeNativeRun(project, "m::Demo", {},
                            {field, module("m::WireImpl", {natural(7), field}),
                             Type(Type::Kind::Boolean), natural(2)}));
    take(prepareOriginal(closed));
    bool selected = false;
    for (const auto &decl : closed.declarations())
      if (decl.origin &&
          decl.origin->index == named(project, "m::WireImpl::pass").id.index) {
        selected = true;
        require(decl.staticArguments ==
                    std::vector<Type>({natural(7), field,
                                       Type(Type::Kind::Boolean), natural(2)}),
                "Protocol dispatch did not retain both telescopes");
      }
    require(selected, "Protocol call retained its abstract member");
  });
  cases.run("member binder cannot capture an equally named owner binder", [] {
    auto project = take(check(R"(interface I<A: Type + Copy + Drop>:
    def choose<B: Type + Copy + Drop>(x: A, y: B) -> B
module M<B: Type + Copy + Drop>: I<B>:
    def choose<A: Type + Copy + Drop>(x: B, y: A) -> A:
        y
pub protocol Demo roles(P)(x: bool @P, y: index @P) -> index @P:
    return M::choose<bool, index>(x, y)
)"));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  for (StringRef declaration :
       {"def keep(x: bool) -> bool:\n        x\n",
        "def keep<U: Type + Copy + Drop, V: nat>(x: U) -> U:\n        x\n",
        "def keep<U: nat>(x: bool) -> bool:\n        x\n",
        "def keep<U: Field>(x: U) -> U:\n        x\n",
        "local def keep<U: Type + Copy + Drop>(x: U) -> U:\n        x\n",
        "def keep<U: Type + Copy + Drop>(x: U) -> bool:\n        true\n"})
    cases.run("universal binder or mode mismatch: " + declaration, [&] {
      refuses(check("interface I:\n    def keep<T: Type + Copy + Drop>(x: T) "
                    "-> T\nmodule M: I:\n    " +
                    declaration),
              "source.conformance");
    });
  cases.run("stronger parameter permission is not its own premise", [] {
    refuses(check(R"(interface I:
    local def keep<T: Type>(x: T) -> T effects()
module M: I:
    local def keep<U: Type + Copy>(x: U) -> U:
        return x
)"),
            "source.conformance");
  });
  cases.run("weaker member permissions follow the interface promises", [] {
    auto project = take(check(R"(interface I:
    local def keep<T: Type + Copy + Drop>(x: T) -> T effects()
module M: I:
    local def keep<U: Type>(x: U) -> U:
        return x
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    value <- M::keep<bool>(x)
    return value
)"));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("a later module binder specializes an earlier natural binder", [] {
    auto project = take(check(R"(domain Fr = field("koala-bear")
interface Family<N: nat>:
    type Value: Field
module Values<N: nat>: Family<N>:
    type Value = Fr
interface I:
    def keep<N: nat, C: Family<N>>(x: [C::Value; N]) -> [C::Value; N]
module M<K: nat>: I:
    def keep<L: nat, D: Family<L>>(x: [D::Value; L]) -> [D::Value; L]:
        x
def apply<C: I>(x: [Fr; 2]) -> [Fr; 2]:
    C::keep<2, Values<2>>(x)
pub protocol Demo roles(P)(x: [Fr; 2] @P) -> [Fr; 2] @P:
    return apply<M<7>>(x)
)"));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("stronger natural premise is refused universally", [] {
    refuses(check(R"(interface I:
    def keep<N: nat>(x: bool) -> bool where 1 <= N
module M: I:
    def keep<K: nat>(x: bool) -> bool where 2 <= K:
        x
)"),
            "source.bound");
  });
  cases.run("weaker natural premise follows renamed interface premise", [] {
    auto project = take(check(R"(interface I:
    def keep<N: nat>(x: bool) -> bool where 2 <= N
module M: I:
    def keep<K: nat>(x: bool) -> bool where 1 <= K:
        x
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    return M::keep<2>(x)
)"));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("stronger capability premise is refused universally", [] {
    refuses(check(R"(interface I:
    def keep<F: Field>(x: F) -> F
module M: I:
    def keep<G: Field>(x: G) -> G where zkc::algebra::TwoAdicField(G):
        x
)"),
            "source.conformance");
  });
  cases.run("renamed capability premise is available to implementation", [] {
    auto project = take(check(R"(interface I:
    def keep<F: Field>(x: F) -> F where zkc::algebra::TwoAdicField(F)
module M: I:
    def keep<G: Field>(x: G) -> G where zkc::algebra::TwoAdicField(G):
        x
domain Fr = field("koala-bear")
pub protocol Demo roles(P)(x: Fr @P) -> Fr @P:
    return M::keep<Fr>(x)
)"));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run("stronger associated permission premise is refused", [] {
    refuses(check(R"(interface Item:
    type Value: Drop
interface I:
    local def keep<C: Item>(x: C::Value) -> C::Value effects()
module M: I:
    local def keep<D: Item>(x: D::Value) -> D::Value where Copy(D::Value):
        return x
)"),
            "source.conformance");
  });
  for (StringRef constraint : {"Family<1>", "Other<K>"})
    cases.run("member module constraint must be exact: " + constraint, [&] {
      refuses(check("interface Family<N: nat>:\n    type Value: Field\n"
                    "interface Other<N: nat>:\n    type Value: Field\n"
                    "interface I:\n    def keep<N: nat, C: Family<N>>(x: bool) "
                    "-> bool\n"
                    "module M: I:\n    def keep<K: nat, D: " +
                    constraint + ">(x: bool) -> bool:\n        x\n"),
              "source.conformance");
    });
  cases.run("a concrete field does not implement every generic field", [] {
    refuses(check(R"(domain Fr = field("koala-bear")
interface I:
    def keep<F: Field>(x: F) -> F
module M: I:
    def keep<G: Field>(x: Fr) -> Fr:
        x
)"),
            "source.conformance");
  });
  for (StringRef signature : {"roles(P, V)(x: bool @V) -> bool @V",
                              "roles(P, V, W)(x: bool @P) -> bool @P",
                              "roles(P, V)(x: index @P) -> index @P"})
    cases.run("generic Protocol port contract: " + signature, [&] {
      refuses(check("interface I:\n    protocol keep<N: nat> roles(A, B)(x: "
                    "bool @A) -> bool @A\n"
                    "module M: I:\n    protocol keep<K: nat> " +
                    signature + ":\n        return x\n"),
              "source.conformance");
    });
  for (StringRef signature :
       {"(coins: Random<G> @V) -> G @V", "(coins: Random<Fr> @P) -> Fr @P",
        "() -> bool @P"})
    cases.run("generic Protocol service contract: " + signature, [&] {
      std::string body =
          signature.starts_with("()")
              ? "        return true\n"
              : "        value <- coins.draw()\n        return value\n";
      refuses(check("domain Fr = field(\"koala-bear\")\n"
                    "interface I:\n    protocol draw<F: Field> roles(A, "
                    "B)(coins: Random<F> @A) -> F @A\n"
                    "module M: I:\n    protocol draw<G: Field> roles(P, V)" +
                    signature + ":\n" + body),
              "source.conformance");
    });
  cases.run("generic Protocol implementation respects effect ceiling", [] {
    refuses(check(R"(interface I:
    protocol keep<N: nat> roles(A)(x: bool @A) -> bool @A effects()
module M: I:
    protocol keep<K: nat> roles(P)(x: bool @P) -> bool @P:
        guard x
        return x
)"),
            "source.effect");
  });
  cases.run("generic members cannot hide additional transport authority", [] {
    refuses(check(R"(interface I:
    protocol keep<T: Type + Copy + Drop> roles(P, V)(x: T @P) -> T @P effects()
module M: I:
    protocol keep<U: Type + Copy + Drop> roles(A, B)(x: U @A) -> U @A:
        discarded <- send x to B
        return x
#[sealed]
struct Secret:
    value: bool
protocol Apply<C: I> roles(P, V)(x: Secret @P) -> Secret @P:
    result <- C::keep<Secret>(x) @(P, V)
    return result
)"),
            "source.conformance");
  });
  cases.run(
      "concrete member transport discharges native boundary requirements", [] {
        auto project = take(check(R"(interface I:
    protocol keep<N: nat> roles(P, V)(x: bool @P) -> bool @P effects()
module M: I:
    protocol keep<K: nat> roles(A, B)(x: bool @A) -> bool @A:
        discarded <- send x to B
        return x
pub protocol Demo<C: I> roles(P, V)(x: bool @P) -> bool @P:
    result <- C::keep<2>(x) @(P, V)
    return result
)"));
        witness(project);
        take(prepareOriginal(
            take(closeNativeRun(project, "m::Demo", {}, {module("m::M")}))));
      });
  const char *sharedAdmission = R"(interface Shared:
    protocol keep<T: Type + Copy + Drop> roles(P, V)(x: T @(P, V)) -> T @(P, V) effects()
module M: Shared:
    protocol keep<U: Type + Copy + Drop> roles(A, B)(x: U @(A, B)) -> U @(A, B):
        return x
)";
  cases.run("generic member preserves required shared boundary",
            [&] { witness(take(check(sharedAdmission))); });
  for (unsigned mutation = 0; mutation < 3; ++mutation)
    cases.run(
        "boundary admission candidate mutation " + std::to_string(mutation),
        [&] {
          auto project = take(check(sharedAdmission));
          witness(project);
          auto &required = named(project, "m::Shared::keep");
          auto &provided = named(project, "m::M::keep");
          require(!required.admissions.empty() && !provided.admissions.empty(),
                  "missing shared signature boundary");
          if (mutation == 0)
            provided.admissions.push_back(
                {parameterType(provided.parameters[0]),
                 Boundary::Construction,
                 provided.span,
                 {}});
          else if (mutation == 1)
            provided.admissions.clear();
          else {
            required.admissions.push_back(
                {parameterType(required.parameters[0]),
                 Boundary::Message,
                 required.span,
                 {}});
            provided.admissions.push_back(
                {parameterType(provided.parameters[0]),
                 Boundary::Message,
                 provided.span,
                 {}});
          }
          auto error = checkScopedElaboration(project);
          require(bool(error) && namesIdentifier(toString(std::move(error)),
                                                 "source.scoped-witness"),
                  "forged boundary requirement was admitted");
        });
  cases.run("generic service Protocol dispatch retains installed root", [] {
    auto project = take(check(R"(domain Fr = field("bls12-381.fr")
interface Draw:
    protocol draw<F: Field> roles(A)(coins: Random<F> @A) -> F @A effects()
module DrawImpl<N: nat>: Draw:
    protocol draw<G: Field> roles(B)(random: Random<G> @B) -> G @B:
        value <- random.draw()
        return value
pub protocol Demo<C: Draw> roles(P)(coins: Random<Fr> @P) -> Fr @P:
    value <- C::draw<Fr>(coins) @P
    return value
)"));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(
        project, "m::Demo", {}, {module("m::DrawImpl", {natural(3)})}))));
  });
  cases.run("generic callback signature and dispatch", [] {
    auto project = take(check(R"(module m;
interface I {math fn run<T:Type+Copy+Drop>(x:T,body:math fn(T)->T)->T;}
module M<N:nat>:I {math fn run<U:Type+Copy+Drop>(x:U,next:math fn(U)->U)->U{return next(x);}}
math fn apply<C:I,T:Type+Copy+Drop>(x:T)->T{return C::run<T>(x,fn(y)=>y);}
protocol Demo roles(P)(x:bool@P)->(out:bool@P){return apply<M<3>,bool>(x);}
)",
                              false));
    witness(project);
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  for (StringRef callback : {"fn(U)->U effects()", "math fn(bool)->bool"})
    cases.run("generic callback mode and type remain exact: " + callback, [&] {
      refuses(check("module m;interface I{math fn "
                    "run<T:Type+Copy+Drop>(x:T,body:math fn(T)->T)->T;}"
                    "module M:I{math fn run<U:Type+Copy+Drop>(x:U,step:" +
                        callback + ")->U{return x;}}",
                    false),
              "source.conformance");
    });
  cases.run("generic callback effect dependency cannot switch slots", [] {
    refuses(check(R"(module m;
interface I {fn run<T:Type+Copy+Drop>(x:T,a:fn(T)->T effects(stop),b:fn(T)->T effects(stop))->T effects(a);}
module M:I {fn run<U:Type+Copy+Drop>(x:U,first:fn(U)->U effects(stop),second:fn(U)->U effects(stop))->U{return second(x);}}
)",
                  false),
            "source.effect");
  });
  cases.run("generic callback input ceiling cannot be strengthened", [] {
    refuses(check(R"(module m;
interface I {fn run<T:Type+Copy+Drop>(x:T,body:fn(T)->T effects())->T effects();}
module M:I {fn run<U:Type+Copy+Drop>(x:U,step:fn(U)->U effects(stop))->U{return x;}}
)",
                  false),
            "source.conformance");
  });
  for (unsigned mutation = 0; mutation != 3; ++mutation)
    cases.run(
        "inferred member obligation cannot authenticate itself " +
            Twine(mutation),
        [&] {
          auto project = take(check(R"(module m;
type Need<F:Field> where zkc::algebra::TwoAdicField(F)=F;
interface I {fn keep<T:Type,N:nat,F:Field>(x:T)->T effects();}
module M:I {fn keep<U:Type,K:nat,G:Field>(x:U)->U{return x;}}
)",
                                    false));
          witness(project);
          auto &provided = named(project, "m::M::keep");
          if (mutation == 0) {
            auto forged = parameterType(provided.parameters[0]);
            forged.assumptions = {true, true};
            provided.permissionBounds.push_back(
                {forged, {true, true}, provided.span, true});
          } else if (mutation == 1)
            provided.bounds.push_back(
                {Natural::constant(2),
                 parameterType(provided.parameters[1]).dimension, provided.span,
                 true});
          else
            provided.capabilityBounds.push_back(
                {named(project, "m::Need").capabilityBounds.front().predicate,
                 {parameterType(provided.parameters[2])},
                 provided.span,
                 true});
          auto error = checkScopedElaboration(project);
          require(bool(error),
                  "inferred member obligation became its own premise");
          require(namesIdentifier(toString(std::move(error)),
                                  "source.scoped-witness"),
                  "inferred member mutation had the wrong diagnostic");
        });
  for (unsigned mutation = 0; mutation != 10; ++mutation)
    cases.run(
        "source-authenticated generic signature mutation " + Twine(mutation),
        [&] {
          auto project = take(check(mathSource));
          witness(project);
          auto &required = named(project, "m::Ops::echo");
          auto &provided = named(project, "m::Impl::echo");
          switch (mutation) {
          case 0:
            provided.parameters.pop_back();
            break;
          case 1:
            provided.parameters.back().sort = Parameter::Sort::Natural;
            break;
          case 2:
            provided.parameters[2].permissions = {};
            break;
          case 3:
            required.parameters[1].permissions =
                provided.parameters[2].permissions = {};
            break;
          case 4:
            provided.parameters.back().arguments[0] = Type(Type::Kind::Boolean);
            break;
          case 5:
            provided.outputs.front().type = required.outputs.front().type =
                Type(Type::Kind::Boolean);
            break;
          case 6:
            named(project, "m::Impl").conformance.back().provided =
                named(project, "m::apply").id;
            break;
          case 7:
            provided.parameters[3].atom = provided.parameters[0].atom;
            break;
          case 8:
            provided.capabilityBounds =
                named(project, "m::Ops").capabilityBounds;
            provided.kind = Declaration::Kind::Local;
            break;
          case 9:
            provided.roles = required.roles = {"P"};
            break;
          }
          auto error = checkScopedElaboration(project);
          require(bool(error), "forged generic contract was admitted");
          require(namesIdentifier(toString(std::move(error)),
                                  "source.scoped-witness"),
                  "generic mutation had the wrong diagnostic");
        });
  for (unsigned mutation = 0; mutation != 5; ++mutation)
    cases.run("authored Protocol contract mutation " + Twine(mutation), [&] {
      auto project = take(check(protocolSource));
      witness(project);
      auto &required = named(project, "m::Wire::pass");
      auto &provided = named(project, "m::WireImpl::pass");
      switch (mutation) {
      case 0:
        required.outputs.front().roles = provided.outputs.front().roles = {};
        break;
      case 1:
        provided.inputs.front().placement.reset();
        break;
      case 2:
        required.completes = provided.completes = true;
        break;
      case 3:
        required.roles = provided.roles = {"forged"};
        break;
      case 4:
        provided.inputOrder.pop_back();
        break;
      }
      auto error = checkScopedElaboration(project);
      require(bool(error), "forged Protocol contract was admitted");
      require(
          namesIdentifier(toString(std::move(error)), "source.scoped-witness"),
          "Protocol mutation had the wrong diagnostic");
    });
  for (unsigned mutation = 0; mutation != 3; ++mutation)
    cases.run(
        "authored generic Protocol invocation mutation " + Twine(mutation),
        [&] {
          auto project = take(check(protocolSource));
          witness(project);
          auto &body = const_cast<Body &>(*named(project, "m::Demo").body);
          bool changed = false;
          for (auto &op : body.operations)
            if (auto *call = std::get_if<ProtocolApplication>(&op.action)) {
              require(bool(op.binding), "missing invocation binding");
              if (mutation == 0)
                call->arguments.back() = op.binding->arguments.back() =
                    natural(3);
              else if (mutation == 1)
                op.binding->target.module =
                    module("m::WireImpl",
                           {natural(7), named(project, "m::Fr").domain});
              else
                call->callee = named(project, "m::WireImpl::pass").id;
              changed = true;
              break;
            }
          require(changed, "no Protocol invocation to mutate");
          auto error = checkScopedElaboration(project);
          require(bool(error), "forged Protocol invocation was admitted");
          auto message = toString(std::move(error));
          require(namesIdentifier(message, "source.scoped-witness") ||
                      namesIdentifier(message, "source.binding-witness"),
                  "invocation mutation had the wrong diagnostic: " + message);
        });
  cases.run(
      "generic contract replay preserves its enclosing work allowance", [] {
        auto project = take(check(mathSource));
        std::vector<SourceWorkBudget> observations;
        if (auto error = checkScopedElaboration(project, {}, &observations))
          throw std::runtime_error(toString(std::move(error)));
        require(observations.size() == 1 &&
                    observations.front().ledger.total > 0,
                "missing independently charged contract replay");
        Limits limits;
        limits.work =
            std::max(observations.front().ledger.total, project.checkedWork());
        if (auto error = checkScopedElaboration(project, limits))
          throw std::runtime_error(toString(std::move(error)));
        --limits.work;
        auto error = checkScopedElaboration(project, limits);
        require(bool(error) &&
                    namesIdentifier(toString(std::move(error)), "source.limit"),
                "contract replay exceeded its observed work allowance");
      });
  cases.run("source and witness refuse exhausted enclosing allowance", [] {
    auto project = take(check(mathSource));
    Limits limits;
    limits.work = 1;
    refuses(check(mathSource, true, limits), "source.limit");
    auto error = checkScopedElaboration(project, limits);
    require(bool(error) &&
                namesIdentifier(toString(std::move(error)), "source.limit"),
            "witness exceeded its enclosing work allowance");
  });
  return cases.result();
}
