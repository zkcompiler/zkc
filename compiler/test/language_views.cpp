#include "../lib/Language/Checker.h"
#include "../lib/Language/ScopedWitness.h"
#include "../lib/Language/State.h"
#include "../lib/Language/WrittenSource.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Translation/Language.h"
#include <algorithm>
using namespace llvm;
using namespace zkc::language;
using namespace zkc::test;
namespace {
const std::string prelude = R"(module m
domain F = field("koala-bear")
type Vector<E: Field> = builtin("vector", E)
type Finite<I: Type + Copy + Drop> = builtin("finite", I)
view def elements<E: Field>(xs: Vector<E>) -> Finite<E> = domain("elements")
view def zip<A: Type + Copy + Drop, B: Type + Copy + Drop>(a: Finite<A>, b: Finite<B>) -> Finite<(A, B)> = domain("zip")
view def product<A: Type + Copy + Drop, B: Type + Copy + Drop>(a: Finite<A>, b: Finite<B>) -> Finite<(A, B)> = domain("product")
view def range(lo: index, hi: index) -> Finite<index> = domain("range")
def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: fn(S, item: I) -> S where item_from(item, rows)) -> S = finite("math.fold")
local def ordered<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: local fn(S, item: I) -> S effects(stop) where item_from(item, rows)) -> S effects(stop) = finite("local.fold")
)";
Expected<CheckedProject> checkAuthored(StringRef source, Limits limits = {}) {
  CaptureOptions options;
  options.format = "zkc-layout";
  auto captured = capture({{"m", source.str(), "views.zkc"}}, options);
  if (!captured)
    return captured.takeError();
  return analyze(*captured, limits).checkedProject();
}
Expected<CheckedProject> check(StringRef source, Limits limits = {}) {
  return checkAuthored(prelude + source.str(), limits);
}
const Declaration &named(const CheckedProject &project, StringRef name) {
  for (const auto &decl : project.declarations())
    if (decl.qualifiedName == name)
      return decl;
  throw std::runtime_error("missing declaration: " + name.str());
}
const std::string composition = R"(
view def relay<I: Type + Copy + Drop>(rows: Finite<I>) -> Finite<I>:
    return rows
view def paired<E: Field>(xs: Vector<E>) -> Finite<(E, E)>:
    shared = elements(xs)
    return zip(shared, shared)
def mathematical<E: Field>(xs: Vector<E>, initial: E) -> E:
    return fold(relay(paired(xs)), initial, fn(state, item) => state + item.0 + item.1)
local def local_total<E: Field>(xs: Vector<E>, initial: E) -> E effects(stop):
    result <- ordered(relay(paired(xs)), initial, fn(state, item) => state + item.0 + item.1)
    return result
pub protocol Demo roles(P)(xs: Vector<F> @P, initial: F @P) -> F @P:
    first = mathematical(xs, initial)
    second <- local_total(xs, initial)
    return first + second
)";
const std::string memberDeclarations = R"(
interface Forward<A: Type + Copy + Drop>:
    view def pick<B: Type + Copy + Drop, N: nat>(value: B, other: B, padding: [A; N]) -> B
module First<K: nat, A: Type + Copy + Drop>: Forward<A>:
    view def pick<C: Type + Copy + Drop, M: nat>(value: C, other: C, padding: [A; M]) -> C:
        return value
module Second<K: nat, A: Type + Copy + Drop>: Forward<A>:
    view def pick<C: Type + Copy + Drop, M: nat>(value: C, other: C, padding: [A; M]) -> C:
        return other
)";
const std::string ordinaryMembers = memberDeclarations + R"(
type Finite<I: Type + Copy + Drop> = builtin("finite", I)
view def range(lo: index, hi: index) -> Finite<index> = domain("range")
local def ordered<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: local fn(S, item: I) -> S effects(stop) where item_from(item, rows)) -> S effects(stop) = finite("local.fold")
def apply(value: bool, body: fn(bool) -> bool) -> bool:
    return body(value)
def mathematical<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool:
    return M::pick<bool, 2>(x, y, padding)
local def local_total<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool effects():
    return M::pick<bool, 2>(x, y, padding)
def mathematical_scoped<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool:
    return apply(x, fn(item) => M::pick<bool, 2>(item, y, padding))
local def local_scoped<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool effects(stop):
    result <- ordered(range(index<0>(), index<1>()), x, fn(state, item) => M::pick<bool, 2>(state, y, padding))
    return result
)";
Type natural(unsigned value) {
  Type result(Type::Kind::Natural);
  result.dimension = Natural::constant(value);
  return result;
}
void witness(const CheckedProject &project) {
  if (auto error = checkScopedElaboration(project))
    throw std::runtime_error(toString(std::move(error)));
}
} // namespace
int main() {
  Cases cases;
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run(
      "layout finite View composition and forwarding reach both native "
      "consumers",
      [&] {
        auto project = take(check(composition));
        const auto &relay = named(project, "m::relay");
        require(relay.kind == Declaration::Kind::View && relay.inputs.empty() &&
                    relay.descriptorInputs.size() == 1 &&
                    relay.descriptorResult &&
                    relay.descriptorResult->family == DescriptorFamily::Finite,
                "mode and finite result contract were not retained separately");
        auto original =
            take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
        for (StringRef operation : {"data.domain_elements", "data.domain_zip",
                                    "data.finite_fold", "exec.fold"})
          require(original.bytes().contains(operation),
                  "missing actual native operation: " + operation);
        auto module =
            mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
        require(bool(module), "View original did not parse");
        take(compareOriginal(original.entry(), *module));
        take(compileEntry(original));
        take(compileEntry(original, {false, false}));
      });
  cases.run("ordinary View forwarding keeps its ordinary value category", [] {
    auto project = take(check(R"(
view def identity<T: Type + Copy + Drop>(value: T) -> T:
    return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return identity(value)
)"));
    const auto &identity = named(project, "m::identity");
    require(identity.kind == Declaration::Kind::View &&
                !identity.descriptorResult && identity.outputs.size() == 1 &&
                identity.descriptorInputs.empty(),
            "ordinary View was classified as a finite factory");
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  for (StringRef caller :
       {"mathematical", "local_total", "mathematical_scoped", "local_scoped"})
    for (StringRef implementation : {"First", "Second"})
      cases.run(
          "ordinary View owner/member dispatch from " + caller + " via " +
              implementation,
          [&] {
            auto source = ordinaryMembers +
                          "pub protocol Demo roles(P)(x: bool @P, y: "
                          "bool @P, padding: [index; 2] @P) -> bool @P:\n";
            bool local = caller.starts_with("local");
            auto call = caller.str() + "<" + implementation.str() +
                        "<7, index>>(x, y, padding)";
            source += local ? "    result <- " + call + "\n    return result\n"
                            : "    return " + call + "\n";
            auto project = take(checkAuthored(source));
            witness(project);
            const auto &abstract = named(project, "m::Forward::pick");
            require(abstract.kind == Declaration::Kind::View &&
                        !abstract.body && !abstract.effectAllowance &&
                        !abstract.descriptorResult,
                    "abstract View lost its inherent structural contract");
            require(named(project, "m::" + caller.str()).body->effects ==
                        EffectSummary{Effects{caller == "local_scoped", false}},
                    "ordinary View call changed its enclosing effects");
            auto closed = take(closeNativeRun(project, "m::Demo"));
            auto origin =
                named(project, "m::" + implementation.str() + "::pick").id;
            bool selected = false;
            for (const auto &decl : closed.declarations())
              if (decl.origin && decl.origin->index == origin.index) {
                selected = true;
                require(decl.kind == Declaration::Kind::View &&
                            decl.staticArguments ==
                                std::vector<Type>{
                                    natural(7), Type(Type::Kind::Index),
                                    Type(Type::Kind::Boolean), natural(2)},
                        "View dispatch lost owner/member telescopes");
              }
            require(selected, "abstract View member was not dispatched");
            auto original = take(prepareOriginal(closed));
            auto module = mlir::parseSourceString<mlir::ModuleOp>(
                original.bytes(), &context);
            require(bool(module), "View member native ports did not verify");
            take(compareOriginal(original.entry(), *module));
            take(compileEntry(original));
            take(compileEntry(original, {false, false}));
          });
  for (StringRef operation : {"and", "or"})
    for (bool left : {false, true})
      for (StringRef call :
           {"identity(x)", "box.read()", "M::pick<bool, 2>(x, y, padding)",
            "apply(x, fn(item) => identity(item))"})
        cases.run(
            "Protocol Boolean ordinary View operand: " + call + " " +
                operation + ", left=" + Twine(left),
            [&] {
              auto source = memberDeclarations + R"(
def apply(value: bool, body: fn(bool) -> bool) -> bool:
    return body(value)
view def identity(value: bool) -> bool:
    return value
struct Box:
    pub value: bool
pub view def read(self: Box) -> bool:
    return self.value
pub protocol Demo<M: Forward<index>> roles(P)(x: bool @P, y: bool @P, box: Box @P, padding: [index; 2] @P) -> bool @P:
    return )";
              source += left ? call.str() + " " + operation.str() + " y\n"
                             : "y " + operation.str() + " " + call.str() + "\n";
              auto project = take(checkAuthored(source));
              witness(project);
              Type moduleType(Type::Kind::Module, "m::First");
              moduleType.arguments = {natural(7), Type(Type::Kind::Index)};
              auto original = take(prepareOriginal(
                  take(closeNativeRun(project, "m::Demo", {}, {moduleType}))));
              auto module = mlir::parseSourceString<mlir::ModuleOp>(
                  original.bytes(), &context);
              require(bool(module), "View Boolean original did not verify");
              take(compareOriginal(original.entry(), *module));
              take(compileEntry(original));
              take(compileEntry(original, {false, false}));
            });
  for (StringRef operation : {"and", "or"})
    for (bool left : {false, true})
      for (StringRef call :
           {"ordered_identity(x)", "ignore(x, fn(item) => item)"})
        cases.run("Protocol Boolean still refuses Local work: " + call + " " +
                      operation + ", left=" + Twine(left),
                  [&] {
                    std::string source = R"(
local def ordered_identity(value: bool) -> bool effects():
    return value
def ignore(value: bool, body: local fn(bool) -> bool effects()) -> bool:
    return value
pub protocol Demo roles(P)(x: bool @P, y: bool @P) -> bool @P:
    return )";
                    source +=
                        left ? call.str() + " " + operation.str() + " y\n"
                             : "y " + operation.str() + " " + call.str() + "\n";
                    refuses(checkAuthored(source), "source.mode");
                  });
  for (StringRef operation : {"and", "or"})
    for (bool left : {false, true})
      cases.run(
          "Protocol Boolean admits checked static descriptor arguments: " +
              operation + ", left=" + Twine(left),
          [&] {
            std::string call = "ignore(range(lo, hi), x)";
            std::string source = R"(
view def ignore(rows: Finite<index>, value: bool) -> bool:
    return value
pub protocol Demo roles(P)(lo: index @P, hi: index @P, x: bool @P, y: bool @P) -> bool @P:
    return )";
            source += left ? call + " " + operation.str() + " y\n"
                           : "y " + operation.str() + " " + call + "\n";
            auto project = take(check(source));
            auto original =
                take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
            take(compileEntry(original, {false, false}));
            take(compileEntry(original, {true, false}));
          });
  for (const auto &example : std::vector<std::pair<std::string, std::string>>{
           {"view def bad(value: bool, body: fn(bool) -> bool) -> bool:\n    "
            "return value\n",
            "source.scoped"},
           {"view def bad(value: bool) -> bool effects():\n    return value\n",
            "source.effect"}})
    cases.run("ordinary View still refuses callback/effect signatures: " +
                  example.first,
              [&] { refuses(checkAuthored(example.first), example.second); });
  for (StringRef kind : {"def", "local def"})
    cases.run("ordinary View conformance retains exact mode: " + kind, [&] {
      refuses(
          checkAuthored("interface I:\n    view def pick(value: bool) -> "
                        "bool\nmodule Bad: I:\n    " +
                        kind.str() +
                        " pick(value: bool) -> bool:\n        return value\n"),
          "source.conformance");
    });
  for (unsigned mutation = 0; mutation != 4; ++mutation)
    cases.run(
        "ordinary View dispatch authenticates conformance and source " +
            Twine(mutation),
        [&] {
          auto project = take(checkAuthored(ordinaryMembers + R"(
pub protocol Demo roles(P)(x: bool @P, y: bool @P, padding: [index; 2] @P) -> bool @P:
    return mathematical<First<7, index>>(x, y, padding)
)"));
          witness(project);
          take(closeNativeRun(project, "m::Demo"));
          auto &implementation =
              const_cast<Declaration &>(named(project, "m::First"));
          if (mutation == 0)
            implementation.conformance.front().provided =
                named(project, "m::Second::pick").id;
          if (mutation == 1) {
            auto &member =
                const_cast<Declaration &>(named(project, "m::First::pick"));
            member.parameters.back().sort = Parameter::Sort::Type;
          }
          if (mutation == 2) {
            auto &body =
                const_cast<Body &>(*named(project, "m::mathematical").body);
            auto &call = std::get<HelperCall>(body.operations.front().action);
            call.callee = named(project, "m::Second::pick").id;
            body.operations.front().binding->target.declaration = call.callee;
          }
          if (mutation == 3) {
            auto &body =
                const_cast<Body &>(*named(project, "m::First::pick").body);
            body.results.front() = ValueId{1};
            for (auto &[expression, value] : body.expressionValues)
              value = ValueId{1};
          }
          refuses(closeNativeRun(project, "m::Demo"),
                  mutation == 3   ? "source.view-witness"
                  : mutation == 2 ? "source.binding-witness"
                                  : "source.scoped-witness");
        });
  cases.run("an ordinary type named Finite has no family authority", [] {
    CaptureOptions options;
    options.format = "zkc-layout";
    auto project = take(analyze(take(capture({{"m", R"(type Finite = bool
view def identity(value: Finite) -> Finite:
    return value
)",
                                               "ordinary.zkc"}},
                                             options)))
                            .checkedProject());
    require(!named(project, "m::identity").descriptorResult,
            "display name installed a descriptor family");
  });
  cases.run(
      "descriptor aliases retain category through imported declarations", [] {
        CaptureOptions options;
        options.format = "zkc-layout";
        auto project =
            take(analyze(take(capture({{"family",
                                        "pub type Rows<T: Type + Copy + Drop> "
                                        "= builtin(\"finite\", T)\n",
                                        "family.zkc"},
                                       {"m", R"(use family::{Rows}
type Traversal<T: Type + Copy + Drop> = Rows<T>
view def identity<T: Type + Copy + Drop>(rows: Traversal<T>) -> Traversal<T>:
    return rows
)",
                                        "alias.zkc"}},
                                      options)))
                     .checkedProject());
        require(named(project, "m::identity").descriptorResult.has_value(),
                "alias erased descriptor category");
      });
  cases.run("ordinary View result and usage inference use the authored policy",
            [] {
              auto project = take(check(R"(
view def identity<T: Type>(value: T):
    return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return identity(value)
)"));
              require(named(project, "m::identity").outputs.size() == 1,
                      "ordinary View result was not inferred");
              take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
            });
  cases.run("ordinary View methods retain the nominal canonical home", [] {
    auto project = take(check(R"(
struct Box:
    pub value: bool
pub view def read(self: Box) -> bool:
    return self.value
pub protocol Demo roles(P)(box: Box @P) -> bool @P:
    return box.read()
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  cases.run(
      "native constructor drift refuses independent View correspondence", [&] {
        auto project = take(check(composition));
        auto entry = take(closeNativeRun(project, "m::Demo"));
        auto text = take(emitOriginal(entry, context));
        auto position = text.find("\"data.domain_zip\"");
        require(position != std::string::npos, "missing zip constructor");
        text.replace(position, StringRef("\"data.domain_zip\"").size(),
                     "\"data.domain_product\"");
        auto module = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
        require(bool(module),
                "same-typed native constructor mutation did not parse");
        refuses(compareOriginal(entry, *module), "source.correspondence");
      });
  for (const auto &example : std::vector<std::pair<std::string, std::string>>{
           {"def leak(rows: Finite<F>) -> Finite<F>:\n    return rows\n",
            "source.descriptor"},
           {"type Escape = (Finite<F>, bool)\n", "source.type"},
           {"type Escape = [Finite<F>; 0]\n", "source.type"},
           {"struct Escape:\n    value: Finite<F>\n", "source.type"},
           {"type Box<T: Type> = T\ntype Escape = Box<Finite<F>>\n",
            "source.generic"},
           {"interface Escape:\n    type Item: Type\nmodule Bad: Escape:\n    "
            "type Item = Finite<F>\n",
            "source.type"},
           {"pub protocol Demo roles(P)(rows: Finite<F> @P) -> bool @P:\n    "
            "return true\n",
            "source.descriptor"},
           {"def leak(rows: Finite<F> @P) -> bool:\n    return true\n",
            "source.descriptor"},
           {"pub protocol Demo roles(P)(rng: Random<Finite<F>> @P) -> bool "
            "@P:\n    return true\n",
            "source.service"}})
    cases.run("descriptor cannot escape through an ordinary representation: " +
                  example.first,
              [&] { refuses(check(example.first), example.second); });
  for (StringRef source :
       {"view def bad(x: F) -> F:\n    return x + x\n",
        "def ordinary(x: F) -> F:\n    return x\nview def bad(x: F) -> F:\n    "
        "return ordinary(x)\n",
        "view def bad(xs: Vector<F>) -> Vector<F>:\n    return [xs]\n"})
    cases.run("View refuses unclassified computation: " + source,
              [&] { refuses(check(source), "source.view"); });
  cases.run("finite View formation cannot borrow a sealed linear operand", [] {
    refuses(check(R"(
#[sealed]
#[linear]
struct Ticket:
    value: bool
view def hidden(ticket: Ticket, lo: index, hi: index) -> Finite<index>:
    return range(lo, hi)
)"),
            "source.finite-domain");
  });
  for (bool available : {false, true})
    cases.run(
        available ? "forwarded descriptor retains transitive participant scope"
                  : "forwarded descriptor cannot borrow an absent participant",
        [&] {
          auto source = std::string(R"(
view def relay<I: Type + Copy + Drop>(rows: Finite<I>) -> Finite<I>:
    return rows
def ignore(rows: Finite<F>, value: F) -> F:
    return value
pub protocol Demo roles(P, V)(xs: Vector<F> @)") +
                        (available ? "P" : "V") +
                        R"(, n: index @P, initial: F @P) -> F @P:
    first = relay(elements(xs))
    rows = relay(first)
    mut result: F @P = initial
    for i in 0..n roles(P) max 4:
        result := ignore(rows, result)
    return result
)";
          if (available) {
            auto project = take(check(source));
            take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
          } else
            refuses(check(source), "source.roles");
        });
  for (unsigned mutation = 0; mutation != 14; ++mutation)
    cases.run(
        "authored recipe replay refuses typed graph drift " + Twine(mutation),
        [&] {
          auto project = take(check(R"(
view def graph<E: Field>(xs: Vector<E>, ys: Vector<E>) -> Finite<(E, E)>:
    first = elements(xs)
    second = elements(ys)
    return zip(first, second)
pub protocol Demo roles(P)(xs: Vector<F> @P, ys: Vector<F> @P, initial: F @P) -> F @P:
    result <- ordered(graph(xs, ys), initial, fn(state, item) => state + item.0 + item.1)
    return result
)"));
          auto &definition = const_cast<DescriptorDefinition &>(
              *named(project, "m::graph").descriptorDefinition);
          auto &binding = definition.bindings.back();
          if (mutation == 0)
            binding.contract.family = static_cast<DescriptorFamily>(99);
          if (mutation == 1)
            binding.kind = DescriptorBinding::Kind::Product;
          if (mutation == 2)
            std::reverse(binding.children.begin(), binding.children.end());
          if (mutation == 3)
            ++*binding.expression;
          if (mutation == 4)
            binding.factory->declaration = named(project, "m::product").id;
          if (mutation == 5) {
            auto &operand = definition.bindings.front().operands.front();
            require(operand.index == 0, "unexpected first source operand");
            operand = ValueId{1};
          }
          if (mutation == 6)
            std::reverse(binding.argumentOrder.begin(),
                         binding.argumentOrder.end());
          if (mutation == 7)
            binding.arguments.front() = Type(Type::Kind::Index);
          if (mutation == 8)
            binding.contract.parameters.clear();
          if (mutation == 9)
            binding.contract.parameters.push_back(Type{});
          if (mutation == 10)
            binding.children.front().contract.parameters.clear();
          if (mutation == 11)
            binding.children.front().contract.parameters = {Type{}};
          if (mutation == 12) {
            auto changed = binding.contract;
            changed.parameters = {Type{}};
            binding.contract = changed;
            const_cast<Declaration &>(named(project, "m::graph"))
                .descriptorResult = changed;
          }
          if (mutation == 13) {
            auto &child = definition.bindings[binding.children.front().node];
            child.contract.parameters = {Type{}};
            binding.children.front().contract = child.contract;
          }
          // Changing the declaration result as well reaches header replay
          // before recipe replay; both use the immutable authored source.
          refuses(closeNativeRun(project, "m::Demo"),
                  mutation == 12 ? "source.scoped-witness"
                                 : "source.view-witness");
        });
  for (bool inferred : {false, true})
    for (bool mutate : {false, true})
      cases.run("ordinary View authored return, inferred=" + Twine(inferred) +
                    ", mutate=" + Twine(mutate),
                [&] {
                  auto source = std::string("view def pick(x: bool, y: bool)") +
                                (inferred ? "" : " -> bool") + R"(:
    return x
pub protocol Demo roles(P)(x: bool @P, y: bool @P) -> bool @P:
    return pick(x, y)
)";
                  auto project = take(checkAuthored(source));
                  take(closeNativeRun(project, "m::Demo"));
                  if (mutate) {
                    auto &body =
                        const_cast<Body &>(*named(project, "m::pick").body);
                    body.results.front() = ValueId{1};
                    refuses(closeNativeRun(project, "m::Demo"),
                            "source.view-witness");
                  }
                });
  for (bool abstract : {false, true})
    cases.run("last authored View cannot be reclassified, abstract=" +
                  Twine(abstract),
              [&] {
                auto source = abstract ? R"(interface Contract:
    view def pick(x: bool) -> bool
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    return x
)"
                                       : R"(view def pick(x: bool) -> bool:
    return x
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    return pick(x)
)";
                auto project = take(checkAuthored(source));
                take(closeNativeRun(project, "m::Demo"));
                auto &decl = const_cast<Declaration &>(
                    named(project, abstract ? "m::Contract::pick" : "m::pick"));
                decl.kind = Declaration::Kind::Math;
                refuses(closeNativeRun(project, "m::Demo"),
                        "source.view-witness");
              });
  cases.run("ordinary View uses Math native ports in Local and callbacks", [&] {
    auto project = take(check(R"(
view def identity<E: Field>(value: E) -> E:
    return value
local def wrapper<E: Field>(value: E) -> E:
    return identity(value)
local def callbacks<E: Field>(xs: Vector<E>, initial: E) -> E effects(stop):
    result <- ordered(elements(xs), initial, fn(state, item) => identity(state) + identity(item))
    return result
pub protocol Demo roles(P)(xs: Vector<F> @P, initial: F @P) -> F @P:
    seed <- wrapper(initial)
    result <- callbacks(xs, seed)
    return result
)"));
    auto original =
        take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
    require(original.bytes().contains("\"exec.compute\""),
            "missing mathematical invocation");
    auto module =
        mlir::parseSourceString<mlir::ModuleOp>(original.bytes(), &context);
    require(bool(module), "ordinary View native call ports did not verify");
    take(compareOriginal(original.entry(), *module));
    take(compileEntry(original));
  });
  cases.run("descriptor output custody cannot be erased", [] {
    refuses(check(R"(
view def relay(rows: Finite<bool>) -> Finite<bool> @Missing -> ():
    return rows
)"),
            "source.descriptor");
  });
  for (unsigned mutation = 0; mutation != 4; ++mutation)
    cases.run(
        "ordinary View body replay refuses typed drift " + Twine(mutation),
        [&] {
          auto project = take(checkAuthored(R"(
view def constant() -> bool:
    return true
view def projected(pair: (bool, bool)) -> bool:
    return pair.0
view def first(x: bool, y: bool) -> bool:
    return x
view def second(x: bool, y: bool) -> bool:
    return y
view def pick(x: bool, y: bool) -> bool:
    chosen = first(x, y)
    return chosen
pub protocol Demo roles(P)(x: bool @P, y: bool @P) -> bool @P:
    return pick(x, y)
)"));
          take(closeNativeRun(project, "m::Demo"));
          auto &body = const_cast<Body &>(
              *named(project, mutation == 0   ? "m::constant"
                              : mutation == 1 ? "m::projected"
                                              : "m::pick")
                   .body);
          if (mutation == 0)
            std::get<MathValue>(body.operations.front().action).literal =
                "false";
          if (mutation == 1)
            std::get<Projection>(body.operations.front().action).path.front() =
                1;
          if (mutation == 2) {
            body.results.front() = ValueId{1};
            for (auto &[expression, value] : body.expressionValues)
              value = ValueId{1};
          }
          if (mutation == 3) {
            auto &operation = body.operations.front();
            std::get<HelperCall>(operation.action).callee =
                named(project, "m::second").id;
            operation.binding->target.declaration =
                named(project, "m::second").id;
          }
          refuses(closeNativeRun(project, "m::Demo"), "source.view-witness");
        });
  for (bool abstract : {false, true})
    cases.run(
        "authored View cannot be missing, abstract=" + Twine(abstract), [&] {
          auto project = take(checkAuthored(abstract ? R"(
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    return x
interface Contract:
    view def last(x: bool) -> bool
)"
                                                     : R"(
pub protocol Demo roles(P)(x: bool @P) -> bool @P:
    return x
view def last(x: bool) -> bool:
    return x
)"));
          take(closeNativeRun(project, "m::Demo"));
          auto &declarations =
              const_cast<zkc::language::detail::CheckedStorage &>(
                  zkc::language::detail::DeclarationAccess::storage(project))
                  .declarations;
          auto id =
              named(project, abstract ? "m::Contract::last" : "m::last").id;
          declarations.erase(declarations.begin() + id.index);
          refuses(closeNativeRun(project, "m::Demo"), "source.installation");
        });
  for (StringRef result : {"bool", "Finite<bool>", ""})
    if (result != "Finite<bool>")
      cases.run("finite constructor refuses ordinary or omitted result: " +
                    result,
                [&] {
                  auto source = std::string("view def bad(value: bool)") +
                                (result.empty() ? "" : " -> " + result.str()) +
                                " = domain(\"range\")\n";
                  refuses(check(source), "source.descriptor");
                });
  for (StringRef placement : {" @Missing", " @Missing -> ()"})
    cases.run("descriptor result rejects modifiers before normalization: " +
                  placement,
              [&] {
                refuses(
                    check("view def relay(rows: Finite<bool>) -> Finite<bool>" +
                          placement.str() + ":\n    return rows\n"),
                    "source.descriptor");
              });
  cases.run("ordinary View may retain an unused descriptor input", [] {
    auto project = take(check(R"(
view def ignore(rows: Finite<bool>, value: bool) -> bool:
    return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return value
)"));
    take(prepareOriginal(take(closeNativeRun(project, "m::Demo"))));
  });
  for (unsigned modifier = 0; modifier != 11; ++modifier)
    cases.run(
        "descriptor signature reader rejects every result modifier " +
            Twine(modifier),
        [&] {
          namespace detail = zkc::language::detail;
          auto project = take(check(R"(
view def relay(rows: Finite<bool>) -> Finite<bool>:
    return rows
)"));
          const auto &storage = detail::DeclarationAccess::storage(project);
          auto authored = storage.writtenSources->modules;
          detail::Work work{Limits{}};
          if (auto error = detail::expandLayoutSections(authored, work))
            throw std::runtime_error(toString(std::move(error)));
          std::optional<detail::SyntaxDeclaration> source;
          for (const auto &module : authored)
            if (module.name == "m")
              for (const auto &member : module.members)
                if (member.name == "relay")
                  source = member;
          require(source && source->outputs.size() == 1,
                  "missing authored descriptor output");
          auto &port = source->outputs.front();
          switch (modifier) {
          case 0:
            port.roles = {"Missing"};
            break;
          case 1:
            port.purpose = RelationPurpose{};
            break;
          case 2:
            port.binding = detail::SyntaxSelector{};
            break;
          case 3:
            port.scoped = detail::SyntaxScopedSignature{};
            break;
          case 4:
            port.serviceConstructor = "random";
            break;
          case 5:
            port.serviceReference = ResolvedReference{};
            break;
          case 6:
            port.oracleHolder = "Missing";
            break;
          case 7:
            port.oracleMaximum = detail::SyntaxType{};
            break;
          case 8:
            port.type.roles = std::vector<std::string>{};
            break;
          case 9:
            port.type.components = std::vector<std::string>{};
            break;
          case 10:
            port.type.oracleHolder = "Missing";
            break;
          }
          detail::CheckedStorage replay(storage.capture, storage.installation);
          replay.declarations = storage.declarations;
          replay.assets = storage.assets;
          replay.sources = storage.sources;
          replay.declarationIndex = storage.declarationIndex;
          detail::Checker reader(replay, work, SourceAccess{{0}});
          auto id = named(project, "m::relay").id;
          require(reader.prepareSignatureReconstruction(id, *source),
                  "failed to prepare signature reader");
          require(!reader.reconstructSignature(id),
                  "descriptor modifier was normalized away");
          auto message = toString(reader.types.takeError());
          require(namesIdentifier(message, "source.descriptor"),
                  "unexpected refusal: " + message);
        });
  cases.run(
      "ordinary body guard refuses missing syntax before lexical resolution",
      [] {
        namespace detail = zkc::language::detail;
        auto project = take(checkAuthored(R"(
view def identity(value: bool) -> bool:
    return value
)"));
        const auto &storage = detail::DeclarationAccess::storage(project);
        detail::CheckedStorage replay(storage.capture, storage.installation);
        replay.declarations = storage.declarations;
        replay.assets = storage.assets;
        replay.sources = storage.sources;
        replay.declarationIndex = storage.declarationIndex;
        detail::Work work{Limits{}};
        detail::Checker reader(replay, work, SourceAccess{{0}});
        auto id = named(project, "m::identity").id;
        auto source = *storage.bodySources.at(id.index)->syntax;
        source.bodies.clear();
        reader.sources.resize(replay.declarations.size());
        reader.sources[id.index] = &source;
        reader.beginViewReconstruction();
        reader.bodyState[id.index] = 0;
        require(!reader.body(id, 1), "ordinary reader accepted missing body");
        auto message = toString(reader.types.takeError());
        require(namesIdentifier(message, "source.body"),
                "unexpected refusal: " + message);
      });
  for (bool inferred : {false, true})
    cases.run(
        "authored ordinary View body cannot be missing, inferred=" +
            Twine(inferred),
        [&] {
          auto source = std::string("view def identity(value: bool)") +
                        (inferred ? "" : " -> bool") + R"(:
    return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return identity(value)
)";
          auto project = take(checkAuthored(source));
          take(closeNativeRun(project, "m::Demo"));
          auto &decl = const_cast<Declaration &>(named(project, "m::identity"));
          decl.body.reset();
          refuses(closeNativeRun(project, "m::Demo"), "source.view-witness");
        });
  for (bool authoredView : {false, true})
    cases.run(
        "candidate cannot invent a View, existing authored View=" +
            Twine(authoredView),
        [&] {
          auto source = std::string(R"(def identity(value: bool) -> bool:
    return value
pub protocol Demo roles(P)(value: bool @P) -> bool @P:
    return identity(value)
)") + (authoredView ? "view def other(value: bool) -> bool:\n    return value\n"
                    : "");
          auto project = take(checkAuthored(source));
          take(closeNativeRun(project, "m::Demo"));
          auto &decl = const_cast<Declaration &>(named(project, "m::identity"));
          decl.kind = Declaration::Kind::View;
          refuses(closeNativeRun(project, "m::Demo"), "source.view-witness");
        });
  return cases.result();
}
