#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Language/Project.h"
#include "zkc/Translation/Language.h"
#include <set>
#include <string>

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::language;
using namespace zkc::test;
namespace {
constexpr StringLiteral prelude = R"(module m;
domain Fr = field("koala-bear");
domain Ext = field("koala-bear.ext8-binomial3");
type Vector<F: Field> = builtin("vector", F);
math fn square<F: Field>(x: F) -> F { return x * x; }
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
math fn residual<F: Field>(a: F, b: F, unused: F, s: F) -> F {
  return (s + 1) * (square(a) - b) + s;
}
)";
constexpr StringLiteral program = R"(
fn fold<F: Field>(low: Vector<F>, high: Vector<F>, r: F) -> Vector<F> {
  return map affine(each low, each high, r);
}
math fn lerp<F: Field>(a: F, b: F, r: F) -> F { return a * r + b; }
fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  let shifted = map lerp(each a, each b, s);
  return map residual<Fr>(each shifted, each b, each c, s);
}
fn repeat(a: Vector<Fr>, s: Fr, n: index) -> Vector<Fr> {
  let mut acc = a;
  for _ in 0..n {
    acc = map affine<_>(each acc, each a, s);
  }
  return acc;
}
protocol Demo roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, c: Vector<Fr> @P,
                       s: Fr @P, n: index @P)
    -> (folded: Vector<Fr> @P, combined: Vector<Fr> @P,
        repeated: Vector<Fr> @P) {
  let folded = fold(a, b, s);
  let combined = combine(a, b, c, s);
  let repeated = repeat(a, s, n);
  return (folded = folded, combined = combined, repeated = repeated);
}
entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }
)";
Expected<CheckedProject> check(StringRef body) {
  auto captured = capture({{"m", (prelude + body).str(), "map.zkc"}});
  if (!captured)
    return captured.takeError();
  return analyze(*captured).checkedProject();
}
Expected<CheckedOriginal> original(StringRef body) {
  auto checked = check(body);
  if (!checked)
    return checked.takeError();
  auto closed = zkc::test::closeProtocolDeployment(*checked, "m::Run");
  if (!closed)
    return closed.takeError();
  return prepareOriginal(*closed);
}
OwningOpRef<ModuleOp> read(const CheckedOriginal &original,
                           MLIRContext &context) {
  auto module = parseSourceString<ModuleOp>(original.bytes(), &context);
  require(bool(module), "emitted map source did not parse");
  return module;
}
SmallVector<exec::CollectOp> collections(ModuleOp module) {
  SmallVector<exec::CollectOp> result;
  module.walk([&](exec::CollectOp op) { result.push_back(op); });
  return result;
}
exec::ComputeOp callback(exec::CollectOp collect) {
  auto function = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
      collect, collect.getBodyAttr());
  require(bool(function), "map callback missing");
  SmallVector<exec::ComputeOp> calls;
  function.walk([&](exec::ComputeOp op) { calls.push_back(op); });
  require(calls.size() == 1,
          "map callback must invoke its actual math helper once");
  return calls.front();
}
} // namespace

int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  cases.run("generic inference, helper calls and local wrappers", [&] {
    auto checked = take(original(program));
    auto module = read(checked, context);
    auto maps = collections(*module);
    require(maps.size() == 4,
            "map occurrences were not retained in source order");
    std::set<std::string> domains, bodies;
    std::multiset<unsigned> widths;
    for (auto map : maps) {
      auto domain = SymbolTable::lookupNearestSymbolFrom<data::DomainOp>(
          map, map.getDomainAttr());
      require(bool(domain), "missing mapped domain");
      auto call = callback(map);
      auto function = call->getParentOfType<func::FuncOp>();
      auto width = domain.getFunctionType().getNumInputs();
      require(call.getInputs().size() == width + 1,
              "mapped callback lost its scalar capture");
      for (unsigned i = 0; i < width; ++i)
        require(call.getInputs()[i] == function.getArgument(1 + i),
                "callback row order differs from each markers");
      require(call.getInputs().back() == function.getArgument(1 + 2 * width),
              "mapped capture was confused with a domain container");
      if (domains.insert(map.getDomain().str()).second)
        widths.insert(width);
      bodies.insert(map.getBody().str());
    }
    require(domains.size() == 3 && bodies.size() == 3 &&
                widths == std::multiset<unsigned>{2, 2, 3},
            "helper instances and each markers did not share exact adapters");
    require(!checked.bytes().contains("vector_add") &&
                !checked.bytes().contains("vector_mul"),
            "original contains realized vector arithmetic");
    take(compileEntry(checked));
    take(compileEntry(checked, {false, false}));
  });
  cases.run("one helper as a scalar and under two masks", [&] {
    auto checked = take(original(
        "fn rows(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
        "  return map affine(each a, each b, s);\n}\n"
        "fn toward(a: Vector<Fr>, y: Fr, s: Fr) -> Vector<Fr> {\n"
        "  return map affine(each a, y, s);\n}\n"
        "fn single(x: Fr, y: Fr, s: Fr) -> Fr { return affine(x, y, s); }\n"
        "protocol Demo roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, y: Fr @P,"
        " s: Fr @P)\n"
        "    -> (r: Vector<Fr> @P, t: Vector<Fr> @P, q: Fr @P) {\n"
        "  return (r = rows(a, b, s), t = toward(a, y, s),"
        " q = single(y, y, s));\n}\n"
        "entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }\n"));
    auto module = read(checked, context);
    auto maps = collections(*module);
    std::set<std::string> helpers, domains;
    std::set<unsigned> widths;
    unsigned calls = 0;
    module->walk([&](exec::ComputeOp op) {
      ++calls;
      helpers.insert(op.getCalleeAttr().getRootReference().str());
    });
    for (auto map : maps) {
      domains.insert(map.getDomain().str());
      auto domain = SymbolTable::lookupNearestSymbolFrom<data::DomainOp>(
          map, map.getDomainAttr());
      widths.insert(domain.getFunctionType().getNumInputs());
    }
    require(maps.size() == 2 && calls == 3 && helpers.size() == 1 &&
                domains.size() == 2 && widths == std::set<unsigned>{1, 2},
            "scalar and mapped occurrences lost their shared helper or "
            "distinct domains");
    take(compileEntry(checked));
  });
  cases.run("compilation is deterministic", [] {
    auto first = take(original(program));
    auto second = take(original(program));
    require(first.bytes() == second.bytes(), "original bytes differ");
    require(take(compileEntry(first)).bytes() ==
                take(compileEntry(second)).bytes(),
            "artifact bytes differ");
  });
  for (StringRef change :
       {"row-order", "callback-port", "helper-target", "invocation-kind"})
    cases.run("emitted map source rejects " + change, [&] {
      auto checked = take(original(program));
      auto closed = take(
          zkc::test::closeProtocolDeployment(take(check(program)), "m::Run"));
      auto module = read(checked, context);
      auto maps = collections(*module);
      require(maps.size() == 4, "missing source maps");
      bool formed = change != "invocation-kind";
      if (change == "row-order") {
        auto domain = SymbolTable::lookupNearestSymbolFrom<data::DomainOp>(
            maps[0], maps[0].getDomainAttr());
        auto elements =
            domain.getBody().front().getOps<data::DomainElementsOp>();
        require(llvm::range_size(elements) == 2, "expected two ordered rows");
        auto first = *elements.begin(), second = *std::next(elements.begin());
        auto operand = first->getOperand(0);
        first->setOperand(0, second->getOperand(0));
        second->setOperand(0, operand);
      } else if (change == "callback-port") {
        auto call = callback(maps[0]);
        auto first = call.getInputs()[0], second = call.getInputs()[1];
        call->setOperand(1, second);
        call->setOperand(2, first);
      } else if (change == "helper-target") {
        SmallVector<exec::ComputeOp> helpers;
        std::set<std::string> names;
        for (auto map : maps) {
          auto call = callback(map);
          if (call.getInputs().size() == 3 &&
              names.insert(call.getCalleeAttr().getRootReference().str())
                  .second)
            helpers.push_back(call);
        }
        require(helpers.size() == 2, "expected distinct same-shaped helpers");
        auto first = helpers[0].getCalleeAttr();
        helpers[0].setCalleeAttr(helpers[1].getCalleeAttr());
        helpers[1].setCalleeAttr(first);
      } else {
        // A pure mathematical helper is not an ordinary scoped ABI callee.
        auto call = callback(maps[0]);
        OpBuilder builder(call);
        auto replacement = func::CallOp::create(
            builder, call.getLoc(), call.getCalleeAttr().getRootReference(),
            call->getResultTypes(), call->getOperands());
        replacement->setAttr("runtime.site", call.getSiteAttr());
        call.getOutcome().replaceAllUsesWith(replacement.getResult(0));
        call.erase();
      }
      ScopedDiagnosticHandler quiet(
          &context, [](mlir::Diagnostic &) { return success(); });
      require(succeeded(verify(*module)) == formed,
              "mutation reached the wrong formation boundary");
      refuses(compareOriginal(closed, *module),
              formed ? "source.correspondence" : "target.admission");
    });

  auto refusal = [&](StringRef label, StringRef body, StringRef code) {
    cases.run(label, [&] { refuses(check(body), code); });
  };
  refusal("missing each on a vector argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(each a, b, s);\n}\n",
          "source.map");
  refusal("each on a scalar argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, each s);\n}\n",
          "source.map");
  refusal("no each argument",
          "fn f(a: Fr, b: Fr, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(a, b, s);\n}\n",
          "source.map");
  refusal("argument count",
          "fn f(a: Vector<Fr>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine(each a, s);\n}\n",
          "source.call");
  refusal("ordered helper",
          "fn g(x: Fr) -> Fr { return x; }\n"
          "fn f(a: Vector<Fr>) -> Vector<Fr> { return map g(each a); }\n",
          "source.map");
  refusal("interface member requires a defined helper",
          "interface Step<F: Field> { math fn apply(x: F) -> F; }\n"
          "module One<F: Field>: Step<F> {\n"
          "  math fn apply(x: F) -> F { return x + 1; }\n}\n"
          "fn f<C: Step<Fr>>(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  return map C::apply(each a);\n}\n",
          "source.map");
  refusal("mixed fields",
          "math fn mix(x: Fr, y: Ext) -> Fr { return x; }\n"
          "fn f(a: Vector<Fr>, e: Ext) -> Vector<Fr> {\n"
          "  return map mix(each a, e);\n}\n",
          "source.map");
  refusal("non-field result",
          "math fn test(x: Fr) -> bool { return x == x; }\n"
          "fn f(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  let tested = map test(each a);\n  return a;\n}\n",
          "source.map");
  refusal("map in a protocol body",
          "protocol P roles(A)(a: Vector<Fr> @A) -> (r: Vector<Fr> @A) {\n"
          "  let r = map square(each a);\n  return (r = r);\n}\n",
          "source.mode");
  refusal("map in a math fn",
          "math fn h(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  return map square(each a);\n}\n",
          "source.mode");
  refusal("index scalar argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, n: index) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, n);\n}\n",
          "source.map");
  refusal("boolean scalar argument",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, go: bool) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, go);\n}\n",
          "source.map");
  // A scalar of another field is an ordinary type conflict of the inferred F.
  refusal("scalar of another field",
          "fn f(a: Vector<Fr>, b: Vector<Fr>, e: Ext) -> Vector<Fr> {\n"
          "  return map affine(each a, each b, e);\n}\n",
          "source.type");
  refusal("vector of another field",
          "fn f(a: Vector<Fr>, b: Vector<Ext>, s: Fr) -> Vector<Fr> {\n"
          "  return map affine<Fr>(each a, each b, s);\n}\n",
          "source.type");
  refusal("unbound map argument",
          "fn f(a: Vector<Fr>) -> Vector<Fr> {\n"
          "  return map affine(each a, each missing, a);\n}\n",
          "source.name");
  refusal("map is reserved", "fn f(map: Fr) -> Fr { return map; }\n",
          "source.name");
  refusal("each is reserved", "fn each(x: Fr) -> Fr { return x; }\n",
          "source.name");
  refusal("each outside map",
          "fn f(a: Vector<Fr>) -> Vector<Fr> { return each a; }\n",
          "source.name");
  // Total mathematics is admitted independently of optional Ring recognition.
  // Dead scalar observations remain part of the authored helper body.
  cases.run("total scalar work outside Ring remains admitted", [] {
    constexpr StringLiteral body =
        "math fn bad<F: Field>(x: F, y: F) -> F {\n"
        "  let unused = x == y;\n  return x;\n}\n"
        "fn f(a: Vector<Fr>, b: Vector<Fr>) -> Vector<Fr> {\n"
        "  return map bad(each a, each b);\n}\n"
        "protocol Demo roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P) -> "
        "(r: Vector<Fr> @P) {\n"
        "  let r = f(a, b);\n  return (r = r);\n}\n"
        "entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }\n";
    auto checked = take(original(body));
    require(checked.bytes().contains("algebra.field_equal") &&
                checked.bytes().contains("exec.compute") &&
                checked.bytes().contains("exec.collect"),
            "source admission dropped the unused scalar computation");
    take(compileEntry(checked));
    take(compileEntry(checked, {false, false}));
  });
  // Ring limits bound optional recognition; they do not reject a total source
  // helper. Each helper doubles the additions of the previous one.
  cases.run("deep total formula retains ordered execution", [] {
    std::string body = "math fn h0<F: Field>(x: F) -> F { return x + 1; }\n";
    for (unsigned i = 1; i <= 10; ++i)
      body += "math fn h" + std::to_string(i) + "<F: Field>(x: F) -> F { " +
              "return h" + std::to_string(i - 1) + "(h" +
              std::to_string(i - 1) + "(x)); }\n";
    body +=
        "fn f(a: Vector<Fr>, n: index) -> Vector<Fr> {\n"
        "  let mut acc = a;\n"
        "  for _ in 0..n {\n"
        "    acc = map h10(each acc);\n"
        "  }\n"
        "  return acc;\n}\n"
        "protocol Demo roles(P)(a: Vector<Fr> @P, n: index @P) -> "
        "(r: Vector<Fr> @P) {\n"
        "  let r = f(a, n);\n  return (r = r);\n}\n"
        "entry fn Run(inputs: Demo::Inputs) { return Demo::run(inputs); }\n";
    auto checked = take(original(body));
    require(checked.bytes().contains("exec.collect"),
            "deep source map was lost");
    take(compileEntry(checked));
    EntryOptions ordered;
    ordered.mathematicalSelection.finiteBulk = false;
    take(compileEntry(checked, ordered));
  });
  return cases.result();
}
