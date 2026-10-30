#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ResourceSources.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/ResourceOrigins.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::resource_sources;
namespace {
auto analysis(Source &source, uint64_t &work, unsigned depth = 64) {
  auto closure = take(protocol::readSourceExecutionClosure(source.owner));
  return take(exec::ResourceOriginAnalysis::create(
      source.owner, std::move(closure), work, depth));
}
func::FuncOp function(Source &source, StringRef name) {
  return cast<func::FuncOp>(SymbolTable::lookupSymbolIn(source.owner, name));
}
void expect(const exec::ResourceOriginSummary &summary,
            std::map<unsigned, unsigned> roots, bool continues = true) {
  require(summary.roots == roots && summary.continues == continues,
          "wrong native roots or continuation");
}
} // namespace
int main() {
  Cases cases;
  for (StringRef name :
       {"apply", "calls80", "draw80", "if", "if-stop", "for", "for-stop",
        "match", "match-stop", "unknown-slot", "stop-call"})
    cases.run("actual native roots through " + name.str(), [&] {
      Source source;
      simple(source, name, true);
      uint64_t work = 100000;
      auto roots = analysis(source, work);
      expect(take(roots->get(function(source, "step"))), {{0, 0}});
    });
  for (StringRef name : {"fresh", "fresh-branch", "fresh-stop-branch",
                         "unknown-wrong", "continuing-call", "box"})
    cases.run("unknown roots remain unknown through " + name.str(), [&] {
      Source source;
      simple(source, name, true);
      uint64_t work = 100000;
      auto roots = analysis(source, work);
      expect(take(roots->get(function(source, "step"))), {});
    });
  cases.run("stopped alternatives differ from unknown successful roots", [] {
    Source source;
    simple(source, "terminal-then-return", true);
    uint64_t work = 100000;
    auto roots = analysis(source, work);
    expect(take(roots->get(function(source, "step"))), {}, false);
  });
  for (StringRef name : {"formal", "formal-swap", "swap"})
    cases.run("actual formal positions through " + name.str(), [&] {
      Source source;
      pair(source, name, true);
      uint64_t work = 100000;
      auto roots = analysis(source, work);
      auto expected =
          name == "formal"        ? std::map<unsigned, unsigned>{{0, 0}, {1, 1}}
          : name == "formal-swap" ? std::map<unsigned, unsigned>{{0, 1}, {1, 0}}
                                  : std::map<unsigned, unsigned>{};
      expect(take(roots->get(function(source, "swap"))), expected);
    });
  cases.run("cached native summaries retain height and shared allowance", [] {
    Source source;
    for (unsigned i = 0; i < 4; ++i) {
      auto fn =
          source.function("f" + std::to_string(i), source.rng, source.rng);
      exec::ScopedExecutionBuilder control(source.builder, fn);
      Value value = fn.getArgument(1);
      if (i)
        value = source.call(control, "f" + std::to_string(i - 1), value,
                            source.rng, "call")[0];
      control.returned(value);
    }
    uint64_t work = 100000;
    auto roots = analysis(source, work, 4);
    auto result = take(roots->get(function(source, "f3")));
    expect(result, {{0, 0}});
    require(result.depth == 4, "cache lost nested height");
    refuses(roots->get(function(source, "f3"), 2),
            "mathematical-analysis-limit");
    auto limited = analysis(source, work);
    take(limited->get(function(source, "f0")));
    work = 1;
    refuses(limited->get(function(source, "f0")),
            "mathematical-analysis-limit");
  });
  cases.run("every smaller native query allowance refuses", [] {
    Source source;
    simple(source, "if", true);
    auto closure = take(protocol::readSourceExecutionClosure(source.owner));
    auto query =
        [&](uint64_t &remaining) -> Expected<exec::ResourceOriginSummary> {
      auto roots = exec::ResourceOriginAnalysis::create(source.owner, closure,
                                                        remaining);
      if (!roots)
        return roots.takeError();
      return (*roots)->get(function(source, "step"));
    };
    uint64_t work = 100000;
    expect(take(query(work)), {{0, 0}});
    uint64_t cost = 100000 - work;
    require(cost > 0 && cost < 1000, "unexpected native query cost");
    for (uint64_t limit = 0; limit < cost; ++limit) {
      uint64_t remaining = limit;
      refuses(query(remaining), "mathematical-analysis-limit");
    }
    expect(take(query(cost)), {{0, 0}});
    require(cost == 0, "exact native query allowance was not consumed");
  });
  cases.run("cached native exhaustion cannot be cleared by restoring work", [] {
    Source source;
    simple(source, "apply", true);
    uint64_t work = 100000;
    auto roots = analysis(source, work);
    expect(take(roots->get(function(source, "step"))), {{0, 0}});
    work = 0;
    refuses(roots->get(function(source, "step")),
            "mathematical-analysis-limit");
    work = 100000;
    refuses(roots->get(function(source, "step")),
            "mathematical-analysis-limit");
  });
  cases.run("native queries refuse zero depth and absent functions", [] {
    Source source;
    simple(source, "apply", true);
    uint64_t work = 100000;
    auto zeroDepth = analysis(source, work, 0);
    refuses(zeroDepth->get(function(source, "step")),
            "mathematical-analysis-limit");
    auto roots = analysis(source, work);
    refuses(roots->get(func::FuncOp{}), "mathematical-formation");
  });
  cases.run("copyable native results never supply resource roots", [] {
    Source source;
    auto identity = source.function("identity", source.boolean, source.boolean);
    exec::ScopedExecutionBuilder body(source.builder, identity);
    body.returned(identity.getArgument(1));
    uint64_t work = 100000;
    auto roots = analysis(source, work);
    expect(take(roots->get(identity)), {});
  });
  cases.run("function identity cannot cross an admitted owner", [] {
    Source left, right;
    simple(left, "apply", true);
    simple(right, "apply", true);
    uint64_t work = 100000;
    auto roots = analysis(left, work);
    refuses(roots->get(function(right, "step")), "mathematical-formation");
  });
  for (StringRef fixture : {"affine.mlir", "affine-successor.mlir"})
    cases.run("finite state uses actual callback roots " + fixture.str(), [&] {
      Source source;
      auto module = parseSourceFile<ModuleOp>(std::string(ZKC_FINITE_FIXTURES) +
                                                  "/" + fixture.str(),
                                              &source.context);
      require(bool(module), "finite native fixture refused");
      auto *owner = &module->getBody()->front();
      auto closure = take(protocol::readSourceExecutionClosure(owner));
      uint64_t work = 100000;
      auto roots = take(exec::ResourceOriginAnalysis::create(
          owner, std::move(closure), work, 2));
      if (auto failure = roots->verifyFiniteState())
        throw std::runtime_error(toString(std::move(failure)));
      auto caller =
          cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "work"));
      auto summary = take(roots->get(caller));
      expect(summary, {{0, 1}, {1, 2}});
      require(summary.depth == 2, "finite callback counted more than once");
      refuses(roots->get(caller, 2), "mathematical-analysis-limit");
    });
  cases.run("helper and finite callback edges share the exact depth limit", [] {
    Source source;
    auto module = parseSourceFile<ModuleOp>(
        std::string(ZKC_FINITE_FIXTURES) + "/affine.mlir", &source.context);
    require(bool(module), "finite native fixture refused");
    source.owner =
        cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
    auto original = function(source, "work");
    auto signature = protocol::scopedDataSignature(original);
    std::string callee = "work";
    for (unsigned i = 0; i < 62; ++i) {
      auto name = "caller" + std::to_string(i);
      auto wrapper =
          source.function(name, signature.getInputs(), signature.getResults());
      exec::ScopedExecutionBuilder body(source.builder, wrapper);
      body.returned(source.call(body, callee,
                                wrapper.getArguments().drop_front(),
                                signature.getResults(), "call"));
      callee = name;
    }
    uint64_t work = 100000;
    auto roots = analysis(source, work);
    // Warm a nested callback summary before asking about the complete chain.
    require(take(roots->get(original)).depth == 2, "wrong folded height");
    auto summary = take(roots->get(function(source, callee)));
    expect(summary, {{0, 1}, {1, 2}});
    require(summary.depth == 64, "mixed callback/call height changed");
    refuses(roots->get(function(source, callee), 2),
            "mathematical-analysis-limit");
    auto fresh = analysis(source, work, 63);
    refuses(fresh->get(function(source, callee)),
            "mathematical-analysis-limit");
  });
  cases.run("finite state refuses exchanged roots in a formed callback", [] {
    Source source;
    auto module = parseSourceFile<ModuleOp>(
        std::string(ZKC_FINITE_FIXTURES) + "/affine.mlir", &source.context);
    require(bool(module), "finite fixture refused");
    auto *owner = &module->getBody()->front();
    auto callback =
        cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "step"));
    auto returned = cast<exec::ReturnOp>(callback.front().front());
    returned->setOperands({callback.getArgument(2), callback.getArgument(1)});
    require(succeeded(mlir::verify(callback)),
            "root swap must remain structurally valid");
    // This isolated checker test constructs the complete actual port view after
    // mutation. Both resources are used once; only the finite root law fails.
    // No cached pre-mutation association or old Program checker is reused.
    protocol::SourceExecutionClosure closure;
    closure.bodies["step"] = {
        {returned, llvm::to_vector(returned.getValues()), {}, {}, false}};
    auto workFunction =
        cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "work"));
    auto fold = cast<exec::FoldOp>(workFunction.front().front());
    auto dispatch = cast<exec::DispatchOp>(fold->getNextNode());
    auto *success = dispatch.getReturned();
    auto result = cast<exec::ReturnOp>(success->front());
    closure.bodies["work"] = {
        {fold,
         llvm::to_vector(fold->getOperands().drop_front()),
         llvm::to_vector(ValueRange(success->getArguments())),
         {},
         false},
        {result, llvm::to_vector(result.getValues()), {}, {}, false}};
    uint64_t work = 100000;
    auto roots = take(
        exec::ResourceOriginAnalysis::create(owner, std::move(closure), work));
    auto failure = roots->verifyFiniteState();
    require(bool(failure), "finite state accepted exchanged roots");
    require(
        namesIdentifier(toString(std::move(failure)), "mathematical-formation"),
        "finite state refusal lost its identifier");
  });
  return cases.result();
}
