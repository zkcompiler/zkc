#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ResourceSources.h"
#include "zkc/Analysis/ExecutionObservations.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::resource_sources;
namespace {
BitVector bits(unsigned width, ArrayRef<unsigned> indices) {
  BitVector result(width);
  for (unsigned index : indices)
    result.set(index);
  return result;
}
void admitted(Source &source) {
  require(succeeded(verify(*source.module)), "malformed observation fixture");
  take(protocol::readSourceExecutionClosure(source.owner));
}
void observe(const ExecutionObservationSummary &summary,
             ArrayRef<BitVector> results, BitVector stops, bool returns,
             bool stopping) {
  require(summary.results == results && summary.stops == stops &&
              summary.mayReturn == returns && summary.mayStop == stopping,
          "incorrect observation summary");
}
} // namespace
// Optional integration probe over the actual emitted closure. This inspects
// all retained local calls at the requested role, not entry reachability or a
// public-coin judgment. The ordinary CTest invocation runs the controls below.
int probe(StringRef path, StringRef role) {
  Source context;
  auto module = parseSourceFile<ModuleOp>(path, &context.context);
  if (!module || failed(zkc::admitStage(*module)))
    return 1;
  ExecutionObservationAnalysis analysis(*module);
  SymbolTableCollection symbols;
  llvm::DenseSet<Operation *> inspected;
  uint64_t remaining = 1000000;
  facts::Work work(remaining);
  unsigned calls = 0, failures = 0;
  auto result = module->walk([&](protocol_ir::LocalCallOp call) {
    if (call.getRole() != role)
      return WalkResult::advance();
    ++calls;
    auto function = symbols.lookupNearestSymbolFrom<func::FuncOp>(
        call, call.getCalleeAttr());
    if (!inspected.insert(function).second)
      return WalkResult::advance();
    auto summary = analysis.get(function, work);
    if (!summary) {
      errs() << "helper " << call.getCallee() << ": "
             << toString(summary.takeError()) << '\n';
      ++failures;
      if (work.exhausted() || failures >= 16)
        return WalkResult::interrupt();
      analysis.clear();
    }
    return WalkResult::advance();
  });
  outs() << "local calls: " << calls
         << ", distinct helpers: " << inspected.size()
         << ", work used: " << 1000000 - remaining << ", refused: " << failures
         << ", interrupted: " << result.wasInterrupted() << '\n';
  return !calls || failures || result.wasInterrupted();
}
int main(int argc, char **argv) {
  if (argc == 3)
    return probe(argv[1], argv[2]);
  if (argc != 1)
    return 2;
  Cases cases;
  cases.run("exact aliased argument substitution and shared summary", [] {
    Source source;
    auto second =
        source.function("second", {source.field, source.field}, source.field);
    exec::ScopedExecutionBuilder inner(source.builder, second);
    inner.returned(second.getArgument(2));
    auto caller =
        source.function("caller", {source.field, source.field}, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    Value result = caller.getArgument(1);
    for (unsigned i = 0; i < 80; ++i)
      result = source.call(control, "second", {caller.getArgument(2), result},
                           source.field, "call" + std::to_string(i))[0];
    control.returned(result);
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    const auto *cached = take(analysis.get(second, work));
    const auto *summary = take(analysis.get(caller, work));
    observe(*summary, {bits(2, {0})}, bits(2, {}), true, false);
    require(summary->callees.size() == 1 && summary->depth == 2,
            "repeated helper was expanded");
    require(cached == take(analysis.get(second, work)),
            "summary address changed after another definition");
    auto before = remaining;
    take(analysis.get(caller, work));
    require(remaining < before, "cache reuse escaped the caller allowance");
  });
  cases.run("an unused partial call still controls continuation", [] {
    Source source;
    source.binding("invert", "field.inverse", {"bls12-381.fr"});
    auto partial = source.function("partial", source.field, {});
    exec::ScopedExecutionBuilder inner(source.builder, partial);
    source.invoke(inner, "invert", partial.getArgument(1), source.field,
                  "ignored");
    inner.returned({});
    auto caller =
        source.function("caller", {source.field, source.field}, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    source.call(control, "partial", caller.getArgument(2), {}, "no_result");
    control.returned(caller.getArgument(1));
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    observe(*take(analysis.get(caller, work)), {bits(2, {0, 1})}, bits(2, {1}),
            true, true);
    auto *primitive = take(analysis.get(partial, work));
    require(primitive->primitives.size() == 1 &&
                primitive->primitives[0]->getName().getStringRef() ==
                    "exec.apply",
            "actual eager primitive occurrence was lost");
  });
  for (bool stops : {false, true})
    cases.run(stops ? "stopped branch contributes only control"
                    : "branch results retain conditions",
              [&] {
                Source source;
                auto caller = source.function(
                    "branch", {source.boolean, source.field, source.field},
                    source.field);
                exec::ScopedExecutionBuilder control(source.builder, caller);
                auto result = control.conditional(
                    caller.getArgument(1),
                    {caller.getArgument(2), caller.getArgument(3)},
                    source.field, "choice", [&](unsigned arm) {
                      auto body = source.region({source.field, source.field},
                                                source.field);
                      exec::ScopedExecutionBuilder inner(source.builder, body);
                      if (stops && arm == 0)
                        inner.reject("refused", "stop");
                      else
                        inner.complete(body.getArgument(1 + arm));
                      return body;
                    });
                control.returned(result);
                admitted(source);
                ExecutionObservationAnalysis analysis(*source.module);
                uint64_t remaining = 100000;
                facts::Work work(remaining);
                observe(*take(analysis.get(caller, work)),
                        {stops ? bits(3, {0, 2}) : bits(3, {0, 1, 2})},
                        stops ? bits(3, {0}) : bits(3, {}), true, stops);
              });
  cases.run("swap carry reaches a fixed point and retains zero trips", [] {
    Source source;
    auto caller = source.function(
        "loop", {source.index, source.index, source.field, source.field},
        {source.field, source.field});
    exec::ScopedExecutionBuilder control(source.builder, caller);
    auto result = control.loop(
        caller.getArgument(1), caller.getArgument(2),
        {caller.getArgument(3), caller.getArgument(4)}, {},
        {source.field, source.field}, false, "swap", [&](unsigned) {
          auto body = source.region({source.index, source.field, source.field},
                                    {source.field, source.field});
          exec::ScopedExecutionBuilder inner(source.builder, body);
          inner.complete({body.getArgument(3), body.getArgument(2)});
          return body;
        });
    control.returned(result);
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    observe(*take(analysis.get(caller, work)),
            {bits(4, {0, 1, 2, 3}), bits(4, {0, 1, 2, 3})}, bits(4, {0, 1}),
            true, true);
  });
  cases.run("unconditional stop has no fabricated successful result", [] {
    Source source;
    auto caller = source.function("stop", source.field, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.reject("abort", "stop");
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    observe(*take(analysis.get(caller, work)), {bits(1, {})}, bits(1, {}),
            false, true);
  });
  cases.run("resource authority is not deterministic data", [] {
    Source source;
    auto caller = source.function("identity", source.rng, source.rng);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.returned(caller.getArgument(1));
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    refuses(analysis.get(caller, work), "execution-observation-unsupported");
  });
  for (StringRef kind : {"commitment", "proof", "opening_state"})
    for (bool nested : {false, true})
      cases.run("row object custody " + kind.str() + (nested ? " nested" : ""),
                [&] {
                  Source source;
                  auto text = "!commitment.vector<\"rows.merkle-keccak256."
                              "koala-bear/0\", \"" +
                              kind.str() + "\">";
                  Type type = parseType(text, &source.context);
                  require(bool(type), "invalid row object type");
                  if (nested)
                    type = data::SequenceType::get(&source.context, type);
                  auto caller = source.function("identity", type, type);
                  exec::ScopedExecutionBuilder control(source.builder, caller);
                  control.returned(caller.getArgument(1));
                  admitted(source);
                  ExecutionObservationAnalysis analysis(*source.module);
                  uint64_t remaining = 100000;
                  facts::Work work(remaining);
                  if (kind == "opening_state")
                    refuses(analysis.get(caller, work),
                            "execution-observation-unsupported");
                  else
                    observe(*take(analysis.get(caller, work)), {bits(1, {0})},
                            bits(1, {}), true, false);
                });
  cases.run("owner and sticky capacity are checked on cache hits", [] {
    Source source;
    auto caller = source.function("identity", source.field, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.returned(caller.getArgument(1));
    admitted(source);
    ExecutionObservationAnalysis foreign(source.owner);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    refuses(foreign.get(caller, work), "execution-observation-owner");
    ExecutionObservationAnalysis analysis(*source.module);
    take(analysis.get(caller, work));
    remaining = 1;
    refuses(analysis.get(caller, work), "execution-observation-capacity");
    remaining = 100000;
    facts::Work fresh(remaining);
    refuses(analysis.get(caller, fresh), "execution-observation-capacity");
    analysis.clear();
    take(analysis.get(caller, fresh));
  });
  for (StringRef fixture : {"collect", "aliased-predicate", "dot"})
    cases.run("finite callback closure " + fixture.str(), [&] {
      Source source;
      auto buffer = MemoryBuffer::getFile(std::string(ZKC_FIXTURES) +
                                          "/finite/" + fixture.str() + ".mlir");
      require(bool(buffer), "missing finite fixture");
      auto module =
          parseSourceString<ModuleOp>((*buffer)->getBuffer(), &source.context);
      require(module && succeeded(verify(*module)), "invalid finite fixture");
      auto owner =
          cast<protocol_ir::ProtocolModuleOp>(module->getBody()->front());
      take(protocol::readSourceExecutionClosure(owner));
      auto function =
          cast<func::FuncOp>(SymbolTable::lookupSymbolIn(owner, "work"));
      ExecutionObservationAnalysis analysis(*module);
      uint64_t remaining = 100000;
      facts::Work work(remaining);
      auto *summary = take(analysis.get(function, work));
      require(summary->mayReturn && summary->mayStop && summary->stops.all() &&
                  !summary->callees.empty(),
              "finite callback observation was omitted");
      for (const auto &result : summary->results)
        require(result.all(), "finite conservative feedback lost an input");
      if (fixture == "aliased-predicate")
        require(summary->callees.size() == 2, "predicate was not inspected");
    });
  cases.run("mathematical compute uses its actual total helper", [] {
    Source source;
    source.builder.setInsertionPointToEnd(&source.owner.getBody().front());
    auto helper =
        func::FuncOp::create(source.builder, source.location, "math",
                             source.builder.getFunctionType(
                                 {source.field, source.field}, source.field));
    helper.setPrivate();
    source.builder.setInsertionPointToEnd(helper.addEntryBlock());
    func::ReturnOp::create(source.builder, source.location,
                           helper.getArgument(1));
    auto caller =
        source.function("caller", {source.field, source.field}, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    auto value = control.invoke(
        "exec.compute", source.field,
        control.scoped({caller.getArgument(1), caller.getArgument(2)}),
        {source.symbol("callee", "math"), source.text("site", "math")});
    control.returned(value);
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    observe(*take(analysis.get(caller, work)), {bits(2, {1})}, bits(2, {}),
            true, false);
    analysis.clear();
    cast<func::ReturnOp>(helper.getBody().front().back())
        .setOperand(0, helper.getArgument(0));
    observe(*take(analysis.get(caller, work)), {bits(2, {0})}, bits(2, {}),
            true, false);
  });
  cases.run("all insufficient cumulative work limits refuse", [] {
    Source source;
    auto caller = source.function("identity", source.field, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.returned(caller.getArgument(1));
    admitted(source);
    auto query = [&](uint64_t &remaining) -> Error {
      ExecutionObservationAnalysis analysis(*source.module);
      facts::Work work(remaining);
      auto result = analysis.get(caller, work);
      if (!result)
        return result.takeError();
      return Error::success();
    };
    uint64_t remaining = 100000;
    if (auto e = query(remaining))
      throw std::runtime_error(toString(std::move(e)));
    uint64_t cost = 100000 - remaining;
    require(cost > 0 && cost < 1000, "unexpected observation cost");
    for (uint64_t limit = 0; limit < cost; ++limit) {
      uint64_t allowance = limit;
      auto e = query(allowance);
      require(bool(e), "insufficient allowance supplied a summary");
      require(namesIdentifier(toString(std::move(e)),
                              "execution-observation-capacity"),
              "capacity was reported as missing semantics");
    }
    if (auto e = query(cost))
      throw std::runtime_error(toString(std::move(e)));
    require(cost == 0, "exact observation allowance differs");
  });
  cases.run("public replay does not grant deterministic-data authority", [] {
    Source source;
    auto group = parseType("!algebra.group<\"bls12-381.g1\">", &source.context);
    require(bool(group), "invalid group fixture");
    source.binding("equal", "curve.equal", {"bls12-381.g1"});
    auto caller = source.function("compare", {group, group}, source.boolean);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    auto result = source.invoke(control, "equal",
                                {caller.getArgument(1), caller.getArgument(2)},
                                source.boolean, "equal");
    control.returned(result);
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    refuses(analysis.get(caller, work), "execution-observation-unsupported");
  });
  cases.run("variant payload and capture have distinct actual formals", [] {
    Source source;
    Type variant = data::importVariantType(
        &source.context,
        {"Payload", {{"value", {"field:bls12-381.fr"}}, {"empty", {}}}});
    auto caller =
        source.function("match", {variant, source.field}, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    auto result = control.match(
        caller.getArgument(1), caller.getArgument(2), source.field,
        {"value", "empty"}, "match", [&](unsigned arm) {
          SmallVector<Type> arguments(arm == 0 ? 2 : 1, source.field);
          auto body = source.region(arguments, source.field);
          exec::ScopedExecutionBuilder inner(source.builder, body);
          inner.complete(body.getArgument(1));
          return body;
        });
    control.returned(result);
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    observe(*take(analysis.get(caller, work)), {bits(2, {0, 1})}, bits(2, {}),
            true, false);
  });
  cases.run("conditional backedges retain their controlling input", [] {
    Source source;
    auto caller = source.function(
        "loop", {source.index, source.index, source.field, source.boolean},
        source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    auto result = control.loop(
        caller.getArgument(1), caller.getArgument(2), caller.getArgument(3),
        caller.getArgument(4), source.field, true, "loop", [&](unsigned) {
          auto body =
              source.region({source.index, source.field, source.boolean},
                            {source.boolean, source.field});
          exec::ScopedExecutionBuilder inner(source.builder, body);
          inner.complete({body.getArgument(3), body.getArgument(2)});
          return body;
        });
    control.returned(result);
    admitted(source);
    ExecutionObservationAnalysis analysis(*source.module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    observe(*take(analysis.get(caller, work)), {bits(4, {0, 1, 2, 3})},
            bits(4, {0, 1, 3}), true, true);
  });
  return cases.result();
}
