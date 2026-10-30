#include "../lib/Dialect/Exec/ClosureAdmission.h"
#include "../lib/Dialect/Exec/ExecutionDefinitions.h"
#include "mlir/IR/Verifier.h"
#include "support/ResourceSources.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "llvm/ADT/ScopeExit.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::resource_sources;
namespace {
void rejected(Source &source, StringRef reason) {
  // Operation formation and scope/transfer ownership can both succeed while
  // actual logical data use is invalid. Do not invoke the enclosing verifier.
  for (auto function : source.owner.getBody().front().getOps<func::FuncOp>())
    require(succeeded(verify(function)), "mutation broke operation formation");
  refuses(protocol::readSourceExecutionClosure(source.owner), reason);
}
void accepted(Source &source) {
  take(protocol::readSourceExecutionClosure(source.owner));
}
void chain(Source &source, unsigned length) {
  for (unsigned i = 0; i < length; ++i) {
    auto function =
        source.function("f" + std::to_string(i), source.rng, source.rng);
    exec::ScopedExecutionBuilder control(source.builder, function);
    Value value = function.getArgument(1);
    if (i)
      value = source.call(control, "f" + std::to_string(i - 1), value,
                          source.rng, "call")[0];
    control.returned(value);
  }
}
} // namespace
int main() {
  Cases cases;
  cases.run("selected computation preflight bounds nesting before recursion",
            [] {
              Source source;
              SmallVector<ModuleOp> units;
              auto cleanup = llvm::scope_exit([&] {
                for (auto unit : llvm::reverse(units))
                  unit.erase();
              });
              Block *parent = &source.owner.getBody().front();
              for (unsigned i = 0; i < 10000; ++i) {
                auto unit = ModuleOp::create(source.location);
                parent->push_back(unit);
                units.push_back(unit);
                parent = unit.getBody();
              }
              units.front()->setAttr("exec.computation",
                                     source.builder.getUnitAttr());
              units.front().setSymName("selected");
              refuses(protocol::readSourceExecutionClosure(source.owner),
                      "execution-source-closure");
            });
  cases.run(
      "structural preflight has exact depth and cumulative work bounds", [] {
        Source source;
        SmallVector<ModuleOp> units;
        auto cleanup = llvm::scope_exit([&] {
          for (auto unit : llvm::reverse(units))
            unit.erase();
        });
        Block *parent = &source.owner.getBody().front();
        for (unsigned i = 0; i < 65; ++i) {
          auto unit = ModuleOp::create(source.location);
          parent->push_back(unit);
          units.push_back(unit);
          parent = unit.getBody();
        }
        unsigned remaining = 65;
        require(protocol::detail::executionStructureWithinLimit(units.front(),
                                                                remaining) &&
                    remaining == 0,
                "exact structural depth/work boundary refused");
        require(!protocol::detail::executionStructureWithinLimit(units.back(),
                                                                 remaining),
                "structural work allowance replenished");
        auto extra = ModuleOp::create(source.location);
        parent->push_back(extra);
        units.push_back(extra);
        remaining = 1000;
        require(!protocol::detail::executionStructureWithinLimit(units.front(),
                                                                 remaining),
                "excess structural nesting accepted");
        extra.erase();
        units.pop_back();
        for (unsigned i = 0; i < 100; ++i)
          units.front().getBody()->push_back(ModuleOp::create(source.location));
        remaining = 164;
        require(!protocol::detail::executionStructureWithinLimit(units.front(),
                                                                 remaining),
                "wide operation inventory bypassed work bound");
        remaining = 165;
        require(protocol::detail::executionStructureWithinLimit(units.front(),
                                                                remaining) &&
                    remaining == 0,
                "exact wide inventory refused");
      });
  cases.run("scope correctness does not admit affine reuse", [] {
    Source source;
    simple(source, "draw-reuse", true);
    rejected(source, "execution-resource-reuse");
  });
  cases.run("two affine formals cannot be supplied the same actual value", [] {
    Source source;
    auto identity =
        source.function("first", {source.rng, source.rng}, source.rng);
    exec::ScopedExecutionBuilder identityBody(source.builder, identity);
    identityBody.returned(identity.getArgument(1));
    auto caller = source.function("caller", source.rng, source.rng);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.returned(source.call(control, "first",
                                 {caller.getArgument(1), caller.getArgument(1)},
                                 source.rng, "use"));
    rejected(source, "execution-resource-reuse");
  });
  cases.run("copyable aliases remain separate closed-region formals", [] {
    Source source;
    auto caller =
        source.function("caller", {source.boolean, source.field}, source.field);
    exec::ScopedExecutionBuilder control(source.builder, caller);
    auto outputs = control.conditional(
        caller.getArgument(1), {caller.getArgument(2), caller.getArgument(2)},
        source.field, "choose", [&](unsigned) {
          auto region =
              source.region({source.field, source.field}, source.field);
          exec::ScopedExecutionBuilder body(source.builder, region);
          body.complete(region.getArgument(2));
          return region;
        });
    control.returned(outputs);
    accepted(source);
    // The byte grammar currently identifies captures only by actual name.
    // Export cannot erase a formal and its owned-storage charge.
    refuses(protocol::readSourceExecutionDefinitions(source.owner),
            "local-control-capture");
  });
  cases.run("occurrences include dormant nested arms", [] {
    Source source;
    auto caller = source.function("caller", source.boolean, {});
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.conditional(caller.getArgument(1), {}, {}, "choose", [&](unsigned) {
      auto region = source.region({}, {});
      exec::ScopedExecutionBuilder body(source.builder, region);
      body.reject("abort", "same");
      return region;
    });
    control.returned({});
    rejected(source, "execution-cfg");
  });
  cases.run("stopped arms cannot invent continuing results", [] {
    Source source;
    simple(source, "if-terminal", true);
    rejected(source, "execution-cfg");
  });
  cases.run("loop invariants cannot borrow affine values repeatedly", [] {
    Source source;
    auto caller = source.function("caller", {source.index, source.rng}, {});
    exec::ScopedExecutionBuilder control(source.builder, caller);
    control.loop(caller.getArgument(1), caller.getArgument(1), {},
                 caller.getArgument(2), {}, false, "loop", [&](unsigned) {
                   auto region = source.region({source.index, source.rng}, {});
                   exec::ScopedExecutionBuilder body(source.builder, region);
                   body.complete({});
                   return region;
                 });
    control.returned({});
    rejected(source, "execution-cfg");
  });
  cases.run("history behind an ordinary call remains forbidden in matches", [] {
    Source source;
    execution(source, "private-history");
    rejected(source, "execution-match-history");
  });
  cases.run("all call edges count even in dormant helpers", [] {
    Source source;
    chain(source, 3);
    auto first =
        cast<func::FuncOp>(SymbolTable::lookupSymbolIn(source.owner, "f0"));
    first.getBody().getBlocks().clear();
    first.addEntryBlock();
    source.builder.setInsertionPointToEnd(&first.front());
    exec::ScopedExecutionBuilder control(source.builder, first);
    control.returned(
        source.call(control, "f2", first.getArgument(1), source.rng, "cycle"));
    rejected(source, "execution-call-cycle");
  });
  for (unsigned length : {64u, 65u})
    cases.run("shared call depth " + std::to_string(length), [&] {
      Source source;
      chain(source, length);
      if (length == 64)
        accepted(source);
      else
        rejected(source, "execution-call-depth");
    });
  cases.run("native admission uses one work allowance", [] {
    Source source;
    chain(source, 3);
    auto closure = take(protocol::readSourceExecutionClosure(source.owner));
    uint64_t work = 10000;
    auto error =
        protocol::detail::verifyClosureUses(source.owner, closure, false, work);
    if (error)
      throw std::runtime_error(llvm::toString(std::move(error)));
    auto cost = 10000 - work;
    require(cost > 0, "native admission did not charge its work");
    work = cost;
    error =
        protocol::detail::verifyClosureUses(source.owner, closure, false, work);
    if (error)
      throw std::runtime_error(llvm::toString(std::move(error)));
    require(work == 0, "exact work charge changed");
    work = cost - 1;
    error =
        protocol::detail::verifyClosureUses(source.owner, closure, false, work);
    require(bool(error), "one-short budget admitted");
    auto diagnostic = llvm::toString(std::move(error));
    require(namesIdentifier(diagnostic, "execution-analysis-limit") ||
                namesIdentifier(diagnostic, "mathematical-analysis-limit"),
            "work exhaustion lost its diagnostic: " + diagnostic);
  });
  return cases.result();
}
