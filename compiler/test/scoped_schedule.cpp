#include "../lib/Transforms/Computation/Schedule.h"
#include "../lib/Transforms/ScopedCandidate.h"
#include "support/NumericalLoops.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::loops;
namespace {
protocol_ir::ProtocolModuleOp owner(mlir::ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
// Independently spell the expected traversal, ports, primitive occurrences and
// completion rules. No schedule reader or consumer supplies this body.
OwningOpRef<mlir::ModuleOp> expected(MLIRContext &context, bool omit = false,
                                     bool extra = false,
                                     bool structured = false) {
  auto location = UnknownLoc::get(&context);
  OwningOpRef<mlir::ModuleOp> module(mlir::ModuleOp::create(location));
  OpBuilder builder(module->getBody(), module->getBody()->end());
  auto root = protocol_ir::ProtocolModuleOp::create(builder, location,
                                                    protocol_ir::Profile::Exec);
  root.getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&root.getBody().front());
  for (auto [name, contract] :
       {std::pair{"add", "field.add"}, std::pair{"subtract", "field.sub"}})
    runtime::BindingOp::create(builder, location, name, contract,
                               builder.getStrArrayAttr({"bls12-381.fr"}), "");
  auto field = algebra::FieldType::get(&context, "bls12-381.fr");
  auto index = builder.getIntegerType(64, false);
  auto scope = runtime::ScopeType::get(&context);
  auto result = exec::OutcomeType::get(&context, {field, field});
  auto entry = func::FuncOp::create(
      builder, location, "evaluate",
      builder.getFunctionType({scope, index, index, field, field, field, field},
                              {result}));
  entry.setPrivate();
  entry.setNoInline(true);
  entry->setAttr("runtime.origin",
                 builder.getArrayAttr({builder.getStringAttr("evaluate"),
                                       builder.getArrayAttr({})}));
  entry.addEntryBlock();
  builder.setInsertionPointToEnd(&entry.front());
  exec::ScopedExecutionBuilder control(builder, entry);
  auto buildLoop = structured ? &exec::ScopedExecutionBuilder::scheduledLoop
                              : &exec::ScopedExecutionBuilder::loop;
  auto outputs = (control.*buildLoop)(
      entry.getArgument(1), entry.getArgument(2),
      entry.getArguments().slice(3, 2), entry.getArguments().slice(5, 2),
      TypeRange{field, field}, false, "traverse", [&](unsigned) {
        OpBuilder::InsertionGuard restore(builder);
        builder.setInsertionPointToEnd(&root.getBody().front());
        auto body = func::FuncOp::create(
            builder, location, "body",
            builder.getFunctionType({scope, index, field, field, field, field},
                                    {result}));
        body.setPrivate();
        body.setNoInline(true);
        body->setAttr("runtime.region", builder.getUnitAttr());
        body.addEntryBlock();
        builder.setInsertionPointToEnd(&body.front());
        exec::ScopedExecutionBuilder inner(builder, body);
        auto apply = [&](StringRef name, StringRef site, ValueRange inputs) {
          return inner.invoke(
              "exec.apply", TypeRange{field}, inner.scoped(inputs),
              {builder.getNamedAttr("binding",
                                    FlatSymbolRefAttr::get(&context, name)),
               builder.getNamedAttr("parameters", builder.getArrayAttr({})),
               builder.getNamedAttr("site", builder.getStringAttr(site))})[0];
        };
        Value sum = body.getArgument(2);
        if (!omit)
          sum = apply("add", "sum", {sum, body.getArgument(4)});
        if (extra)
          (void)apply("add", "extra", {sum, body.getArgument(4)});
        auto next = apply("subtract", "next", {sum, body.getArgument(5)});
        inner.complete({body.getArgument(3), next});
        return body;
      });
  control.returned(outputs);
  return module;
}
OwningOpRef<mlir::ModuleOp> scheduled(MLIRContext &context) {
  return expected(context, false, false, true);
}
void acceptSchedule(mlir::ModuleOp schedule, mlir::ModuleOp actual) {
  require(succeeded(computation::verifyRecipeOutput(actual)),
          "scoped recipe admission refused");
  require(succeeded(computation::verifyScheduleLowering(schedule, actual)),
          "actual scoped schedule differs");
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<scf::SCFDialect, arith::ArithDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run(
      "numerical candidate ports read the actual scoped SCF schedule", [&] {
        auto schedule = expected(context, false, false, true);
        auto flat = expected(context);
        auto root = owner(*schedule);
        auto entry = SymbolTable(root).lookup<func::FuncOp>("evaluate");
        auto actual = protocol::readScheduledExecutionClosure(root);
        require(bool(actual), actual ? "" : llvm::toString(actual.takeError()));
        auto error = protocol::verifySourceExecutionDefinitions(
            owner(*flat), actual->definitions);
        require(!error, error ? llvm::toString(std::move(error)) : "");
        auto view = mathematical::ScopedCandidate::readSchedule(root);
        require(bool(view), view ? "" : llvm::toString(view.takeError()));
        mathematical::CandidatePorts ports(view->get());
        auto *loop = ports.first(&entry.front());
        require(isa_and_nonnull<exec::RangeOp>(loop) &&
                    ports.bodies(loop) == 1 &&
                    ports.inputs(loop) == entry.getArguments().drop_front() &&
                    ports.outputs(loop).size() == 2,
                "loop data coordinates differ from actual schedule");
        auto *body = ports.body(loop, 0);
        auto *sum = ports.first(body);
        require(ports.arguments(body).size() == 5 &&
                    isa_and_nonnull<exec::ApplyOp>(sum) &&
                    ports.inputs(sum) == ValueRange{body->getArgument(2),
                                                    body->getArgument(4)} &&
                    ports.producer(ports.outputs(sum).front()) == sum,
                "outlined scalar association did not retain actual SSA");
        auto *returned = ports.next(loop);
        require(isa_and_nonnull<exec::ReturnOp>(returned) &&
                    !ports.next(returned) &&
                    ports.inputs(returned) == ports.outputs(loop),
                "scheduled output boundary differs");
      });
  cases.run("independent SCF and scoped execution agree", [&] {
    auto schedule = scheduled(context), native = expected(context);
    auto before = clone(*schedule), nativeBefore = clone(*native);
    acceptSchedule(*schedule, *native);
    uint64_t remaining = 1000000;
    auto result = computation::consumeSchedule(*schedule, remaining);
    require(bool(result), "scoped schedule consumption failed");
    acceptSchedule(*schedule, *result);
    require(same(*schedule, *before) && same(*native, *nativeBefore),
            "reader changed its input");
  });
  for (StringRef mutation :
       {"bound", "seed order", "capture order", "state order", "formula",
        "site", "missing instruction", "extra instruction", "dormant body",
        "nominal domain"})
    cases.run("independent reader refuses " + mutation, [&] {
      auto schedule = scheduled(context);
      auto candidate = expected(context, mutation == "missing instruction",
                                mutation == "extra instruction");
      auto root = owner(*candidate);
      auto entry = SymbolTable(root).lookup<func::FuncOp>("evaluate");
      auto body = SymbolTable(root).lookup<func::FuncOp>("body");
      if (mutation == "bound") {
        auto range =
            cast<exec::RangeOp>(operations(entry, "exec.range").front());
        range->setOperand(2, range->getOperand(1));
      } else if (mutation == "seed order" || mutation == "capture order") {
        unsigned start = mutation == "seed order" ? 3 : 5;
        auto a = entry.getArgument(start), b = entry.getArgument(start + 1);
        entry.walk([&](Operation *op) {
          for (auto &operand : op->getOpOperands()) {
            if (operand.get() == a)
              operand.set(b);
            else if (operand.get() == b)
              operand.set(a);
          }
        });
      } else if (mutation == "state order")
        operations(body, "exec.complete")
            .front()
            ->setOperand(1, body.getArgument(2));
      else if (mutation == "formula") {
        auto *apply = operations(body, "exec.apply").front();
        apply->setOperand(2, apply->getOperand(1));
      } else if (mutation == "site")
        operations(body, "exec.apply")
            .front()
            ->setAttr("site", StringAttr::get(&context, "changed"));
      else if (mutation == "dormant body") {
        auto duplicate = cast<func::FuncOp>(body->clone());
        duplicate.setSymName("unused");
        root.getBody().front().push_back(duplicate);
      }
      if (mutation == "nominal domain")
        SymbolTable(root).lookup<runtime::BindingOp>("add")->setAttr(
            "arguments", OpBuilder(&context).getStrArrayAttr({"bn254.fr"}));
      if (mutation == "dormant body" || mutation == "nominal domain")
        require(failed(computation::verifyRecipeOutput(*candidate)),
                "invalid declaration must fail admission");
      else
        require(succeeded(computation::verifyRecipeOutput(*candidate)),
                "semantic mutation should remain admitted");
      require(
          failed(computation::verifyScheduleLowering(*schedule, *candidate)),
          "changed semantics accepted");
    });
  cases.run("consumer capacity preserves immutable source", [&] {
    auto schedule = scheduled(context), before = clone(*schedule);
    uint64_t remaining = 0;
    require(!computation::consumeSchedule(*schedule, remaining) && !remaining &&
                same(*schedule, *before),
            "capacity published or changed input");
  });
  cases.run("reader exact capacity boundary", [&] {
    auto schedule = scheduled(context), native = expected(context);
    uint64_t remaining = 100000;
    require(succeeded(computation::verifyScheduleLowering(*schedule, *native,
                                                          &remaining)),
            "positive reader control failed");
    uint64_t exact = 100000 - remaining, shortWork = exact - 1;
    require(succeeded(computation::verifyScheduleLowering(*schedule, *native,
                                                          &exact)) &&
                !exact,
            "exact allowance failed");
    finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                       {}};
    require(failed(computation::verifyScheduleLowering(*schedule, *native,
                                                       &shortWork, &outcome)) &&
                outcome.status == finite::VerificationStatus::RequiredCapacity,
            "short allowance misclassified");
  });
  for (StringRef name : {"elements", "indices"})
    for (auto policy : {ordered, fused})
      cases.run(name + (policy.collectFoldFusion ? " fused scoped recipe"
                                                 : " ordered scoped recipe"),
                [&] {
                  auto unit = source(context, name);
                  mathematical::RealizationWork work;
                  uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
                  OwningOpRef<mlir::ModuleOp> schedule;
                  auto actual = computation::realizeEntry(
                      *unit, "collect_fold", policy, work, remaining, bytes, {},
                      nullptr, nullptr, nullptr, false, &schedule);
                  require(
                      bool(actual) && bool(schedule),
                      "numerical source did not realize into scoped execution");
                  acceptSchedule(*schedule, *actual);
                  zkc::test::loops::accepts(*unit, *actual, policy);
                });
  return cases.result();
}
