#include "../lib/Transforms/Computation/Schedule.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "support/NumericalLoops.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::loops;
namespace {
protocol_ir::ProtocolModuleOp owner(mlir::ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
func::FuncOp function(mlir::ModuleOp module) {
  return SymbolTable(owner(module)).lookup<func::FuncOp>("evaluate");
}
OwningOpRef<mlir::ModuleOp>
schedule(mlir::ModuleOp source, MathematicalSelectionPolicy policy = fused) {
  mathematical::RealizationWork work;
  uint64_t remaining = 1000000, bytes = 16 * 1024 * 1024;
  OwningOpRef<mlir::ModuleOp> selected;
  auto actual = computation::realizeEntry(source, "collect_fold", policy, work,
                                          remaining, bytes, {}, nullptr,
                                          nullptr, nullptr, false, &selected);
  require(bool(actual) && bool(selected), "selected schedule was not retained");
  require(succeeded(computation::verifyScheduledRecipeOutput(*selected)),
          "scoped schedule admission refused");
  return selected;
}
void scheduleAccepts(mlir::ModuleOp source, mlir::ModuleOp schedule,
                     MathematicalSelectionPolicy policy = fused) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch, {}};
  require(succeeded(computation::verifyEntrySchedule(
              source, schedule, "collect_fold", policy, {}, &outcome)) &&
              outcome.status == finite::VerificationStatus::Verified,
          "source does not match actual schedule");
}
void scheduleMismatch(mlir::ModuleOp source, mlir::ModuleOp schedule,
                      MathematicalSelectionPolicy policy = fused) {
  finite::VerificationResult outcome{finite::VerificationStatus::Verified, {}};
  require(failed(computation::verifyEntrySchedule(
              source, schedule, "collect_fold", policy, {}, &outcome)) &&
              outcome.status == finite::VerificationStatus::Mismatch,
          "source difference was accepted or classified as capacity");
}
OwningOpRef<mlir::ModuleOp> consume(mlir::ModuleOp scheduled) {
  uint64_t work = 1000000;
  auto result = computation::consumeSchedule(scheduled, work);
  require(bool(result) && work < 1000000,
          "schedule consumer failed or did not debit work");
  require(succeeded(computation::verifyScheduleLowering(scheduled, *result)),
          "SCF to CFG comparison refused");
  return result;
}
OwningOpRef<mlir::ModuleOp> controls(MLIRContext &context) {
  auto result = parseSourceString<mlir::ModuleOp>(R"mlir(
!tag = !data.variant<"variant:5b227a6b632e76617269616e742f30222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
module {
 module @numerical attributes {exec.computation} {
   func.func @evaluate(%condition:i1,%fallback:!tag)->(i1,!tag,i1) {
     %yes = arith.constant true
     %choice = "data.make"() {alternative="left"} : ()->!tag
     %present = "data.is"(%choice) {alternative="left"} : (!tag)->i1
     %selected = arith.select %condition,%present,%yes : i1
     func.return %yes,%choice,%selected : i1,!tag,i1
   }
 }
}
)mlir",
                                                  &context);
  require(bool(result), "Boolean/variant computation source did not verify");
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<scf::SCFDialect, arith::ArithDialect>();
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("Boolean and variant recipes use scoped control directly", [&] {
    auto original = controls(context);
    auto unit = cast<mlir::ModuleOp>(original->getBody()->front());
    auto selected = schedule(unit);
    for (llvm::StringRef name : {"exec.variant", "exec.match", "exec.test"})
      require(!operations(*selected, name).empty(),
              "missing direct scoped control");
    scheduleAccepts(unit, *selected);
    auto actual = consume(*selected);
    accepts(unit, *actual);
  });
  for (llvm::StringRef mutation :
       {"Boolean value", "Boolean type", "variant label", "variant type",
        "match labels", "match type"})
    cases.run("scoped schedule refuses malformed control: " + mutation, [&] {
      auto original = controls(context);
      auto unit = cast<mlir::ModuleOp>(original->getBody()->front());
      auto selected = schedule(unit);
      auto changed = clone(*selected);
      OpBuilder builder(&context);
      Operation *op;
      if (mutation.starts_with("Boolean")) {
        op = operations(*changed, "exec.boolean").front();
        if (mutation.ends_with("type"))
          op->setAttr("value", builder.getStringAttr("true"));
        else
          op->removeAttr("value");
      } else if (mutation.starts_with("variant")) {
        op = operations(*changed, "exec.variant").front();
        if (mutation.ends_with("type"))
          op->setAttr("alternative", builder.getBoolAttr(true));
        else
          op->removeAttr("alternative");
      } else {
        op = operations(*changed, "exec.match").front();
        if (mutation.ends_with("type"))
          op->setAttr("alternatives", builder.getStringAttr("left"));
        else
          op->removeAttr("alternatives");
      }
      ScopedDiagnosticHandler quiet(&context,
                                    [](Diagnostic &) { return success(); });
      scheduleMismatch(unit, *changed);
      uint64_t work = 1000000;
      require(!computation::consumeSchedule(*changed, work),
              "malformed schedule was consumed");
      scheduleAccepts(unit, *selected);
    });
  cases.run(
      "scoped scalar branches remain outlined within finite traversal", [&] {
        auto unit = source(context, "elements");
        auto callback = helper(*unit, "body");
        auto returned = cast<func::ReturnOp>(callback.front().back());
        OpBuilder builder(returned);
        OperationState comparison(returned.getLoc(), "algebra.field_equal");
        comparison.addOperands(
            {callback.getArgument(0), callback.getArgument(2)});
        comparison.addTypes(builder.getI1Type());
        auto condition = builder.create(comparison)->getResult(0);
        auto controlSource = controls(context);
        auto prototype = mathematical::getComputationEntry(
            cast<mlir::ModuleOp>(controlSource->getBody()->front()));
        IRMapping values;
        values.map(prototype.getArgument(0), condition);
        for (auto &op : prototype.front().without_terminator())
          builder.clone(op, values);
        auto selector = values.lookup(prototype.front().back().getOperand(2));
        auto selected = arith::SelectOp::create(
            builder, returned.getLoc(), selector, returned.getOperand(0),
            callback.getArgument(0));
        returned->setOperand(0, selected.getResult());
        require(succeeded(mlir::verify(*unit)),
                "conditional callback is malformed");
        auto local = realize(*unit);
        auto scheduled = schedule(*unit);
        for (StringRef name : {"exec.test", "exec.match", "exec.variant"}) {
          auto nested = operations(*scheduled, name);
          require(llvm::any_of(nested,
                               [](Operation *op) {
                                 auto function =
                                     op->getParentOfType<func::FuncOp>();
                                 return function &&
                                        function->hasAttr("runtime.region");
                               }),
                  "callback control did not remain nested inside SCF: " + name);
        }
        scheduleAccepts(*unit, *scheduled);
        auto actual = consume(*scheduled);
        require(
            succeeded(computation::verifyScheduleLowering(*scheduled, *actual)),
            "nested conditional schedule consumption disagrees");
        accepts(*unit, *actual);
      });
  for (StringRef mutation :
       {"module region", "module result", "function region",
        "missing function type", "nonfunction type property"})
    cases.run("schedule checks builtin shape before access: " + mutation, [&] {
      auto original = controls(context);
      auto unit = cast<mlir::ModuleOp>(original->getBody()->front());
      auto local = realize(unit);
      auto scheduled = schedule(unit);
      auto changed = clone(*scheduled);
      OpBuilder builder(&context);
      if (mutation == "module region" || mutation == "module result") {
        OperationState state(changed->getLoc(),
                             mlir::ModuleOp::getOperationName());
        if (mutation == "module result") {
          state.addTypes(builder.getI1Type());
          state.addRegion();
        }
        auto *replacement = Operation::create(state);
        if (mutation == "module result")
          replacement->getRegion(0).takeBody(changed->getBodyRegion());
        changed =
            OwningOpRef<mlir::ModuleOp>(cast<mlir::ModuleOp>(replacement));
      } else {
        auto target = function(*changed);
        if (mutation == "function region") {
          OperationState state(target.getLoc(), target->getName());
          state.addAttributes(target->getAttrs());
          builder.setInsertionPoint(target);
          builder.create(state);
          target.erase();
        } else if (mutation == "missing function type")
          target->removeAttr("function_type");
        else
          target->setAttr("function_type", TypeAttr::get(builder.getI1Type()));
      }
      scheduleMismatch(unit, *changed);
      uint64_t work = 1000000;
      require(!computation::consumeSchedule(*changed, work) &&
                  failed(computation::verifyScheduleLowering(*changed, *local)),
              "malformed builtin shape reached a generated accessor");
      scheduleAccepts(unit, *scheduled);
    });

  for (llvm::StringRef name : {"elements", "indices", "nonzero_seeds",
                               "unit_state", "mixed_states", "nested_checks"})
    for (bool sequence : {false, true})
      for (auto policy : {ordered, fused})
        cases.run(name + (sequence ? " sequence" : " vector") +
                      (policy.collectFoldFusion ? " fused scoped schedule"
                                                : " ordered scoped schedule"),
                  [&] {
                    auto unit = source(context, name, "bls12-381.fr", sequence);
                    auto before = clone(*unit);
                    auto selected = schedule(*unit, policy);
                    auto scheduleBefore = clone(*selected);
                    require(!operations(*selected, "scf.while").empty(),
                            "no actual SCF loop");
                    selected->walk([&](Operation *op) {
                      require(op->getName().getDialectNamespace() != "local",
                              "Local recipe survived");
                    });
                    scheduleAccepts(*unit, *selected, policy);
                    auto actual = consume(*selected);
                    require(operations(*actual, "scf.while").empty(),
                            "SCF schedule escaped into CFG");
                    accepts(*unit, *actual, policy);
                    require(same(*unit, *before) &&
                                same(*selected, *scheduleBefore),
                            "source or schedule mutated");
                  });
  for (llvm::StringRef name : {"elements", "indices"})
    for (llvm::StringRef mutation : {"producer formula", "consumer formula",
                                     "bound", "seed order", "result order"})
      cases.run(
          name + " original source refuses actual schedule change: " + mutation,
          [&] {
            auto unit = source(context, name);
            auto selected = schedule(*unit);
            auto changed = clone(*selected);
            if (mutation == "producer formula" ||
                mutation == "consumer formula") {
              llvm::SmallVector<Operation *> calls;
              changed->walk([&](exec::ApplyOp op) {
                if (primitiveBinding(op).getContract() ==
                    (mutation == "producer formula" ? "field.mul"
                                                    : "field.sub"))
                  calls.push_back(op);
              });
              require(calls.size() >=
                          (mutation == "producer formula" ? 2u : 1u),
                      "missing recipe formula");
              auto *op = mutation == "producer formula" ? calls[1] : calls[0];
              op->setOperand(2, op->getOperand(1));
            } else if (mutation == "bound") {
              auto range = operations(*changed, "exec.range").back();
              range->setOperand(2, range->getOperand(1));
            } else if (mutation == "seed order") {
              runtime::BorrowTransferOp transfer;
              changed->walk([&](runtime::BorrowTransferOp op) {
                if (op.getInputs().size() == 2)
                  transfer = op;
              });
              require(bool(transfer), "missing carried pair");
              auto first = transfer->getOperand(1),
                   second = transfer->getOperand(2);
              transfer->setOperand(1, second);
              transfer->setOperand(2, first);
            } else {
              auto returned =
                  operations(function(*changed), "exec.returned").back();
              // The root return has data payload; administrative transfer
              // packaging inside SCF carries a single transfer.
              require(returned->getNumOperands() == 2,
                      "missing root result pair");
              auto first = returned->getOperand(0),
                   second = returned->getOperand(1);
              returned->setOperand(0, second);
              returned->setOperand(1, first);
            }
            require(
                succeeded(computation::verifyScheduledRecipeOutput(*changed)),
                "semantic mutation malformed the schedule");
            scheduleMismatch(*unit, *changed);
            auto actual = consume(*changed);
            mismatch(*unit, *actual);
            scheduleAccepts(*unit, *selected);
          });
  cases.run(
      "zero construction and comparison allowances preserve sources", [&] {
        auto unit = source(context, "elements");
        auto selected = schedule(*unit), before = clone(*selected);
        uint64_t work = 0;
        require(!computation::consumeSchedule(*selected, work) && !work &&
                    same(*selected, *before),
                "zero copy allowance mutated input");
        auto actual = consume(*selected);
        finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                           {}};
        require(failed(computation::verifyScheduleLowering(*selected, *actual,
                                                           &work, &outcome)) &&
                    outcome.status ==
                        finite::VerificationStatus::RequiredCapacity,
                "zero comparison allowance was not required capacity");
      });
  return cases.result();
}
