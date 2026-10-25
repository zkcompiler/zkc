#include "../lib/Transforms/Kernel/Schedule.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "support/NumericalLoops.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/Execution.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::loops;

namespace {
OwningOpRef<mlir::ModuleOp> authored(MLIRContext &context, StringRef name) {
  auto bytes = llvm::MemoryBuffer::getFile(
      (Twine(ZKC_LOOP_FIXTURES) + "/" + name + ".mlir").str());
  require(bool(bytes), "missing independently authored fixture");
  // The expected Local fragment has no participant Entry and uses its dedicated
  // fragment admission. The schedule must pass ordinary MLIR verification.
  auto result = parseSourceString<mlir::ModuleOp>(
      (*bytes)->getBuffer(),
      ParserConfig(&context, name != "authored-schedule-local"));
  require(bool(result), "independently authored fixture did not parse");
  return result;
}
func::FuncOp function(mlir::ModuleOp module) {
  auto result = SymbolTable(module).lookup<func::FuncOp>("evaluate");
  require(bool(result), "schedule lost its standard function");
  return result;
}
scf::ForOp loop(mlir::ModuleOp module) {
  auto all = operations(module, "scf.for");
  require(all.size() == 1, "fixture must contain one actual SCF traversal");
  return cast<scf::ForOp>(all.front());
}
Operation *packetStart(scf::ForOp scheduled) {
  auto *at = scheduled.getOperation();
  for (unsigned i = 0; i < 5; ++i) {
    at = at->getPrevNode();
    require(at, "incomplete scheduled loop packet");
  }
  return at;
}
void scheduleAccepts(mlir::ModuleOp source, mlir::ModuleOp schedule,
                     MathematicalSelectionPolicy policy = fused,
                     finite::VerificationLimits limits = {}) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch, {}};
  require(succeeded(kernel::verifyEntrySchedule(
              source, schedule, "collect_fold", policy, limits, &outcome)) &&
              outcome.status == finite::VerificationStatus::Verified,
          "original source did not match actual scheduled instructions");
}
void scheduleMismatch(mlir::ModuleOp source, mlir::ModuleOp schedule,
                      MathematicalSelectionPolicy policy = fused) {
  finite::VerificationResult outcome{finite::VerificationStatus::Verified, {}};
  require(failed(kernel::verifyEntrySchedule(source, schedule, "collect_fold",
                                             policy, {}, &outcome)) &&
              outcome.status == finite::VerificationStatus::Mismatch,
          "schedule difference was accepted or classified as capacity");
}
OwningOpRef<mlir::ModuleOp> schedule(mlir::ModuleOp local) {
  uint64_t work = 1000000;
  auto result = kernel::scheduleEntry(local, work);
  require(bool(result) && work < 1000000,
          "actual schedule producer failed or did not debit work");
  require(succeeded(mlir::verify(*result)),
          "produced schedule is not valid ordinary MLIR");
  return result;
}
OwningOpRef<mlir::ModuleOp> controls(MLIRContext &context) {
  auto result = parseSourceString<mlir::ModuleOp>(R"mlir(
!tag = !local.variant<"variant:5b227a6b632e76617269616e742f30222c5b2243686f696365222c226c656674222c5b5d2c5b2231222c2232225d2c227269676874222c5b2234222c2232225d2c5b2233222c2235225d2c5b2230222c2236225d5d5d">
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
  require(bool(result), "Boolean/variant Kernel source did not verify");
  return result;
}
OwningOpRef<mlir::ModuleOp> consume(mlir::ModuleOp scheduled) {
  uint64_t work = 1000000;
  auto result = kernel::consumeSchedule(scheduled, work);
  require(bool(result) && work < 1000000,
          "actual schedule consumer failed or did not debit work");
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
  cases.run("Boolean and variant schedules verify as ordinary MLIR", [&] {
    auto original = controls(context);
    auto unit = cast<mlir::ModuleOp>(original->getBody()->front());
    auto local = realize(unit);
    auto scheduled = schedule(*local);
    require(operations(*scheduled, "local.variant_inject").size() == 1 &&
                operations(*scheduled, "local.match").size() == 1 &&
                operations(*scheduled, "local.if").size() == 1,
            "control fixture did not exercise all Local control verifiers");
    scheduleAccepts(unit, *scheduled);
    auto actual = consume(*scheduled);
    require(succeeded(kernel::verifyScheduleLowering(*scheduled, *actual)),
            "Boolean/variant schedule consumption disagrees");
    accepts(unit, *actual);
  });

  for (StringRef mutation :
       {"missing Boolean value", "Boolean value type", "missing Boolean result",
        "missing variant alternative", "variant alternative type",
        "missing match alternatives", "match alternatives type",
        "match label type"})
    cases.run("ordinary verifier rejects schedule shape: " + mutation, [&] {
      auto original = controls(context);
      auto unit = cast<mlir::ModuleOp>(original->getBody()->front());
      auto local = realize(unit);
      auto scheduled = schedule(*local);
      auto changed = clone(*scheduled);
      OpBuilder builder(&context);
      Operation *malformed = nullptr;
      if (mutation.contains("Boolean")) {
        auto *value = operations(*changed, "local.bool_constant").front();
        malformed = value;
        if (mutation == "missing Boolean value")
          value->removeAttr("value");
        else if (mutation == "Boolean value type")
          value->setAttr("value", builder.getStringAttr("true"));
        else {
          // Keep function/result types and SSA closure valid, so this reaches
          // operation admission rather than a function-signature refusal.
          value->getResult(0).replaceAllUsesWith(
              function(*changed).getArgument(0));
          OperationState state(value->getLoc(), value->getName());
          state.addAttributes(value->getAttrs());
          builder.setInsertionPoint(value);
          malformed = builder.create(state);
          value->erase();
        }
      } else if (mutation.contains("variant")) {
        malformed = operations(*changed, "local.variant_inject").front();
        if (mutation == "missing variant alternative")
          malformed->removeAttr("alternative");
        else
          malformed->setAttr("alternative", builder.getBoolAttr(true));
      } else {
        malformed = operations(*changed, "local.match").front();
        if (mutation == "missing match alternatives")
          malformed->removeAttr("alternatives");
        else if (mutation == "match alternatives type")
          malformed->setAttr("alternatives", builder.getStringAttr("left"));
        else
          malformed->setAttr(
              "alternatives",
              builder.getArrayAttr(
                  {builder.getBoolAttr(true), builder.getStringAttr("right")}));
      }
      std::string diagnostic;
      llvm::raw_string_ostream stream(diagnostic);
      ScopedDiagnosticHandler handler(&context, [&](Diagnostic &message) {
        message.print(stream);
        return success();
      });
      require(failed(mlir::verify(*changed)),
              "malformed control passed ordinary MLIR verification");
      diagnostic.clear();
      scheduleMismatch(unit, *changed);
      require(diagnostic.find(malformed->getName().getStringRef().str()) !=
                  std::string::npos,
              "schedule reader did not reach ordinary operation admission");
      uint64_t work = 1000000;
      require(!kernel::consumeSchedule(*changed, work) &&
                  failed(kernel::verifyScheduleLowering(*changed, *local)),
              "malformed schedule reached another typed reader");
      scheduleAccepts(unit, *scheduled);
    });

  cases.run("isolated Local controls verify inside scheduled SCF", [&] {
    auto unit = source(context, "elements");
    auto callback = helper(*unit, "body");
    auto returned = cast<func::ReturnOp>(callback.front().back());
    OpBuilder builder(returned);
    OperationState comparison(returned.getLoc(), "algebra.field_equal");
    comparison.addOperands({callback.getArgument(0), callback.getArgument(2)});
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
    auto selected = arith::SelectOp::create(builder, returned.getLoc(),
                                            selector, returned.getOperand(0),
                                            callback.getArgument(0));
    returned->setOperand(0, selected.getResult());
    require(succeeded(mlir::verify(*unit)),
            "conditional callback is malformed");
    auto local = realize(*unit);
    auto scheduled = schedule(*local);
    for (StringRef name : {"local.if", "local.match", "local.variant_inject"}) {
      auto nested = operations(*scheduled, name);
      require(llvm::any_of(nested,
                           [](Operation *op) {
                             return bool(op->getParentOfType<scf::ForOp>());
                           }),
              "callback control did not remain nested inside SCF: " + name);
    }
    scheduleAccepts(*unit, *scheduled);
    auto actual = consume(*scheduled);
    require(succeeded(kernel::verifyScheduleLowering(*scheduled, *actual)),
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
      auto scheduled = schedule(*local);
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
      require(!kernel::consumeSchedule(*changed, work) &&
                  failed(kernel::verifyScheduleLowering(*changed, *local)),
              "malformed builtin shape reached a generated accessor");
      scheduleAccepts(unit, *scheduled);
    });

  for (StringRef placement : {"function", "control", "primitive"})
    cases.run("native profile still refuses misplaced " + placement, [&] {
      auto program = parseSourceString<mlir::ModuleOp>(R"mlir(
module { "protocol.module"() ({
 "protocol.participant"() ({ ^entry(%condition:i1):
   "protocol.finish"(%condition) : (i1)->()
 }) {sym_name="endpoint",function_type=(i1)->i1,instance="main",role="P"} : ()->()
 "protocol.entry"() {sym_name="main",targets=[["P",@endpoint]]} : ()->()
}) {profile=#protocol.profile<exec>} : ()->() }
)mlir",
                                                       &context);
      require(bool(program),
              "native placement positive control did not verify");
      auto owner =
          cast<protocol_ir::ProtocolModuleOp>(program->getBody()->front());
      OpBuilder builder(&context);
      StringRef expected;
      if (placement == "primitive") {
        builder.setInsertionPointToStart(&owner.getBody().front());
        local::OperationBindingOp::create(builder, owner.getLoc(), "combine",
                                          "bool.and", builder.getArrayAttr({}),
                                          "", mlir::ArrayAttr{});
        auto endpoint = *owner.getBody()
                             .front()
                             .getOps<protocol_ir::ParticipantOp>()
                             .begin();
        auto &body = endpoint->getRegion(0).front();
        builder.setInsertionPoint(&body.back());
        OperationState state(owner.getLoc(),
                             protocol::boundOperationName("bool.and"));
        state.addOperands({body.getArgument(0), body.getArgument(0)});
        state.addTypes(builder.getI1Type());
        state.addAttribute("binding",
                           FlatSymbolRefAttr::get(&context, "combine"));
        state.addAttribute("site", builder.getStringAttr("misplaced"));
        state.addAttribute("parameters", builder.getArrayAttr({}));
        auto *primitive = builder.create(state);
        require(succeeded(mlir::verify(primitive)),
                "logical primitive failed standalone binding verification");
        expected = "binding-operation";
      } else if (placement == "control") {
        auto endpoint = *owner.getBody()
                             .front()
                             .getOps<protocol_ir::ParticipantOp>()
                             .begin();
        auto &body = endpoint->getRegion(0).front();
        builder.setInsertionPoint(&body.back());
        auto branch = local::LocalIfOp::create(
            builder, endpoint.getLoc(), TypeRange{},
            ValueRange{body.getArgument(0)}, "misplaced");
        for (auto &region : branch->getRegions()) {
          auto *block = builder.createBlock(&region);
          builder.setInsertionPointToEnd(block);
          local::LocalYieldOp::create(builder, branch.getLoc(), ValueRange{});
        }
        require(succeeded(mlir::verify(branch)),
                "isolated Local frame failed standalone operation "
                "verification");
        expected = "local-control-shape";
      } else {
        builder.setInsertionPointToEnd(&owner.getBody().front());
        auto standard = func::FuncOp::create(
            builder, owner.getLoc(), "misplaced",
            builder.getFunctionType(TypeRange{}, TypeRange{}));
        builder.setInsertionPointToEnd(standard.addEntryBlock());
        func::ReturnOp::create(builder, standard.getLoc());
        expected = "interactive-top-operation";
      }
      ScopedDiagnosticHandler silence(&context,
                                      [](Diagnostic &) { return success(); });
      require(failed(mlir::verify(*program)),
              "whole-program verification weakened vocabulary placement");
      refuses(protocol::readExecutionModel(*program), expected);
    });

  cases.run(
      "independently authored SCF is consumed into independently authored "
      "Local",
      [&] {
        auto scheduled = authored(context, "authored-schedule");
        require(succeeded(mlir::verify(*scheduled)),
                "independently authored schedule failed normal verification");
        auto expected = authored(context, "authored-schedule-local");
        auto before = clone(*scheduled);
        auto expectedBefore = clone(*expected);
        auto actual = consume(*scheduled);
        require(succeeded(kernel::verifyRecipeOutput(*expected)) &&
                    succeeded(kernel::verifyScheduleLowering(*scheduled,
                                                             *expected)) &&
                    succeeded(
                        kernel::verifyScheduleLowering(*scheduled, *actual)) &&
                    same(*actual, *expected),
                "independent schedule/Local controls disagree");
        require(same(*scheduled, *before) && same(*expected, *expectedBefore),
                "consumer or reader changed independently authored input");
      });

  cases.run(
      "schedule schema inspection has an exact shared work boundary", [&] {
        auto scheduled = authored(context, "authored-schedule");
        auto before = clone(*scheduled);
        auto *start = packetStart(loop(*scheduled));
        auto *at = start;
        uint64_t ample = 100000;
        auto matched = kernel::readScheduledLoop(at, ample);
        require(succeeded(matched) && matched->has_value() && ample < 100000,
                "schema inspection did not charge actual scheduled work");
        uint64_t cost = 100000 - ample;
        uint64_t exact = cost, shortWork = cost - 1;
        at = start;
        auto boundary = kernel::readScheduledLoop(at, exact);
        require(succeeded(boundary) && boundary->has_value() && exact == 0,
                "schema exact allowance was refused");
        at = start;
        require(failed(kernel::readScheduledLoop(at, shortWork)) &&
                    at == start && same(*scheduled, *before),
                "schema capacity advanced cursor or modified the schedule");
        uint64_t empty = 0;
        auto *ordinary = &function(*scheduled).front().back();
        at = ordinary;
        auto absent = kernel::readScheduledLoop(at, empty);
        require(succeeded(absent) && !absent->has_value() && at == ordinary &&
                    empty == 0,
                "an unmatched operation confused zero allowance with failure");
        at = start;
        require(failed(kernel::readScheduledLoop(at, empty)) && at == start,
                "a real packet was inspected without allowance");
      });

  for (StringRef mutation :
       {"zero step", "two step", "signed comparison",
        "comparison attribute type", "loop operand arity", "lower bridge type",
        "upper bridge arity", "induction bridge type", "upper bound",
        "invariant forwarding", "escaping invariant", "state partition",
        "lexical capture", "nominal state type", "missing admission"})
    cases.run("schedule schema independently refuses " + mutation, [&] {
      auto scheduled = authored(context, "authored-schedule");
      auto expected = authored(context, "authored-schedule-local");
      auto candidate = clone(*scheduled);
      auto traversal = loop(*candidate);
      auto *start = packetStart(traversal);
      auto *at = start;
      auto valid = kernel::readScheduledLoop(at);
      require(succeeded(valid) && valid->has_value() &&
                  at == traversal->getNextNode() && (*valid)->states == 2 &&
                  (*valid)->lower == function(*candidate).getArgument(0) &&
                  (*valid)->upper == function(*candidate).getArgument(1),
              "schema positive control failed");
      auto *lower = traversal->getPrevNode()->getPrevNode()->getPrevNode();
      auto *upper = lower->getNextNode();
      auto &body = *traversal.getBody();
      OpBuilder builder(&context);
      if (mutation == "zero step" || mutation == "two step")
        traversal.getStep().getDefiningOp()->setAttr(
            "value",
            builder.getI64IntegerAttr(mutation == "zero step" ? 0 : 2));
      else if (mutation == "signed comparison")
        traversal->removeAttr("unsignedCmp");
      else if (mutation == "comparison attribute type")
        traversal->setAttr("unsignedCmp", builder.getBoolAttr(true));
      else if (mutation == "loop operand arity")
        traversal->setOperands(ValueRange{});
      else if (mutation == "lower bridge type")
        lower->getResult(0).setType(builder.getI32Type());
      else if (mutation == "upper bridge arity")
        upper->setOperands({upper->getOperand(0), upper->getOperand(0)});
      else if (mutation == "induction bridge type")
        body.front().getResult(0).setType(builder.getI64Type());
      else if (mutation == "upper bound")
        upper->setOperand(0, function(*candidate).getArgument(0));
      else if (mutation == "invariant forwarding")
        body.back().setOperand(2, body.getArgument(4));
      else if (mutation == "escaping invariant")
        function(*candidate)
            .front()
            .back()
            .setOperand(0, traversal.getResult(2));
      else if (mutation == "state partition")
        traversal->setAttr("state_count", builder.getI64IntegerAttr(1));
      else if (mutation == "lexical capture")
        body.front().getNextNode()->setOperand(
            1, function(*candidate).getArgument(4));
      else if (mutation == "nominal state type")
        body.getArgument(1).setType(
            algebra::FieldType::get(&context, "bn254.fr"));
      else {
        // Remove the lower admission's terminator, retaining packet adjacency.
        start->getRegion(0).front().back().erase();
      }
      at = start;
      auto unmatched = kernel::readScheduledLoop(at);
      require(succeeded(unmatched) && !unmatched->has_value() && at == start,
              "malformed packet was accepted or advanced caller cursor");
      uint64_t work = 1000000;
      require(!kernel::consumeSchedule(*candidate, work) &&
                  failed(kernel::verifyScheduleLowering(*candidate, *expected)),
              "malformed SCF packet reached executable publication");
      require(succeeded(kernel::verifyScheduleLowering(*scheduled, *expected)),
              "independent positive control was damaged");
    });

  for (StringRef mutation : {"bound", "seed order", "state order", "capture",
                             "missing body", "extra body", "nominal domain"})
    cases.run("actual SCF to Local reader rejects " + mutation, [&] {
      auto scheduled = authored(context, "authored-schedule");
      auto expected = authored(context, "authored-schedule-local");
      auto candidate = clone(*expected);
      auto target = stateLoops(*candidate).front();
      auto &body = target.getBody().front();
      auto *add = &body.front();
      OpBuilder builder(&context);
      if (mutation == "bound")
        target->setOperand(1, target->getOperand(0));
      else if (mutation == "seed order") {
        auto first = target->getOperand(2);
        target->setOperand(2, target->getOperand(3));
        target->setOperand(3, first);
      } else if (mutation == "state order")
        body.back().setOperand(0, body.getArgument(1));
      else if (mutation == "capture") {
        auto first = target->getOperand(4);
        target->setOperand(4, target->getOperand(5));
        target->setOperand(5, first);
      } else if (mutation == "missing body") {
        add->getResult(0).replaceAllUsesWith(body.getArgument(1));
        add->erase();
      } else if (mutation == "extra body") {
        builder.setInsertionPoint(add);
        builder.clone(*add)->setAttr("site", builder.getStringAttr("extra"));
      } else {
        auto binding = SymbolTable(kernelRecipeOutput(*candidate))
                           .lookup<local::OperationBindingOp>("add");
        binding->setAttr("arguments", builder.getStrArrayAttr({"bn254.fr"}));
      }
      if (mutation != "nominal domain")
        require(succeeded(kernel::verifyRecipeOutput(*candidate)),
                "Local semantic mutation must remain an admitted fragment");
      require(failed(kernel::verifyScheduleLowering(*scheduled, *candidate)),
              "schedule/Local mismatch was accepted");
      require(succeeded(kernel::verifyScheduleLowering(*scheduled, *expected)),
              "unmodified Local control failed");
    });

  for (StringRef name : {"elements", "indices"}) {
    cases.run(name + " original source to actual SCF to actual Local", [&] {
      auto unit = source(context, name);
      OwningOpRef<mlir::ModuleOp> sourceBefore(
          cast<mlir::ModuleOp>((*unit)->clone()));
      auto local = realize(*unit);
      auto localBefore = clone(*local);
      auto scheduled = schedule(*local);
      auto scheduleBefore = clone(*scheduled);
      require(operations(*scheduled, "scf.for").size() == 1,
              "producer did not expose an actual SCF traversal");
      scheduleAccepts(*unit, *scheduled);
      auto actual = consume(*scheduled);
      require(succeeded(kernel::verifyScheduleLowering(*scheduled, *actual)),
              "actual schedule and actual consumer output differ");
      accepts(*unit, *actual);
      require(same(*unit, *sourceBefore) && same(*local, *localBefore) &&
                  same(*scheduled, *scheduleBefore),
              "scheduled preservation mutated an input");
      scheduleMismatch(*unit, *scheduled, ordered);
      auto orderedLocal = realize(*unit, ordered);
      auto orderedSchedule = schedule(*orderedLocal);
      scheduleAccepts(*unit, *orderedSchedule, ordered);
    });

    for (StringRef mutation : {"producer formula", "consumer formula", "bound",
                               "seed order", "capture", "missing body",
                               "extra body", "result order", "entry results"})
      cases.run(
          name + " original source rejects changed actual SCF: " + mutation,
          [&] {
            auto unit = source(context, name);
            auto local = realize(*unit);
            auto scheduled = schedule(*local);
            auto changed = clone(*scheduled);
            auto traversal = loop(*changed);
            auto &body = *traversal.getBody();
            auto multiply =
                operations(traversal, "algebra.exec.field_multiply");
            OpBuilder builder(&context);
            if (mutation == "producer formula")
              multiply[1]->setOperand(1, multiply[1]->getOperand(0));
            else if (mutation == "consumer formula") {
              auto subtract =
                  operations(traversal, "algebra.exec.field_subtract");
              require(subtract.size() == 1, "missing consumer transition");
              subtract.front()->setOperand(1, subtract.front()->getOperand(0));
            } else if (mutation == "bound") {
              auto *start = packetStart(traversal);
              auto *upperAdmission = start->getNextNode();
              auto *lowerBridge = upperAdmission->getNextNode();
              auto *upperBridge = lowerBridge->getNextNode();
              auto lowerBound = lowerBridge->getOperand(0);
              upperAdmission->setOperands({lowerBound, lowerBound});
              upperBridge->setOperand(0, lowerBound);
            } else if (mutation == "seed order") {
              auto first = traversal->getOperand(3);
              traversal->setOperand(3, traversal->getOperand(4));
              traversal->setOperand(4, first);
            } else if (mutation == "capture") {
              auto args = function(*changed).getArguments();
              bool found = false;
              for (unsigned i = 5; i < traversal->getNumOperands(); ++i)
                if (traversal->getOperand(i) == args[1]) {
                  traversal->setOperand(i, args[2]);
                  found = true;
                } else if (traversal->getOperand(i) == args[2])
                  traversal->setOperand(i, args[1]);
              require(found, "schedule capture mutation did not apply");
            } else if (mutation == "missing body") {
              require(multiply.front()->use_empty(),
                      "missing dead callback work");
              multiply.front()->erase();
            } else if (mutation == "extra body") {
              builder.setInsertionPoint(multiply.front());
              auto *extra = builder.clone(*multiply.front());
              extra->setAttr("site", builder.getStringAttr(
                                         multiply.front()
                                             ->getAttrOfType<StringAttr>("site")
                                             .str() +
                                         "_extra"));
            } else if (mutation == "entry results") {
              auto &returned = function(*changed).front().back();
              returned.setOperand(0, returned.getOperand(1));
            } else {
              auto first = body.back().getOperand(0);
              body.back().setOperand(0, body.back().getOperand(1));
              body.back().setOperand(1, first);
            }
            // These preserve the schedule schema. The source checker must
            // reject the actual changed transition, even though its consumer is
            // correct.
            auto actual = consume(*changed);
            require(
                succeeded(kernel::verifyScheduleLowering(*changed, *actual)),
                "changed SCF positive consumer control failed");
            scheduleMismatch(*unit, *changed);
            mismatch(*unit, *actual);
            scheduleAccepts(*unit, *scheduled);
          });
  }
  for (auto policy : {ordered, fused})
    cases.run(
        policy.collectFoldFusion ? "required fused schedule reader capacity"
                                 : "required ordered schedule reader capacity",
        [&] {
          auto unit = source(context, "elements");
          auto local = realize(*unit, policy);
          auto scheduled = schedule(*local);
          finite::VerificationResult outcome{
              finite::VerificationStatus::Verified, {}};
          require(failed(kernel::verifyEntrySchedule(*unit, *scheduled,
                                                     "collect_fold", policy,
                                                     {0, 100000}, &outcome)) &&
                      outcome.status ==
                          finite::VerificationStatus::RequiredCapacity,
                  "required schedule capacity was misclassified");
          scheduleAccepts(*unit, *scheduled, policy);
        });
  cases.run(
      "producer and consumer copying exhaust without mutating inputs", [&] {
        auto scheduled = authored(context, "authored-schedule");
        auto local = authored(context, "authored-schedule-local");
        auto before = clone(*scheduled), localBefore = clone(*local);
        uint64_t none = 0;
        require(!kernel::scheduleEntry(*local, none) && none == 0 &&
                    !kernel::consumeSchedule(*scheduled, none) && none == 0 &&
                    same(*scheduled, *before) && same(*local, *localBefore),
                "copy capacity published output or mutated source");
      });
  return cases.result();
}
