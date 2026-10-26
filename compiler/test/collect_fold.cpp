#include "../lib/Transforms/CollectFold.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "support/NumericalLoops.h"
#include <utility>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::test::loops;

namespace {
FailureOr<finite::CollectFold> pair(mlir::ModuleOp unit, uint64_t &remaining) {
  auto &body = mathematical::getComputationEntry(unit).front();
  return finite::readCollectFold(&body.front(), body.front().getNextNode(),
                                 remaining);
}
void assertMaterialized(mlir::ModuleOp candidate) {
  require(stateLoops(candidate).size() >= 2 &&
              !operations(candidate, "algebra.exec.vector_append").empty(),
          "declined pair did not retain collection followed by reduction");
}
void assertFused(mlir::ModuleOp candidate) {
  auto loops = stateLoops(candidate);
  require(loops.size() == 1 && loops.front()->getNumResults() == 2 &&
              operations(candidate, "algebra.exec.vector_append").empty() &&
              operations(candidate, "algebra.exec.vector_empty").empty(),
          "eligible pair did not become one two-state streaming traversal");
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("fixed Local implementation retains ordered materialization", [&] {
    auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_LOOP_FIXTURES) +
                                             "/collect-fold-fixed.mlir");
    require(bool(bytes), "missing fixed implementation fixture");
    auto original =
        parseSourceString<mlir::ModuleOp>((*bytes)->getBuffer(), &context);
    require(bool(original), "fixed implementation fixture refused");
    auto saved = clone(*original);
    auto candidate = clone(*original);
    require(succeeded(finite::realizeLocals(*candidate, fused)) &&
                succeeded(finite::verifyRealizations(*original, *candidate)),
            "fixed implementation lost its ordinary finite path");
    auto *owner = &candidate->getBody()->front();
    auto collect = SymbolTable(owner).lookup<local::FuncOp>("collect");
    auto fold = SymbolTable(owner).lookup<local::FuncOp>("fold");
    require(collect && fold &&
                !operations(collect, "algebra.exec.vector_append").empty() &&
                !operations(fold, "local.for").empty(),
            "fixed Local collect/fold was replaced by composition");
    auto binding =
        SymbolTable(owner).lookup<local::OperationBindingOp>("multiply");
    require(binding && binding.getImplementation() == "arkworks/field.mul" &&
                same(*original, *saved),
            "fixed implementation or original source changed");
  });
  for (StringRef field : {"koala-bear", "koala-bear.ext8-binomial3"})
    for (StringRef name : {"elements", "indices"})
      cases.run(name + " composition preserves nominal " + field, [&] {
        auto unit = source(context, name, field);
        auto candidate = realize(*unit);
        assertFused(*candidate);
        accepts(*unit, *candidate);
        auto other = source(context, name);
        mismatch(*other, *candidate);
      });
  for (StringRef name : {"elements", "indices"}) {
    cases.run(name + " collection fusion is independent of finite bulk policy",
              [&] {
                auto unit = source(context, name);
                MathematicalSelectionPolicy policy{true, false, true};
                auto candidate = realize(*unit, policy);
                assertFused(*candidate);
                accepts(*unit, *candidate, policy);
              });
    for (StringRef field : {"bls12-381.fr", "koala-bear.ext8-binomial3"})
      cases.run(name + " standard Sequence composition in " + field, [&] {
        auto unit = source(context, name, field, true);
        auto candidate = realize(*unit);
        assertFused(*candidate);
        require(operations(*candidate, "data.exec.sequence_append").empty() &&
                    operations(*candidate, "data.exec.sequence_empty").empty(),
                "Sequence composition retained materialization");
        accepts(*unit, *candidate);
      });
  }
  cases.run("ordered mixed native state tuple is preserved", [&] {
    auto unit = source(context, "mixed_states");
    auto candidate = realize(*unit);
    assertFused(*candidate);
    accepts(*unit, *candidate);
    auto traversal = stateLoops(*candidate).front();
    require(traversal->getResult(0).getType().isSignlessInteger(1) &&
                isa<algebra::FieldType>(traversal->getResult(1).getType()),
            "mixed native state coordinates lost their nominal types");
  });
  cases.run("literal nonzero seeds retain exact ordered values", [&] {
    auto unit = source(context, "nonzero_seeds");
    auto candidate = realize(*unit);
    assertFused(*candidate);
    accepts(*unit, *candidate);
    auto traversal = stateLoops(*candidate).front();
    for (auto [position, literal] :
         {std::pair<unsigned, StringRef>{2, "7"}, {3, "11"}}) {
      auto *seed = traversal->getOperand(position).getDefiningOp();
      require(seed &&
                  seed->getName().getStringRef() ==
                      "algebra.exec.field_constant" &&
                  seed->getAttrOfType<ArrayAttr>("parameters") ==
                      Builder(&context).getStrArrayAttr({literal}),
              "nonzero seed value was synthesized, reordered or reset");
    }
  });
  cases.run("zero state still executes both complete callback bodies", [&] {
    auto unit = source(context, "unit_state");
    uint64_t remaining = 100000;
    require(succeeded(pair(*unit, remaining)), "zero state pair was declined");
    auto candidate = realize(*unit);
    accepts(*unit, *candidate);
    require(
        operations(*candidate, "algebra.exec.vector_append").empty() &&
            operations(*candidate, "algebra.exec.field_multiply").size() == 2 &&
            operations(*candidate, "algebra.exec.field_subtract").size() == 1,
        "zero state dropped dead callback work or retained materialization");
  });
  cases.run("unused nested strict zip check retains conditional entry", [&] {
    auto unit = source(context, "nested_checks");
    uint64_t remaining = 100000;
    require(failed(pair(*unit, remaining)),
            "nested strict admission was eligible for streaming");
    auto candidate = realize(*unit);
    assertMaterialized(*candidate);
    accepts(*unit, *candidate);
    auto checks = operations(*candidate, "local.exec.require");
    require(!checks.empty(), "unused nested zip lost its strict shape check");
    for (auto *check : checks)
      require(bool(check->getParentOfType<local::LocalForOp>()),
              "nested zip admission escaped its conditional outer traversal");
  });
  for (StringRef name : {"elements", "indices"}) {
    cases.run(
        name + " composition preserves source, states, seeds and captures",
        [&] {
          auto unit = source(context, name);
          OwningOpRef<mlir::ModuleOp> saved(
              cast<mlir::ModuleOp>((*unit)->clone()));
          uint64_t remaining = 100000;
          auto description = pair(*unit, remaining);
          require(succeeded(description) && remaining < 100000 &&
                      description->indexed == (name == "indices"),
                  "eligible original pair was not recognized");
          auto output = realize(*unit);
          assertFused(*output);
          accepts(*unit, *output);
          require(same(*unit, *saved),
                  "composition modified original callbacks");
          auto loop = stateLoops(*output).front();
          auto args = entry(*output).getArguments();
          require(loop->getOperand(2) == args[3] &&
                      loop->getOperand(3) == args[4],
                  "ordered nonzero seed inputs were replaced or interchanged");
          auto &body = loop->getRegion(0).front();
          // The first backedge is the CURRENT second state, not the entry seed.
          require(body.back().getOperand(0) == body.getArgument(2),
                  "state rotation does not use the current iteration state");
          auto disabled = realize(*unit, ordered);
          assertMaterialized(*disabled);
          accepts(*unit, *disabled, ordered);
          mismatch(*unit, *output, ordered);
          require(same(*unit, *saved),
                  "decline/check modified original source");
        });

    for (StringRef mutation :
         {"seed", "state", "capture", "operand", "missing body", "extra body",
          "return", "fixed implementation", "nominal domain"})
      cases.run(name + " actual candidate rejects " + mutation, [&] {
        auto unit = source(context, name);
        auto original = realize(*unit);
        accepts(*unit, *original);
        auto candidate = clone(*original);
        auto loop = stateLoops(*candidate).front();
        auto &body = loop->getRegion(0).front();
        auto multiply = operations(loop, "algebra.exec.field_multiply");
        require(multiply.size() >= 2, "missing independent body instructions");
        OpBuilder builder(&context);
        if (mutation == "seed") {
          auto first = loop->getOperand(2);
          loop->setOperand(2, loop->getOperand(3));
          loop->setOperand(3, first);
        } else if (mutation == "state") {
          auto first = body.back().getOperand(0);
          body.back().setOperand(0, body.back().getOperand(1));
          body.back().setOperand(1, first);
        } else if (mutation == "capture") {
          // Swap distinct field captures, retaining a valid, unique capture
          // frame while changing the callback inputs.
          auto args = entry(*candidate).getArguments();
          bool changed = false;
          for (unsigned i = 4; i < loop->getNumOperands(); ++i)
            if (loop->getOperand(i) == args[1]) {
              loop->setOperand(i, args[2]);
              changed = true;
            } else if (loop->getOperand(i) == args[2])
              loop->setOperand(i, args[1]);
          require(changed, "factor capture mutation did not apply");
        } else if (mutation == "operand") {
          multiply[1]->setOperand(1, multiply[1]->getOperand(0));
        } else if (mutation == "missing body") {
          require(multiply.front()->use_empty(), "dead body work is now live");
          multiply.front()->erase();
        } else if (mutation == "extra body") {
          builder.setInsertionPoint(multiply.front());
          auto extra = builder.clone(*multiply.front());
          extra->setAttr(
              "site",
              builder.getStringAttr(
                  multiply.front()->getAttrOfType<StringAttr>("site").str() +
                  "_extra"));
        } else if (mutation == "return") {
          auto &returned = entry(*candidate).getBody().front().back();
          returned.setOperand(0, returned.getOperand(1));
        } else {
          auto binding = primitiveBinding(multiply[1]);
          if (mutation == "fixed implementation")
            binding->setAttr("implementation",
                             builder.getStringAttr("arkworks/field.mul"));
          else
            binding->setAttr("arguments",
                             builder.getStrArrayAttr({"bn254.fr"}));
        }
        if (mutation != "nominal domain")
          require(succeeded(kernel::verifyRecipeOutput(*candidate)),
                  "semantic mutation must remain an admitted Local fragment");
        mismatch(*unit, *candidate);
        accepts(*unit, *original);
      });

    for (StringRef mutation : {"producer formula", "consumer formula",
                               "producer dead work", "consumer results"})
      cases.run(
          name + " original helper differs from actual composed output: " +
              mutation,
          [&] {
            auto unit = source(context, name);
            auto candidate = realize(*unit);
            auto changedHelper = helper(
                *unit, mutation.starts_with("producer")
                           ? "body"
                           : (name == "indices" ? "indexed_step" : "step"));
            auto &body = changedHelper.front();
            if (mutation == "producer formula")
              body.front().getNextNode()->setOperand(1, body.getArgument(0));
            else if (mutation == "consumer formula")
              body.back().setOperand(1, body.getArgument(0));
            else if (mutation == "producer dead work")
              body.front().erase();
            else
              body.back().setOperands(
                  {body.back().getOperand(1), body.back().getOperand(0)});
            require(succeeded(verify(*unit)),
                    "original helper mutation malformed");
            mismatch(*unit, *candidate);
            // Positive control: the changed original has its own valid output.
            auto ownOutput = realize(*unit);
            accepts(*unit, *ownOutput);
          });
  }

  for (StringRef reason : {"shared output", "whole vector", "captured alias",
                           "nested check", "predicate", "consumer predicate"})
    cases.run("unsupported composition declines: " + reason, [&] {
      auto unit =
          source(context, reason == "captured alias" ? "indices" : "elements");
      auto entrySource = mathematical::getComputationEntry(*unit);
      auto *producer = &entrySource.front().front();
      auto *consumer = producer->getNextNode();
      auto body = helper(*unit, "body");
      auto step =
          helper(*unit, reason == "captured alias" ? "indexed_step" : "step");
      OpBuilder builder(&context);
      if (reason == "shared output") {
        builder.setInsertionPoint(&entrySource.front().back());
        OperationState state(entrySource.getLoc(), "data.dim");
        state.addOperands(producer->getResult(0));
        state.addTypes(builder.getIntegerType(64, false));
        state.addAttribute("axis", builder.getI64IntegerAttr(0));
        builder.create(state);
      } else if (reason == "whole vector" || reason == "captured alias") {
        builder.setInsertionPoint(&step.front().back());
        OperationState state(step.getLoc(), "data.dim");
        state.addOperands(step.getArgument(reason == "captured alias" ? 5 : 3));
        state.addTypes(builder.getIntegerType(64, false));
        state.addAttribute("axis", builder.getI64IntegerAttr(0));
        builder.create(state);
      } else if (reason == "nested check") {
        builder.setInsertionPoint(&body.front().back());
        OperationState state(body.getLoc(), "algebra.finite_fold");
        state.addOperands({body.getArgument(1), body.getArgument(0),
                           body.getArgument(2), body.getArgument(2)});
        state.addTypes(
            {body.getArgument(0).getType(), body.getArgument(0).getType()});
        state.addAttribute("domain", FlatSymbolRefAttr::get(&context, "items"));
        state.addAttribute("step", FlatSymbolRefAttr::get(&context, "step"));
        builder.create(state);
      } else {
        auto prototype = reason == "predicate" ? body : step;
        builder.setInsertionPointToEnd(unit->getBody());
        auto predicate = func::FuncOp::create(
            builder, prototype.getLoc(), "select",
            builder.getFunctionType(
                reason == "predicate"
                    ? prototype.getArgumentTypes()
                    : TypeRange(
                          ValueRange(prototype.getArguments().drop_front(2))),
                builder.getI1Type()));
        predicate.setPrivate();
        builder.setInsertionPointToEnd(predicate.addEntryBlock());
        auto yes = arith::ConstantOp::create(builder, predicate.getLoc(),
                                             builder.getBoolAttr(false));
        func::ReturnOp::create(builder, predicate.getLoc(), yes.getResult());
        (reason == "predicate" ? producer : consumer)
            ->setAttr("predicate", FlatSymbolRefAttr::get(&context, "select"));
      }
      require(succeeded(verify(*unit)), "decline fixture is not admitted");
      uint64_t remaining = 100000;
      require(failed(pair(*unit, remaining)),
              "unsafe composition was selected");
      auto candidate = realize(*unit);
      assertMaterialized(*candidate);
      accepts(*unit, *candidate);
    });

  cases.run("optional discovery exhaustion retains checked materialization",
            [&] {
              auto unit = source(context, "indices");
              mathematical::RealizationWork work;
              work.collectFoldDiscovery = 0;
              auto candidate = realize(*unit, fused, {}, &work);
              assertMaterialized(*candidate);
              accepts(*unit, *candidate);
              require(work.collectFoldDiscovery == 0,
                      "optional work was replenished");
            });
  cases.run("discovery has an exact independent capacity boundary", [&] {
    auto unit = source(context, "indices");
    uint64_t ample = 100000;
    require(succeeded(pair(*unit, ample)), "ample discovery control failed");
    auto cost = 100000 - ample;
    require(cost > 1, "discovery failed to charge structural work");
    uint64_t exact = cost, shortWork = cost - 1;
    require(succeeded(pair(*unit, exact)) && exact == 0 &&
                failed(pair(*unit, shortWork)),
            "discovery boundary was not determined by actual source work");
    mathematical::RealizationWork work;
    work.collectFoldDiscovery = cost - 1;
    auto fallback = realize(*unit, fused, {}, &work);
    assertMaterialized(*fallback);
    accepts(*unit, *fallback);
    require(work.collectFoldDiscovery < cost,
            "declined discovery replenished its spent allowance");
  });
  cases.run(
      "optional comparison capacity retries original unfused source", [&] {
        auto unit = source(context, "elements");
        // This independent source variant has a supported pointwise bulk body.
        // Discovery is exhausted, so collect-fold must retain its ordered
        // reserve.
        helper(*unit, "body").front().front().erase();
        MathematicalSelectionPolicy policy{true, false, true};
        mathematical::RealizationWork bulkWork, retryWork;
        bulkWork.collectFoldDiscovery = retryWork.collectFoldDiscovery = 0;
        auto bulk = realize(*unit, policy, {}, &bulkWork);
        auto materialized = realize(*unit, ordered);
        require(!same(*bulk, *materialized),
                "bulk positive control selected no work");
        finite::VerificationResult outcome{finite::VerificationStatus::Verified,
                                           {}};
        require(
            failed(kernel::verifyEntryRecipes(*unit, *bulk, "collect_fold",
                                              policy, {100000, 1}, &outcome)) &&
                outcome.status == finite::VerificationStatus::OptionalCapacity,
            "optional comparison capacity became required refusal or mismatch");
        auto retried = realize(*unit, policy, {100000, 1}, &retryWork);
        require(same(*retried, *materialized) &&
                    retryWork.collectFoldDiscovery == 0,
                "optional retry changed source path or replenished discovery");
        accepts(*unit, *retried, policy);
        auto changed = clone(*bulk);
        auto &returned = entry(*changed).getBody().front().back();
        returned.setOperand(0, entry(*changed).getArgument(3));
        mismatch(*unit, *changed, policy);
      });
  for (auto policy : {ordered, fused})
    cases.run(policy.collectFoldFusion ? "required fused reader capacity"
                                       : "required ordered reader capacity",
              [&] {
                auto unit = source(context, "elements");
                auto candidate = realize(*unit, policy);
                finite::VerificationResult outcome{
                    finite::VerificationStatus::Verified, {}};
                require(
                    failed(kernel::verifyEntryRecipes(*unit, *candidate,
                                                      "collect_fold", policy,
                                                      {0, 100000}, &outcome)) &&
                        outcome.status ==
                            finite::VerificationStatus::RequiredCapacity,
                    "required capacity became optional fallback or mismatch");
                accepts(*unit, *candidate, policy);
              });
  return cases.result();
}
