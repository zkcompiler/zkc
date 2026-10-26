#include "../lib/Transforms/Kernel/FrontierVerification.h"
#include "../lib/Transforms/Kernel/Support.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
OwningOpRef<mlir::ModuleOp> fixture(MLIRContext &context, StringRef name) {
  // These direct reader fixtures intentionally omit the full retained source
  // interface record. Full admission is exercised by the projected integration
  // cases; these tests isolate the independent frontier reader.
  auto module = parseSourceFile<mlir::ModuleOp>(
      (Twine(ZKC_FRONTIER_FIXTURES) + "/" + name).str(),
      ParserConfig(&context, false));
  require(bool(module), "frontier fixture did not parse");
  return module;
}
protocol_ir::ProtocolModuleOp owner(mlir::ModuleOp module) {
  return cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
}
func::FuncOp entry(mlir::ModuleOp module, StringRef name) {
  auto unit = SymbolTable(owner(module)).lookup<mlir::ModuleOp>(name);
  require(bool(unit), "missing fixture unit");
  auto result = mathematical::getComputationEntry(unit);
  require(bool(result), "missing fixture entry");
  return result;
}
func::FuncOp wrapper(mlir::ModuleOp module, StringRef name) {
  auto result = SymbolTable(owner(module)).lookup<func::FuncOp>(name);
  require(bool(result), "missing fixture wrapper");
  return result;
}
exec::ComputeOp inner(mlir::ModuleOp module, StringRef name) {
  return cast<exec::ComputeOp>(wrapper(module, name).getBody().front().front());
}
protocol_ir::LocalCallOp invocation(mlir::ModuleOp module, StringRef name) {
  protocol_ir::LocalCallOp result;
  owner(module).walk([&](protocol_ir::ParticipantOp participant) {
    participant.walk([&](protocol_ir::LocalCallOp call) {
      if (call.getCallee() == name)
        result = call;
    });
  });
  require(bool(result), "missing fixture invocation");
  return result;
}
exec::ReturnOp returned(mlir::ModuleOp module, StringRef name) {
  exec::ReturnOp result;
  wrapper(module, name).walk([&](exec::ReturnOp op) {
    require(!result, "fixture has multiple success returns");
    result = op;
  });
  require(bool(result), "fixture has no success return");
  return result;
}
Value payload(exec::ComputeOp call, unsigned index) {
  require(call.getOutcome().hasOneUse(),
          "fixture computation is not dispatched");
  auto dispatch = cast<exec::DispatchOp>(*call.getOutcome().getUsers().begin());
  return dispatch.getReturned()->getArgument(index);
}
void changeGuard(func::FuncOp function) {
  exec::TestOp test;
  function.walk([&](exec::TestOp op) { test = op; });
  require(bool(test), "fixture guard missing");
  test->setOperand(1, function.getArgument(4));
}
SmallVector<Operation *> subtracts(func::FuncOp function) {
  SmallVector<Operation *> result;
  for (auto &op : function.front())
    if (op.getName().getStringRef() == "algebra.field_subtract")
      result.push_back(&op);
  return result;
}
SmallVector<kernel::FrontierNormalizationOrigin>
origins(mlir::ModuleOp before) {
  // Explicit test evidence: the first two first-entry instructions and first
  // second-entry instruction stand for independently checked polynomial work.
  // Every other operation is concrete, even though none has a site attribute.
  auto first = entry(before, "first_unit");
  auto second = entry(before, "second_unit");
  return {
      {first, {&first.front().front(), first.front().front().getNextNode()}},
      {second, {&second.front().front()}}};
}
void accepts(mlir::ModuleOp before, mlir::ModuleOp after) {
  uint64_t remaining = 100000;
  require(succeeded(kernel::verifyKernelFrontier(before, after, origins(before),
                                                 remaining)),
          "valid frontier rejected");
}
void forwardingReturns(mlir::ModuleOp module) {
  auto first = wrapper(module, "first");
  auto result = returned(module, "first");
  result.setOperand(0, first.getArgument(1));
  result.setOperand(2, result.getOperand(1));
  auto second = wrapper(module, "second");
  result = returned(module, "second");
  result.setOperand(0, second.getArgument(1));
  result.setOperand(2, second.getArgument(1));
  // The earlier forwarded result aliases the participant input. Later
  // generated work must retain that identity when it imports the result.
  invocation(module, "second")
      ->setOperand(0, invocation(module, "first").getResult(0));
}
void appendReturn(mlir::ModuleOp module, StringRef name, Value value) {
  auto function = wrapper(module, name);
  auto result = returned(module, name);
  result->insertOperands(result.getNumOperands(), value);
  auto call = invocation(module, name);
  SmallVector<Type> types(call.getResultTypes());
  types.push_back(value.getType());
  auto outcome = exec::OutcomeType::get(module.getContext(), types);
  function.walk([&](Operation *op) {
    if (isa<exec::ReturnOp, exec::FailureOp>(op))
      op->getResult(0).setType(outcome);
  });
  OpBuilder builder(call);
  function.setFunctionType(
      builder.getFunctionType(function.getArgumentTypes(), outcome));
  OperationState state(call.getLoc(),
                       protocol_ir::LocalCallOp::getOperationName());
  state.addOperands(call.getInputs());
  state.addTypes(types);
  state.addAttributes(call->getAttrs());
  auto replacement = cast<protocol_ir::LocalCallOp>(builder.create(state));
  call->replaceAllUsesWith(
      replacement.getResults().take_front(call.getNumResults()));
  call.erase();
}

void rejects(mlir::ModuleOp candidate,
             llvm::function_ref<LogicalResult()> check) {
  bool identifier = false;
  ScopedDiagnosticHandler handler(
      candidate.getContext(), [&](Diagnostic &diagnostic) {
        identifier |= diagnostic.str().find("kernel-frontier-correspondence") !=
                      std::string::npos;
        return success();
      });
  require(failed(check()), "mutated frontier accepted");
  require(identifier, "frontier refusal lost diagnostic identifier");
}
kernel::KernelNormalizationRewrite rewrite(mlir::ModuleOp source,
                                           mlir::ModuleOp candidate) {
  auto sourceCall = inner(source, "second");
  auto call = inner(candidate, "second");
  auto unit = cast<mlir::ModuleOp>(
      entry(candidate, "second_unit")->getParentOp()->clone());
  Builder builder(candidate.getContext());
  unit->setAttr("sym_name", builder.getStringAttr("normalized_unit"));
  owner(candidate).getBody().front().push_back(unit);
  call.setCalleeAttr(SymbolRefAttr::get(
      candidate.getContext(), "normalized_unit",
      {FlatSymbolRefAttr::get(candidate.getContext(), "evaluate")}));
  return {sourceCall, call, unit};
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  auto cfgFixture = [&] {
    auto result =
        parseSourceString<mlir::ModuleOp>(R"mlir(
      module {
        "protocol.module"() ({
          func.func private @branch(%condition: i1, %x: i64, %y: i64) -> i64 {
            cf.cond_br %condition, ^left(%x : i64), ^right(%y : i64)
          ^join(%result: i64):
            return %result : i64
          ^left(%a: i64):
            cf.br ^join(%a : i64)
          ^right(%b: i64):
            cf.br ^join(%b : i64)
          }
          func.func private @definition_order(%x: i64, %y: i64) -> i64 {
            cf.br ^definition
          ^use:
            return %sum : i64
          ^definition:
            %sum = arith.addi %x, %y : i64
            cf.br ^use
          }
        }) {profile = #protocol.profile<exec>} : () -> ()
      }
    )mlir",
                                          ParserConfig(&context, false));
    require(bool(result), "CFG context fixture did not parse");
    // This is a structural-checker fixture, not a protocol admission fixture.
    for (auto function :
         owner(*result).getBody().front().getOps<func::FuncOp>())
      require(succeeded(verify(function)), "CFG fixture is not valid SSA");
    return result;
  };
  cases.run("normalization preserves full CFG and non-dominance block order",
            [&] {
              auto before = cfgFixture(), after = cfgFixture();
              uint64_t remaining = 100000;
              require(succeeded(kernel::verifyKernelNormalizationContext(
                          *before, *after, {}, remaining)),
                      "unchanged CFG context rejected");
            });
  for (unsigned mutation = 0; mutation != 4; ++mutation)
    cases.run(
        "normalization refuses CFG mutation " + std::to_string(mutation), [&] {
          auto before = cfgFixture(), after = cfgFixture();
          auto branch =
              SymbolTable(owner(*after)).lookup<func::FuncOp>("branch");
          auto condition = cast<cf::CondBranchOp>(branch.front().back());
          if (mutation == 0)
            condition->setSuccessor(condition.getFalseDest(), 0);
          else if (mutation == 1)
            condition->setOperand(1, branch.getArgument(2));
          else if (mutation == 2) {
            auto function = SymbolTable(owner(*after))
                                .lookup<func::FuncOp>("definition_order");
            function.back().front().setOperand(0, function.getArgument(1));
          } else {
            auto &left = *std::next(branch.begin(), 2);
            left.back().setOperand(0, branch.getArgument(2));
          }
          for (auto function :
               owner(*after).getBody().front().getOps<func::FuncOp>())
            require(succeeded(verify(function)),
                    "CFG mutation must remain valid SSA");
          uint64_t remaining = 100000;
          rejects(*after, [&] {
            return kernel::verifyKernelNormalizationContext(*before, *after, {},
                                                            remaining);
          });
        });
  for (StringRef name :
       {"frontier-before.mlir", "frontier-after.mlir",
        "frontier-pack-before.mlir", "frontier-pack-after.mlir"})
    cases.run("scoped source closure admission: " + name, [&] {
      auto source = fixture(context, name);
      for (auto function :
           owner(*source).getBody().front().getOps<func::FuncOp>())
        require(succeeded(verify(function)), "scoped fixture has invalid SSA");
      if (auto error = protocol::verifySourceExecutionClosure(owner(*source)))
        throw std::runtime_error(llvm::toString(std::move(error)));
    });
  for (bool batching : {false, true})
    cases.run(
        "projected shared coefficients cross a scoped guard, batching=" +
            Twine(batching),
        [&] {
          auto source = fixture(context, "shared-polynomial.mlir");
          MathematicalSelectionPolicy policy;
          policy.calculationBatching = batching;
          PassManager projection(&context);
          projection.addPass(protocol::createProjectProtocolPass(false));
          projection.addPass(protocol::createLowerMathPass(policy));
          require(succeeded(projection.run(*source)),
                  "scoped projection failed");
          auto normalized = kernel::prepareKernelLowering(*source);
          require(bool(normalized) && succeeded(verify(*normalized)),
                  "scoped shared frontier was refused");
          unsigned imports = 0, exports = 0;
          SymbolTable original(owner(*source));
          for (auto function :
               owner(*normalized).getBody().front().getOps<func::FuncOp>()) {
            auto before = original.lookup<func::FuncOp>(function.getSymName());
            require(bool(before),
                    "frontier added an unrelated scoped function");
            auto prior = protocol::scopedDataSignature(before);
            auto actual = protocol::scopedDataSignature(function);
            if (!prior)
              continue;
            require(bool(actual), "scoped wrapper lost its data signature");
            imports += actual.getNumInputs() - prior.getNumInputs();
            exports += actual.getNumResults() - prior.getNumResults();
          }
          require(imports && exports, "shared coefficients were recomputed");
          OwningOpRef<mlir::ModuleOp> lowered(
              cast<mlir::ModuleOp>(source->clone()));
          require(succeeded(kernel::lowerKernels(*lowered, policy)) &&
                      succeeded(verify(*lowered)),
                  "scoped shared frontier realization failed");
          require(succeeded(
                      kernel::verifyKernelLowering(*source, *lowered, policy)),
                  "actual shared frontier candidate lost correspondence");
          protocol_ir::LocalCallOp consumer;
          lowered->walk([&](protocol_ir::LocalCallOp call) {
            auto before = original.lookup<func::FuncOp>(call.getCallee());
            auto signature =
                before ? protocol::scopedDataSignature(before) : FunctionType();
            if (signature && call.getNumOperands() > signature.getNumInputs())
              consumer = call;
          });
          require(bool(consumer), "actual consumer has no coefficient import");
          bool changed = false;
          for (Value input : consumer.getInputs().drop_back())
            if (input != consumer.getInputs().back() &&
                input.getType() == consumer.getInputs().back().getType()) {
              consumer->setOperand(consumer.getNumOperands() - 1, input);
              changed = true;
              break;
            }
          require(changed && succeeded(verify(*lowered)),
                  "coefficient import mutation must remain admitted");
          bool identifier = false;
          ScopedDiagnosticHandler handler(
              &context, [&](Diagnostic &diagnostic) {
                identifier |= diagnostic.str().find(
                                  "numerical-lowering-correspondence") !=
                              std::string::npos;
                return success();
              });
          require(
              failed(kernel::verifyKernelLowering(*source, *lowered, policy)),
              "wrong actual coefficient import escaped correspondence");
          require(identifier, "coefficient import refusal lost its identifier");
        });
  cases.run("identity frontier", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    accepts(*before, *after);
  });
  cases.run("actual ports and earlier same-block reuse", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    accepts(*before, *after);
  });
  auto forwarding = [&](StringRef name, bool expected,
                        llvm::function_ref<void(mlir::ModuleOp)> mutate) {
    cases.run(name, [&] {
      auto before = fixture(context, "frontier-before.mlir");
      auto after = fixture(context, "frontier-after.mlir");
      forwardingReturns(*before);
      forwardingReturns(*after);
      mutate(*after);
      if (expected)
        accepts(*before, *after);
      else {
        uint64_t remaining = 100000;
        rejects(*after, [&] {
          return kernel::verifyKernelFrontier(*before, *after, origins(*before),
                                              remaining);
        });
      }
    });
  };
  cases.run("identity with mixed forwarding and duplicate return aliases", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    forwardingReturns(*before);
    forwardingReturns(*after);
    accepts(*before, *after);
  });
  cases.run("all original wrapper results may be forwarding aliases", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    for (auto module : {before.get(), after.get()}) {
      forwardingReturns(module);
      for (StringRef name : {"first", "second"}) {
        auto function = wrapper(module, name);
        auto result = returned(module, name);
        for (unsigned i = 0; i < 3; ++i)
          result.setOperand(i, function.getArgument(1));
      }
    }
    accepts(*before, *after);
  });
  cases.run("forwarding preserves permuted inner input coordinates", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    for (auto module : {before.get(), after.get()}) {
      forwardingReturns(module);
      auto call = inner(module, "second");
      auto a = call.getInputs()[0], b = call.getInputs()[1];
      call->setOperand(1, b);
      call->setOperand(2, a);
    }
    // The generated product now reads (b, a), so its exact earlier producer
    // is the second product, even though field multiplication commutes.
    invocation(*after, "second")
        ->setOperand(4, invocation(*after, "first").getResult(4));
    accepts(*before, *after);
  });
  forwarding("forwarding aliases survive an earlier generated import", true,
             [](auto) {});
  forwarding("appended return may forward an imported generated value", true,
             [&](auto module) {
               appendReturn(module, "second",
                            wrapper(module, "second").getArgument(5));
             });
  forwarding("forwarded original argument coordinate cannot change", false,
             [&](auto module) {
               auto function = wrapper(module, "first");
               returned(module, "first").setOperand(0, function.getArgument(2));
             });
  forwarding("duplicate numerical return aliases cannot diverge", false,
             [&](auto module) {
               returned(module, "first")
                   .setOperand(2, payload(inner(module, "first"), 2));
             });
  forwarding("original forwarding cannot become a numerical return", false,
             [&](auto module) {
               returned(module, "second")
                   .setOperand(0, payload(inner(module, "second"), 0));
             });
  forwarding("generated import cannot use an unrelated forwarding alias", false,
             [&](auto module) {
               invocation(module, "second")
                   ->setOperand(4, invocation(module, "first").getResult(0));
             });
  forwarding("extra forwarding requires a checked normalization value", false,
             [&](auto module) {
               appendReturn(module, "second",
                            wrapper(module, "second").getArgument(1));
             });
  forwarding("forwarded argument must belong to the actual wrapper", false,
             [&](auto module) {
               appendReturn(module, "second",
                            wrapper(module, "first").getArgument(1));
             });
  forwarding("numerical coordinate must belong to the actual inner call", false,
             [&](auto module) {
               appendReturn(module, "second",
                            payload(inner(module, "first"), 0));
             });
  for (StringRef mutation : {"none", "arity", "premise", "presence"})
    cases.run("scoped computation policy comparison: " + mutation, [&] {
      auto before = fixture(context, "frontier-before.mlir");
      auto after = fixture(context, "frontier-after.mlir");
      Builder builder(&context);
      for (auto module : {before.get(), after.get()})
        module.walk([&](exec::ComputeOp call) {
          call.setPolicyAttr(builder.getBoolArrayAttr({true, false, false}));
        });
      auto call = inner(*after, "second");
      if (mutation == "arity")
        call.setPolicyAttr(builder.getBoolArrayAttr({}));
      else if (mutation == "premise")
        call.setPolicyAttr(builder.getBoolArrayAttr({false, false, false}));
      else if (mutation == "presence")
        call.removePolicyAttr();
      if (mutation == "none")
        accepts(*before, *after);
      else {
        uint64_t remaining = 100000;
        rejects(*after, [&] {
          return kernel::verifyKernelFrontier(*before, *after, origins(*before),
                                              remaining);
        });
      }
    });
  auto packCase = [&](StringRef name, bool expected,
                      llvm::function_ref<void(
                          mlir::ModuleOp, mlir::ModuleOp,
                          SmallVector<kernel::FrontierNormalizationOrigin> &)>
                          mutate) {
    cases.run(name, [&] {
      auto before = fixture(context, "frontier-pack-before.mlir");
      auto after = fixture(context, "frontier-pack-after.mlir");
      auto first = entry(*before, "first_unit");
      auto second = entry(*before, "second_unit");
      SmallVector<kernel::FrontierNormalizationOrigin> evidence{
          {first, {}}, {second, {&second.front().front()}}};
      mutate(*before, *after, evidence);
      uint64_t remaining = 100000;
      auto check = [&] {
        return kernel::verifyKernelFrontier(*before, *after, evidence,
                                            remaining);
      };
      if (expected)
        require(succeeded(check()), "exact packed coordinate rejected");
      else
        rejects(*after, check);
    });
  };
  packCase("exact packed scalar crosses a numerical cut", true,
           [](auto, auto, auto &) {});
  packCase("packed scalar retains exact coordinate", false,
           [&](auto, auto after, auto &) {
             auto first = entry(after, "first_unit");
             auto values = subtracts(first);
             first.front().back().setOperand(1, values.front()->getResult(0));
           });
  packCase("concrete projection cannot be erased", false,
           [](auto, auto, auto &evidence) {
             evidence.back().polynomialGenerated.clear();
           });
  packCase("packed source coordinate cannot change", false,
           [&](auto before, auto, auto &) {
             entry(before, "second_unit")
                 .front()
                 .front()
                 .setAttr("index",
                          IntegerAttr::get(IntegerType::get(&context, 64), 0));
           });
  packCase("concrete scalar producer cannot be coalesced", false,
           [&](auto, auto after, auto &) {
             auto values = subtracts(entry(after, "first_unit"));
             values.back()->getResult(0).replaceAllUsesWith(
                 values.front()->getResult(0));
             values.back()->erase();
           });
  auto negative = [&](StringRef name,
                      llvm::function_ref<void(mlir::ModuleOp)> mutate) {
    cases.run(name, [&] {
      auto before = fixture(context, "frontier-before.mlir");
      auto after = fixture(context, "frontier-after.mlir");
      mutate(*after);
      uint64_t remaining = 100000;
      rejects(*after, [&] {
        return kernel::verifyKernelFrontier(*before, *after, origins(*before),
                                            remaining);
      });
    });
  };
  negative("failure packaging must match the extended root outcome",
           [&](auto module) {
             auto function = wrapper(module, "first");
             function.walk([&](exec::FailureOp failure) {
               failure.getOutcome().setType(
                   exec::OutcomeType::get(&context, {}));
             });
           });
  negative("only selected compute success blocks may gain data arguments",
           [&](auto module) {
             auto function = wrapper(module, "first");
             function.walk([&](exec::TestOp test) {
               auto dispatch = cast<exec::DispatchOp>(
                   *test.getOutcome().getUsers().begin());
               dispatch.getReturned()->addArgument(
                   IntegerType::get(&context, 1), test.getLoc());
             });
           });
  negative("normalization cannot redirect the failure continuation",
           [&](auto module) {
             auto call = inner(module, "first");
             auto dispatch =
                 cast<exec::DispatchOp>(*call.getOutcome().getUsers().begin());
             dispatch->setSuccessor(dispatch.getReturned(), 1);
           });
  negative("permuted actual inner operands", [&](mlir::ModuleOp module) {
    auto call = inner(module, "second");
    auto a = call.getInputs()[0], b = call.getInputs()[1];
    call->setOperand(1, b);
    call->setOperand(2, a);
  });
  negative("final wrapper original return swap", [&](mlir::ModuleOp module) {
    auto result = returned(module, "second");
    auto a = result.getOperand(0), b = result.getOperand(1);
    result->setOperand(0, b);
    result->setOperand(1, a);
  });
  negative("wrong appended import from equal-valued generated output",
           [&](mlir::ModuleOp module) {
             invocation(module, "second")
                 ->setOperand(4, invocation(module, "first").getResult(4));
           });
  negative("changed inner guard condition", [&](mlir::ModuleOp module) {
    auto function = wrapper(module, "first");
    changeGuard(function);
  });
  negative("changed participant guard condition", [&](mlir::ModuleOp module) {
    auto call = invocation(module, "first");
    call->getNextNode()->setOperand(0, call->getBlock()->getArgument(3));
  });
  negative("concrete work moved across guard", [&](mlir::ModuleOp module) {
    auto first = entry(module, "first_unit"),
         second = entry(module, "second_unit");
    auto *dead = subtracts(first).back();
    IRMapping values;
    values.map(first.getArguments(),
               second.getArguments().take_front(first.getNumArguments()));
    OpBuilder builder(&second.front(), second.front().begin());
    builder.clone(*dead, values);
    dead->erase();
  });
  negative("duplicate concrete occurrence", [&](mlir::ModuleOp module) {
    auto *op = subtracts(entry(module, "first_unit")).back();
    OpBuilder builder(op);
    builder.clone(*op);
  });
  negative("erased unused concrete occurrence", [&](mlir::ModuleOp module) {
    auto *op = subtracts(entry(module, "first_unit")).back();
    require(op->use_empty(), "dead-work fixture changed");
    op->erase();
  });
  negative(
      "merged equal-valued concrete occurrences", [&](mlir::ModuleOp module) {
        auto values = subtracts(entry(module, "second_unit"));
        values[1]->getResult(0).replaceAllUsesWith(values[0]->getResult(0));
        values[1]->erase();
      });
  negative("equal-valued distinct concrete operand",
           [&](mlir::ModuleOp module) {
             auto function = entry(module, "second_unit");
             auto values = subtracts(function);
             for (auto &op : function.front())
               if (op.getName().getStringRef() == "algebra.field_add")
                 op.setOperand(1, values[1]->getResult(0));
           });
  negative("equal-valued distinct original concrete returns",
           [&](mlir::ModuleOp module) {
             auto function = entry(module, "second_unit");
             auto returned = cast<func::ReturnOp>(function.front().back());
             auto a = returned.getOperand(1), b = returned.getOperand(2);
             returned->setOperand(1, b);
             returned->setOperand(2, a);
           });
  negative("authored dormant definition changed", [&](mlir::ModuleOp module) {
    auto function = wrapper(module, "authored");
    function.front().front().setOperand(1, function.getArgument(2));
  });
  negative("participant action order changed", [&](mlir::ModuleOp module) {
    auto first = invocation(module, "first");
    first->getNextNode()->moveBefore(first);
  });
  negative(
      "concrete replay of earlier exported result", [&](mlir::ModuleOp module) {
        auto function = entry(module, "second_unit");
        OperationState state(function.getLoc(), "algebra.field_multiply");
        state.addOperands({function.getArgument(0), function.getArgument(1)});
        state.addTypes(function.getArgument(0).getType());
        OpBuilder builder(&function.front(), function.front().begin());
        auto *replay = builder.create(state);
        function.getArgument(4).replaceAllUsesWith(replay->getResult(0));
      });
  cases.run("missing site does not grant shareability", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    auto evidence = origins(*before);
    for (auto &origin : evidence)
      origin.polynomialGenerated.clear();
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelFrontier(*before, *after, evidence, remaining);
    });
  });
  cases.run("sharing cannot use a later cut", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    for (auto module : {before.get(), after.get()})
      invocation(module, "second")->moveBefore(invocation(module, "first"));
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelFrontier(*before, *after, origins(*before),
                                          remaining);
    });
  });
  cases.run("sharing cannot cross participant blocks", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    for (auto module : {before.get(), after.get()}) {
      auto call = invocation(module, "second");
      auto *finish = call->getNextNode();
      auto *block = new Block();
      call->getParentRegion()->push_back(block);
      for (auto argument : call->getBlock()->getArguments())
        block->addArgument(argument.getType(), argument.getLoc());
      call->moveBefore(block, block->end());
      finish->moveBefore(block, block->end());
      for (unsigned i = 0; i < 4; ++i)
        call->setOperand(i, block->getArgument(i));
    }
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelFrontier(*before, *after, origins(*before),
                                          remaining);
    });
  });
  cases.run("exhausted comparison budget", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-after.mlir");
    uint64_t remaining = 0;
    rejects(*after, [&] {
      return kernel::verifyKernelFrontier(*before, *after, origins(*before),
                                          remaining);
    });
    require(remaining == 0, "comparison budget underflow");
  });
  cases.run("explicit normalization callee rewrite", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    auto record = rewrite(*before, *after);
    uint64_t remaining = 100000;
    require(succeeded(kernel::verifyKernelNormalizationContext(
                *before, *after, {record}, remaining)),
            "checked normalization context rejected");
  });
  cases.run("normalization cannot change guard", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    auto record = rewrite(*before, *after);
    auto function = wrapper(*after, "first");
    changeGuard(function);
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelNormalizationContext(*before, *after, {record},
                                                      remaining);
    });
  });
  cases.run("normalization retains original raw units", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    auto record = rewrite(*before, *after);
    auto function = entry(*after, "second_unit");
    function.front().front().setOperand(0, function.getArgument(1));
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelNormalizationContext(*before, *after, {record},
                                                      remaining);
    });
  });
  cases.run("unrecorded normalization rewrite", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    rewrite(*before, *after);
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelNormalizationContext(*before, *after, {},
                                                      remaining);
    });
  });
  cases.run("normalization cannot change entry declaration attributes", [&] {
    auto before = fixture(context, "frontier-before.mlir");
    auto after = fixture(context, "frontier-before.mlir");
    auto record = rewrite(*before, *after);
    mathematical::getComputationEntry(record.normalizedUnit)
        ->setAttr("changed_contract", UnitAttr::get(&context));
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelNormalizationContext(*before, *after, {record},
                                                      remaining);
    });
  });
  return cases.result();
}
