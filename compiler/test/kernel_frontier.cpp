#include "../lib/Transforms/Kernel/FrontierVerification.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "llvm/ADT/STLExtras.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
OwningOpRef<mlir::ModuleOp> fixture(MLIRContext &context, StringRef name) {
  // These direct reader fixtures intentionally omit the full retained source
  // interface record. Admission/integration is a separate lead-owned check.
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
  auto unit = SymbolTable(owner(module)).lookup<kernel::ModuleOp>(name);
  require(bool(unit), "missing fixture unit");
  auto result = kernel::getEntry(unit);
  require(bool(result), "missing fixture entry");
  return result;
}
local::FuncOp wrapper(mlir::ModuleOp module, StringRef name) {
  auto result = SymbolTable(owner(module)).lookup<local::FuncOp>(name);
  require(bool(result), "missing fixture wrapper");
  return result;
}
kernel::CallOp inner(mlir::ModuleOp module, StringRef name) {
  return cast<kernel::CallOp>(wrapper(module, name).getBody().front().front());
}
local::CallOp invocation(mlir::ModuleOp module, StringRef name) {
  local::CallOp result;
  owner(module).walk([&](protocol_ir::ParticipantOp participant) {
    participant.walk([&](local::CallOp call) {
      if (call.getCallee() == name)
        result = call;
    });
  });
  require(bool(result), "missing fixture invocation");
  return result;
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
  auto unit = cast<kernel::ModuleOp>(
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
  negative("permuted actual inner operands", [&](mlir::ModuleOp module) {
    auto call = inner(module, "second");
    auto a = call.getOperand(0), b = call.getOperand(1);
    call->setOperand(0, b);
    call->setOperand(1, a);
  });
  negative("final wrapper original return swap", [&](mlir::ModuleOp module) {
    auto returned = cast<local::ReturnOp>(
        wrapper(module, "second").getBody().front().back());
    auto a = returned.getOperand(0), b = returned.getOperand(1);
    returned->setOperand(0, b);
    returned->setOperand(1, a);
  });
  negative("wrong appended import from equal-valued generated output",
           [&](mlir::ModuleOp module) {
             invocation(module, "second")
                 ->setOperand(4, invocation(module, "first").getResult(4));
           });
  negative("changed inner guard condition", [&](mlir::ModuleOp module) {
    auto function = wrapper(module, "first");
    for (auto &op : function.getBody().front())
      if (op.getName().getStringRef() == "local.guard")
        op.setOperand(0, function.getArgument(3));
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
    function.getBody().front().front().setOperand(0, function.getArgument(1));
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
    function.getBody().front().front().getNextNode()->setOperand(
        0, function.getArgument(3));
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
    kernel::getEntry(record.normalizedUnit)
        ->setAttr("changed_contract", UnitAttr::get(&context));
    uint64_t remaining = 100000;
    rejects(*after, [&] {
      return kernel::verifyKernelNormalizationContext(*before, *after, {record},
                                                      remaining);
    });
  });
  return cases.result();
}
