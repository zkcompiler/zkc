#include "../lib/Transforms/Computation/Support.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/IR/AlgebraTypes.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Computation.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
OwningOpRef<ModuleOp> fixture(MLIRContext &context, StringRef name) {
  auto bytes = MemoryBuffer::getFile(std::string(ZKC_CONTROL_FIXTURES) + "/" +
                                     name.str() + ".mlir");
  require(bool(bytes), "cannot read selected Math fixture");
  auto result = parseSourceString<ModuleOp>((*bytes)->getBuffer(), &context);
  require(bool(result) && succeeded(admitStage(*result)),
          "original Math admission failed");
  return result;
}
OwningOpRef<ModuleOp> logical(ModuleOp original,
                              MathematicalSelectionPolicy policy = {}) {
  OwningOpRef<ModuleOp> result(cast<ModuleOp>(original->clone()));
  PassManager manager(original.getContext());
  manager.addPass(protocol::createProjectProtocolPass(false, policy));
  manager.addPass(protocol::createLowerMathPass(policy));
  require(succeeded(manager.run(*result)),
          "selected Math demand lowering failed");
  return result;
}
void mismatch(ModuleOp original, ModuleOp candidate) {
  require(succeeded(admitStage(candidate)),
          "mutation must remain independently admitted");
  bool diagnosed = false;
  ScopedDiagnosticHandler capture(
      candidate.getContext(), [&](Diagnostic &diagnostic) {
        diagnosed |= namesIdentifier(diagnostic.str(),
                                     "numerical-lowering-correspondence");
        return success();
      });
  require(
      failed(computation::verifyComputationRealization(original, candidate)) &&
          diagnosed,
      "actual selected candidate mutation escaped correspondence");
}
OwningOpRef<ModuleOp> admittedText(MLIRContext &context, StringRef text) {
  auto result = parseSourceString<ModuleOp>(text, &context);
  require(bool(result) && succeeded(admitStage(*result)),
          "generated Math admission failed");
  return result;
}
constexpr StringLiteral finiteDeclarations =
    R"(!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%lo:ui64,%hi:ui64):
   %d = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>
   "data.domain_yield"(%d) : (!data.domain<ui64>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(ui64,ui64)->!data.domain<ui64>} : ()->()
)";
constexpr StringLiteral finiteEntry = R"(
 "protocol.func"() ({ ^entry(%enabled:i1,%count:ui64,%value:!F):
   %zero = "data.index"() {value=0:ui64} : ()->ui64
   %total = "data.finite_fold"(%zero,%count,%value,%value,%enabled) {domain=@items,step=@outer} : (ui64,ui64,!F,!F,i1)->!F
   "protocol.return"(%total) : (!F)->()
 }) {sym_name="main",function_type=(i1,ui64,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)";
// A fold step whose body is `levels` nested selected regions. The innermost
// then-arm runs `innermost`, reading %c<levels>, %a<levels> and %x<levels>.
std::string nestedStep(StringRef name, unsigned levels, StringRef innermost) {
  std::string region = innermost.str();
  for (unsigned level = levels; level; --level) {
    auto arm = [&](StringRef label) {
      return "  ^" + label.str() + "(%c" + std::to_string(level) + ":i1,%a" +
             std::to_string(level) + ":!F,%x" + std::to_string(level) +
             ":!F):\n";
    };
    auto outer = std::to_string(level - 1);
    auto branch = "  %r" + std::to_string(level) + " = \"data.branch\"(%c" +
                  outer + ",%c" + outer + ",%a" + outer + ",%x" + outer +
                  ") ({\n" + arm("then") + region + "  }, {\n" + arm("else") +
                  "  \"data.yield\"(%a" + std::to_string(level) +
                  ") : (!F)->()\n  }) {alternatives=[\"then\",\"else\"]} : "
                  "(i1,i1,!F,!F)->!F\n";
    region = branch + (level > 1 ? "  \"data.yield\"(%r" +
                                       std::to_string(level) + ") : (!F)->()\n"
                                 : "  return %r1 : !F\n");
  }
  return " func.func private @" + name.str() +
         "(%a0:!F,%i:ui64,%lo:ui64,%hi:ui64,%x0:!F,%c0:i1)->!F {\n" + region +
         " }\n";
}
// Two fold steps, each with fewer than 64 nested selected regions, chained
// through a fold in the innermost arm of the outer step.
std::string helperChain(unsigned outer, unsigned inner) {
  auto last = std::to_string(outer);
  std::string text = finiteDeclarations.str();
  text += nestedStep("inner", inner,
                     "  \"data.yield\"(%x" + std::to_string(inner) +
                         ") : (!F)->()\n");
  text += nestedStep(
      "outer", outer,
      "  %z = \"data.index\"() {value=0:ui64} : ()->ui64\n"
      "  %n = \"data.index\"() {value=1:ui64} : ()->ui64\n"
      "  %t = \"data.finite_fold\"(%z,%n,%a" +
          last + ",%x" + last + ",%c" + last +
          ") {domain=@items,step=@inner} : (ui64,ui64,!F,!F,i1)->!F\n"
          "  \"data.yield\"(%t) : (!F)->()\n");
  return text + finiteEntry.str();
}
// A fold step with a primitive in the helper body and a selected region whose
// arms have no instructions of their own.
std::string helperSites() {
  std::string text = finiteDeclarations.str();
  text +=
      R"( func.func private @outer(%state:!F,%i:ui64,%lo:ui64,%hi:ui64,%value:!F,%enabled:i1)->!F {
   %sum = algebra.field_add %state,%value : (!F,!F)->!F
   %result = "data.branch"(%enabled,%state,%sum) ({
   ^then(%acc:!F,%x:!F):
     "data.yield"(%x) : (!F)->()
   }, {
   ^else(%acc:!F,%x:!F):
     "data.yield"(%acc) : (!F)->()
   }) {alternatives=["then","else"]} : (i1,!F,!F)->!F
   return %result : !F
 }
)";
  return text + finiteEntry.str();
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("malformed dormant arm is checked before selection", [&] {
    auto original = fixture(context, "math");
    bool changed = false;
    original->walk([&](data::BranchOp branch) {
      if (!changed) {
        OpBuilder builder(branch);
        auto selector =
            arith::ConstantIntOp::create(builder, branch.getLoc(), 0, 1);
        branch->setOperand(0, selector);
        branch.getArms()[0].front().back().eraseOperands(0, 1);
        changed = true;
      }
    });
    bool diagnosed = false;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      diagnosed |= namesIdentifier(diagnostic.str(), "selected-control-shape");
      return success();
    });
    require(changed && failed(admitStage(*original)) && diagnosed,
            "malformed dormant arm was not independently refused");
  });
  for (StringRef name : {"math", "math-match", "math-nested", "math-finite",
                         "math-allocation", "math-demand"})
    for (bool batching : {false, true})
      for (bool bulk : {false, true})
        cases.run(
            name + " batching=" + Twine(batching) + " bulk=" + Twine(bulk),
            [&] {
              auto original = fixture(context, name);
              MathematicalSelectionPolicy policy;
              policy.calculationBatching = batching;
              policy.finiteBulk = bulk;
              auto source = logical(*original, policy);
              auto candidate =
                  computation::proposeComputationRealization(*source, policy);
              require(bool(candidate), "selected recipe proposal failed");
              require(succeeded(computation::verifyComputationRealization(
                          *source, *candidate, policy)),
                      "independent selected recipe reader refused actual "
                      "candidate");
            });
  cases.run("selected finite callbacks retain all invocation policy flags",
            [&] {
              auto original = fixture(context, "math-finite");
              MathematicalSelectionPolicy policy;
              policy.vectorReductionFusion = true;
              policy.collectFoldFusion = true;
              policy.calculationBatching = false;
              policy.numericalExpressions = NumericalExpressionMode::VectorOnly;
              auto source = logical(*original, policy);
              auto candidate =
                  computation::proposeComputationRealization(*source, policy);
              require(bool(candidate) &&
                          succeeded(computation::verifyComputationRealization(
                              *source, *candidate, policy)),
                      "selected callback changed invocation policy");
            });
  cases.run("selected reader counts each nested branch once", [&] {
    auto original = fixture(context, "math");
    data::BranchOp current;
    original->walk([&](data::BranchOp branch) {
      current = branch;
      return WalkResult::interrupt();
    });
    require(bool(current), "missing nested branch root");
    OpBuilder builder(&context);
    auto location = current.getLoc();
    current->insertOperands(1, current->getOperand(0));
    for (Region &arm : current.getArms())
      arm.front().insertArgument(0u, builder.getI1Type(), location);
    for (unsigned depth = 1; depth < 40; ++depth) {
      auto &arm = current.getArms()[0].front();
      auto *yield = &arm.back();
      builder.setInsertionPoint(yield);
      SmallVector<Value> inputs{arm.getArgument(0), arm.getArgument(0),
                                arm.getArgument(1), arm.getArgument(2)};
      auto nested =
          data::BranchOp::create(builder, location, current.getResultTypes(),
                                 inputs, current.getAlternatives(), 2);
      for (auto [index, region] : enumerate(nested.getArms())) {
        auto *block = new Block;
        region.push_back(block);
        block->addArguments(arm.getArgumentTypes(),
                            SmallVector<Location>(3, location));
        builder.setInsertionPointToEnd(block);
        data::YieldOp::create(builder, location,
                              block->getArgument(index ? 2 : 1));
      }
      yield->setOperand(0, nested.getResult(0));
      current = nested;
    }
    require(succeeded(admitStage(*original)), "deep selected original refused");
    auto source = logical(*original);
    auto candidate = computation::proposeComputationRealization(*source);
    require(bool(candidate) &&
                succeeded(computation::verifyComputationRealization(
                    *source, *candidate)),
            "deep selected recipe reader refused");
  });
  cases.run("selected captures preserve exact SSA aliases", [&] {
    auto original = fixture(context, "math");
    original->walk([&](func::CallOp call) {
      if (call.getCallee() == "choose")
        call->setOperand(2, call.getOperand(1));
    });
    require(succeeded(admitStage(*original)),
            "aliased original admission failed");
    auto source = logical(*original);
    auto candidate = computation::proposeComputationRealization(*source);
    require(bool(candidate) &&
                succeeded(computation::verifyComputationRealization(
                    *source, *candidate)),
            "selected capture alias correspondence refused");
  });
  cases.run(
      "independently admitted candidate rejects reordered typed captures", [&] {
        auto original = fixture(context, "math-nested");
        auto source = logical(*original);
        auto candidate = computation::proposeComputationRealization(*source);
        require(bool(candidate), "missing typed-capture candidate");
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
        auto closure = take(protocol::readSourceExecutionClosure(unit));
        llvm::StringSet<> helpers;
        for (const auto &[name, body] : closure.bodies)
          for (const auto &step : body)
            if (isa<exec::TestOp>(step.operation) && step.inputs.size() == 5)
              for (auto function : step.regions) {
                require(function.getNumArguments() == 5,
                        "unexpected typed capture width");
                auto first = function.getArgument(1),
                     second = function.getArgument(2);
                require(first.getType() != second.getType(),
                        "typed captures must differ");
                SmallVector<OpOperand *> firstUses, secondUses;
                for (auto &use : first.getUses())
                  firstUses.push_back(&use);
                for (auto &use : second.getUses())
                  secondUses.push_back(&use);
                SmallVector<Type> inputs(function.getArgumentTypes());
                std::swap(inputs[1], inputs[2]);
                first.setType(inputs[1]);
                second.setType(inputs[2]);
                for (auto *use : firstUses)
                  use->set(second);
                for (auto *use : secondUses)
                  use->set(first);
                function.setFunctionType(FunctionType::get(
                    &context, inputs, function.getResultTypes()));
                helpers.insert(function.getSymName());
              }
        require(helpers.size() == 2,
                "missing actual selected typed-capture helpers");
        candidate->walk([&](runtime::EnterScopeOp enter) {
          if (enter.getKind() == "conditional" &&
              enter.getInputs().size() == 4) {
            auto first = enter.getInputs()[0];
            enter->setOperand(1, enter.getInputs()[1]);
            enter->setOperand(2, first);
          }
        });
        candidate->walk([&](func::CallOp call) {
          if (helpers.contains(call.getCallee())) {
            auto first = call.getOperand(1);
            call->setOperand(1, call.getOperand(2));
            call->setOperand(2, first);
          }
        });
        mismatch(*source, *candidate);
      });
  for (StringRef mutation : {"capture", "selector", "operand", "yield", "site"})
    cases.run(
        "independently admitted actual candidate rejects " + mutation, [&] {
          auto original = fixture(context, "math-nested");
          auto source = logical(*original);
          auto candidate = computation::proposeComputationRealization(*source);
          require(bool(candidate), "missing selected candidate");
          bool changed = false;
          if (mutation == "capture") {
            // Permute both conditional invocations, preserving their common ABI
            // and the candidate's own closed-arm admission.
            auto unit = cast<protocol_ir::ProtocolModuleOp>(
                candidate->getBody()->front());
            auto closure = take(protocol::readSourceExecutionClosure(unit));
            llvm::StringSet<> conditionalHelpers;
            for (const auto &[name, body] : closure.bodies)
              for (const auto &step : body)
                if (isa<exec::TestOp>(step.operation))
                  for (auto function : step.regions)
                    conditionalHelpers.insert(function.getSymName());
            candidate->walk([&](runtime::EnterScopeOp enter) {
              if (enter.getKind() == "conditional" &&
                  enter.getInputs().size() == 2 &&
                  enter.getInputs()[0].getType() ==
                      enter.getInputs()[1].getType()) {
                auto left = enter.getInputs()[0];
                enter->setOperand(1, enter.getInputs()[1]);
                enter->setOperand(2, left);
              }
            });
            candidate->walk([&](func::CallOp call) {
              if (conditionalHelpers.contains(call.getCallee()) &&
                  call.getNumOperands() == 3 &&
                  call.getOperand(1).getType() ==
                      call.getOperand(2).getType()) {
                auto left = call.getOperand(1);
                call->setOperand(1, call.getOperand(2));
                call->setOperand(2, left);
                changed = true;
              }
            });
          } else if (mutation == "selector") {
            candidate->walk([&](exec::TestOp test) {
              auto function = test->getParentOfType<func::FuncOp>();
              if (!changed)
                for (Value argument : function.getArguments())
                  if (argument.getType().isSignlessInteger(1) &&
                      argument != test.getCondition()) {
                    test->setOperand(1, argument);
                    changed = true;
                    break;
                  }
            });
          } else if (mutation == "operand") {
            candidate->walk([&](exec::ApplyOp op) {
              if (!changed && op.getInputs().size() == 2 &&
                  op.getInputs()[0].getType() == op.getInputs()[1].getType()) {
                op->setOperand(2, op.getInputs()[0]);
                changed = true;
              }
            });
          } else if (mutation == "yield") {
            candidate->walk([&](exec::CompleteOp op) {
              auto function = op->getParentOfType<func::FuncOp>();
              if (!changed && op->getNumOperands() == 2 &&
                  function.getNumArguments() == 3 &&
                  op->getOperand(1).getType() ==
                      function.getArgument(1).getType()) {
                op->setOperand(1, function.getArgument(1));
                changed = true;
              }
            });
          } else {
            candidate->walk([&](exec::ApplyOp op) {
              if (!changed) {
                auto site = op.getSite().str() + "_mutated";
                op.setSite(site);
                changed = true;
              }
            });
          }
          require(changed, "mutation did not find actual selected instruction");
          mismatch(*source, *candidate);
        });
  // The finite reader issues the occurrence of every helper operation. A
  // candidate cannot rename one within the finite occurrence namespace.
  for (StringRef mutation : {"selected region", "primitive"})
    cases.run("helper " + mutation + " occurrence is derived, not read", [&] {
      auto original = admittedText(context, helperSites());
      auto source = logical(*original);
      auto candidate = computation::proposeComputationRealization(*source);
      require(bool(candidate) &&
                  succeeded(computation::verifyComputationRealization(
                      *source, *candidate)),
              "helper occurrence positive control refused");
      Operation *target = nullptr;
      if (mutation == "selected region") {
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
        auto closure = take(protocol::readSourceExecutionClosure(unit));
        for (const auto &[name, body] : closure.bodies)
          for (const auto &step : body)
            if (isa<exec::TestOp>(step.operation) && step.outputs.size() == 1 &&
                isa<algebra::FieldType>(step.outputs.front().getType()))
              target = step.operation;
      } else
        candidate->walk([&](exec::ApplyOp op) {
          auto binding =
              SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                  op, op.getBindingAttr());
          if (binding && binding.getContract() == "field.add")
            target = op;
        });
      require(target, "helper occurrence fixture lost its instruction");
      // Rename the occurrence consistently, including the scope entries of a
      // selected region, so that the candidate remains admitted.
      auto site = target->getAttrOfType<StringAttr>("site");
      auto renamed = StringAttr::get(&context, site.getValue() + "_mutated");
      candidate->walk([&](Operation *op) {
        if (op->getAttr("site") == site)
          op->setAttr("site", renamed);
      });
      mismatch(*source, *candidate);
    });
  cases.run("selected nesting is cumulative across helper crossings", [&] {
    auto within = admittedText(context, helperChain(20, 20));
    auto source = logical(*within);
    auto candidate = computation::proposeComputationRealization(*source);
    require(bool(candidate) &&
                succeeded(computation::verifyComputationRealization(
                    *source, *candidate)),
            "chained helpers within the nesting bound refused");
    // Each step stays below 64 levels; together they exceed it.
    auto deep = admittedText(context, helperChain(40, 40));
    auto deepSource = logical(*deep);
    ScopedDiagnosticHandler silence(&context,
                                    [](Diagnostic &) { return success(); });
    auto deepCandidate =
        computation::proposeComputationRealization(*deepSource);
    require(!deepCandidate || failed(computation::verifyComputationRealization(
                                  *deepSource, *deepCandidate)),
            "chained helpers exceeded the selected nesting bound");
  });
  return cases.result();
}
