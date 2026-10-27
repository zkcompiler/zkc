#include "../lib/Transforms/MathematicalSupport.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ScopedComputation.h"
#include "support/ScopedFinite.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/Threading.h"
#include "llvm/Support/thread.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "fixture pass failed");
}
OwningOpRef<ModuleOp> copy(ModuleOp module) {
  return OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
}
protocol_ir::ParticipantOp participant(ModuleOp module, StringRef role = "P") {
  protocol_ir::ParticipantOp result;
  module.walk([&](protocol_ir::ParticipantOp op) {
    if (op.getRole() == role)
      result = op;
  });
  return result;
}
func::FuncOp callee(protocol_ir::LocalCallOp call) {
  return SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
      call, call.getCalleeAttr());
}
constexpr StringLiteral fixture = R"mlir(module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a: i1, %b: i1, %c: i1):
    %and = arith.andi %a, %b : i1
    %or = arith.ori %a, %b : i1
    %xor = arith.xori %and, %or : i1
    %eq = arith.cmpi eq, %xor, %c : i1
    %ne = arith.cmpi ne, %eq, %c : i1
    %one = arith.constant true
    %selected = arith.select %ne, %and, %one : i1
    %same = arith.select %c, %and, %and : i1
    protocol.guard %c {owner="P", site="gate"}
    %sent = protocol.exchange %selected {sender="P", receiver="V", site="message"} : i1
    %later = arith.andi %selected, %same : i1
    protocol.guard %sent {owner="V", site="received_guard"}
    "protocol.return"(%later, %and, %or, %sent) : (i1,i1,i1,i1) -> ()
  }) {sym_name="main", function_type=(i1,i1,i1)->(i1,i1,i1,i1), roles=["P","V"],
      input_roles=[["P"],["P"],["P"]], output_roles=[["P"],["P"],["P"],["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () })mlir";
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  auto source = parseSourceString<ModuleOp>(fixture, &context);
  require(bool(source), "fixture refused");
  run(*source, protocol::createProjectProtocolPass());
  auto logical = copy(*source);
  run(*logical, protocol::createLowerMathPass());
  auto bound = copy(*logical);
  run(*bound, kernel::createLowerKernelsPass());
  Cases cases;
  cases.run("all Boolean recipes, shared demand, received guard", [&] {
    require(succeeded(mathematical::verifyMathLowering(
                cast<protocol_ir::ProtocolModuleOp>(source->getBody()->front()),
                cast<protocol_ir::ProtocolModuleOp>(
                    logical->getBody()->front()))) &&
                succeeded(kernel::verifyKernelLowering(*logical, *bound)),
            "valid lowering refused");
  });
  cases.run("equivalent pure split is a different lowering policy", [&] {
    constexpr StringLiteral text = R"mlir(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%a:i1,%b:i1):
        %t = arith.andi %a,%b : i1
        %u = arith.xori %t,%a : i1
        %r = protocol.exchange %u {sender="P",receiver="V",site="message"} : i1
        "protocol.return"(%r) : (i1)->()
      }) {sym_name="main",function_type=(i1,i1)->i1,roles=["P","V"],
          input_roles=[["P"],["P"]],output_roles=[["V"]]} : ()->()
    }) {profile=#protocol.profile<protocol>} : ()->() })mlir";
    auto original = parseSourceString<ModuleOp>(text, &context);
    require(bool(original), "split fixture");
    run(*original, protocol::createProjectProtocolPass());
    auto split = copy(*original);
    run(*split, protocol::createLowerMathPass());
    auto call = *participant(*split)
                     .getBody()
                     .front()
                     .getOps<protocol_ir::LocalCallOp>()
                     .begin();
    auto function = callee(call);
    auto invocation = cast<exec::ComputeOp>(function.getBody().front().front());
    auto entry = SymbolTable::lookupNearestSymbolFrom<func::FuncOp>(
        invocation, invocation.getCalleeAttr());
    require(bool(entry) && entry.getNumArguments() == 2 &&
                isa<arith::AndIOp>(entry.front().front()),
            "split fixture mathematical body");
    auto closure = cast<mlir::ModuleOp>(entry->getParentOp());
    OpBuilder builder(function);
    auto prefixUnit = cast<mlir::ModuleOp>(builder.clone(*closure));
    prefixUnit.setSymName("split_prefix_computation");
    auto prefixEntry = mathematical::getComputationEntry(prefixUnit);
    auto &prefixBody = prefixEntry.front();
    auto &first = prefixBody.front();
    prefixBody.back().setOperands(first.getResults());
    for (auto &operation : llvm::make_early_inc_range(prefixBody))
      if (&operation != &first && !isa<func::ReturnOp>(operation))
        operation.erase();
    auto prefix = cast<func::FuncOp>(builder.clone(*function));
    prefix.setSymName("split_prefix");
    prefix->setAttr("runtime.origin",
                    builder.getArrayAttr({builder.getStringAttr("split_prefix"),
                                          builder.getArrayAttr({})}));
    auto prefixInvocation =
        cast<exec::ComputeOp>(prefix.getBody().front().front());
    prefixInvocation.setCalleeAttr(SymbolRefAttr::get(
        SymbolTable::getSymbolName(prefixUnit),
        {FlatSymbolRefAttr::get(&context, prefixEntry.getSymName())}));
    builder.setInsertionPoint(call);
    auto prefixCall = protocol_ir::LocalCallOp::create(
        builder, call.getLoc(), call.getResultTypes(), call.getInputs(),
        prefix.getSymName(), "split_prefix", call.getRole());
    auto &andOperation = entry.front().front();
    andOperation.getResult(0).replaceAllUsesWith(entry.getArgument(1));
    andOperation.erase();
    call->setOperand(1, prefixCall.getResult(0));
    split->walk([&](protocol_ir::ProjectionOp record) {
      SmallVector<Attribute> rows(record.getCalculations().getValue());
      rows.push_back(builder.getDictionaryAttr(
          {builder.getNamedAttr(
               "participant", FlatSymbolRefAttr::get(
                                  &context, participant(*split).getSymName())),
           builder.getNamedAttr("callee", prefixCall.getCalleeAttr()),
           builder.getNamedAttr("site", prefixCall.getSiteAttr())}));
      record.setCalculationsAttr(builder.getArrayAttr(rows));
    });
    require(succeeded(verify(*split)), "split lost formation");
    bool partition = false;
    ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
      partition |=
          d.str().find("multiple calculations at one cut") != std::string::npos;
      return success();
    });
    require(
        failed(mathematical::verifyMathLowering(
            cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front()),
            cast<protocol_ir::ProtocolModuleOp>(split->getBody()->front()))) &&
            partition,
        "split escaped the closed lowering policy");
  });
  cases.run("logical computation operand mutation", [&] {
    auto candidate = copy(*logical);
    bool changed = false;
    candidate->walk([&](arith::AndIOp op) {
      if (!changed && op->getParentOfType<mlir::ModuleOp>() &&
          op.getLhs() != op.getRhs()) {
        op->setOperand(1, op.getLhs());
        changed = true;
      }
    });
    require(changed && succeeded(verify(*candidate)),
            "logical operand mutation lost formation");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(failed(mathematical::verifyMathLowering(
                cast<protocol_ir::ProtocolModuleOp>(source->getBody()->front()),
                cast<protocol_ir::ProtocolModuleOp>(
                    candidate->getBody()->front()))),
            "changed computation mathematics escaped formation correspondence");
  });
  auto mutation = [&](StringRef name, llvm::function_ref<void(ModuleOp)> change,
                      bool formed = true,
                      StringRef formationCode = "mathematical-projection") {
    cases.run(name, [&] {
      auto candidate = copy(*bound);
      change(*candidate);
      if (!formed) {
        bool code = false;
        ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
          code |=
              diagnostic.str().find(formationCode.str()) != std::string::npos;
          return success();
        });
        require(failed(verify(*candidate)) && code,
                "structural mutation escaped formation admission");
        return;
      }
      require(succeeded(verify(*candidate)),
              "mutation did not retain formation");
      bool code = false;
      ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
        code |= diagnostic.str().find("numerical-lowering-correspondence") !=
                std::string::npos;
        return success();
      });
      require(failed(kernel::verifyKernelLowering(*logical, *candidate)) &&
                  code,
              "lowering mutation escaped data-flow comparison");
    });
  };
  auto calculations = [](ModuleOp module) {
    return SmallVector<protocol_ir::LocalCallOp>(
        participant(module)
            .getBody()
            .front()
            .getOps<protocol_ir::LocalCallOp>());
  };
  mutation(
      "swapped calculation participant attribution",
      [&](ModuleOp module) {
        module.walk([&](protocol_ir::ProjectionOp record) {
          SmallVector<Attribute> items(record.getCalculations().getValue());
          NamedAttrList first(cast<DictionaryAttr>(items.front()));
          NamedAttrList last(cast<DictionaryAttr>(items.back()));
          auto owner = first.get("participant");
          require(owner != last.get("participant"),
                  "fixture needs distinct participants");
          first.set("participant", last.get("participant"));
          last.set("participant", owner);
          items.front() = first.getDictionary(&context);
          items.back() = last.getDictionary(&context);
          record.setCalculationsAttr(ArrayAttr::get(&context, items));
        });
      },
      false);
  mutation(
      "changed calculation site attribution",
      [&](ModuleOp module) {
        module.walk([&](protocol_ir::ProjectionOp record) {
          SmallVector<Attribute> items(record.getCalculations().getValue());
          NamedAttrList fields(cast<DictionaryAttr>(items.front()));
          fields.set("site", StringAttr::get(&context, "missing_invocation"));
          items.front() = fields.getDictionary(&context);
          record.setCalculationsAttr(ArrayAttr::get(&context, items));
        });
      },
      false);
  mutation("changed generated function visibility", [&](ModuleOp module) {
    callee(calculations(module)[1]).setPrivate();
  });
  cases.run("outlined guard bodies must remain private", [&] {
    auto candidate = copy(*bound);
    auto function = callee(calculations(*candidate)[0]);
    auto closure =
        take(protocol::readSourceExecutionClosure(function->getParentOp()));
    auto &body = closure.bodies.at(function.getSymName().str());
    require(isa<exec::TestOp>(body.front().operation) &&
                body.front().regions.size() == 2,
            "missing outlined guard bodies");
    body.front().regions[0].setPublic();
    refuses(protocol::readSourceExecutionClosure(function->getParentOp()),
            "execution-source-closure");
  });
  mutation("wrong capture AND(a,b) becomes AND(a,a)", [&](ModuleOp module) {
    auto call = calculations(module)[1];
    call->setOperand(1, call->getOperand(0));
  });
  mutation("wrong primitive operand", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto op = scopedFinite::applications(function, "bool.and").front();
    op->setOperand(2, op.getInputs()[0]);
  });
  mutation("swapped calculation results", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto returned = scopedComputation::returned(function);
    auto first = returned.getValues()[0], second = returned.getValues()[1];
    returned->setOperand(0, second);
    returned->setOperand(1, first);
  });
  mutation("wrong guard condition", [&](ModuleOp module) {
    auto call = calculations(module)[0];
    call->setOperand(0, participant(module).getBody().front().getArgument(0));
  });
  mutation(
      "wrong guard rejection",
      [&](ModuleOp module) {
        auto function = callee(calculations(module)[0]);
        SmallVector<func::CallOp> arms;
        function.walk([&](func::CallOp call) { arms.push_back(call); });
        require(arms.size() == 2, "guard fixture closed bodies");
        auto first = arms[0].getCalleeAttr();
        arms[0].setCalleeAttr(arms[1].getCalleeAttr());
        arms[1].setCalleeAttr(first);
      },
      false);
  mutation("wrong finish value", [&](ModuleOp module) {
    auto &finish = participant(module).getBody().front().back();
    finish.setOperand(0, participant(module).getBody().front().getArgument(0));
  });
  mutation("work before guard", [&](ModuleOp module) {
    auto calls = calculations(module);
    calls[1]->moveBefore(calls[0]);
  });
  mutation("extra executable calculation", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto first = scopedFinite::applications(function).front();
    scopedComputation::duplicateInvocation(first, function, "extra");
  });
  mutation("changed selection arm", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto closure =
        take(protocol::readSourceExecutionClosure(function->getParentOp()));
    bool changed = false;
    for (const auto &step : closure.bodies.at(function.getSymName().str())) {
      if (!isa<exec::TestOp>(step.operation) || step.outputs.size() != 1)
        continue;
      require(step.regions.size() == 2, "missing selection arms");
      auto arm = cast<func::FuncOp>(step.regions[0]);
      auto complete = cast<exec::CompleteOp>(
          closure.bodies.at(arm.getSymName().str()).back().operation);
      auto argument = cast<BlockArgument>(complete.getValues()[0]);
      complete->setOperand(1, arm.getArgument(3 - argument.getArgNumber()));
      changed = true;
      break;
    }
    require(changed, "no select in fixture");
  });
  mutation("wrong literal", [&](ModuleOp module) {
    unsigned changed = 0;
    callee(calculations(module)[1]).walk([&](exec::BooleanOp value) {
      require(value.getValue(), "literal fixture must start true");
      value.setValue(false);
      ++changed;
    });
    require(changed == 1, "missing or duplicated selection literal");
  });
  mutation("changed primitive contract", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto first = scopedFinite::applications(function, "bool.and").front();
    FlatSymbolRefAttr binding;
    module.walk([&](runtime::BindingOp op) {
      if (op.getContract() == "bool.or")
        binding = FlatSymbolRefAttr::get(&context, op.getSymName());
    });
    require(bool(binding), "missing OR binding in fixture");
    first.setBindingAttr(binding);
  });
  mutation("untracked executable definition", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto *extra = function->clone();
    Builder builder(&context);
    extra->setAttr("sym_name", builder.getStringAttr("extra_definition"));
    extra->setAttr(
        "runtime.origin",
        builder.getArrayAttr({builder.getStringAttr("extra_definition"),
                              builder.getArrayAttr({})}));
    function->getBlock()->push_back(extra);
  });
  mutation("untracked binding declaration", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    OpBuilder builder(function);
    runtime::BindingOp::create(builder, function.getLoc(), "unused_binding",
                               "bool.and", builder.getArrayAttr({}), "",
                               mlir::ArrayAttr{});
  });
  mutation("generated logical origin", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    Builder builder(&context);
    function->setAttr(
        "runtime.origin",
        builder.getArrayAttr({builder.getStringAttr("different_origin"),
                              builder.getArrayAttr({})}));
  });
  cases.run(
      "an unused authored callee cannot become a generated calculation", [&] {
        auto original = copy(*source);
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
        auto templateFunction = callee(calculations(*bound)[1]);
        bound->walk([&](runtime::BindingOp binding) {
          unit.getBody().front().push_back(binding->clone());
        });
        auto closure = take(protocol::readSourceExecutionClosure(
            templateFunction->getParentOp()));
        llvm::DenseSet<Operation *> copied;
        std::function<void(func::FuncOp)> copyRegions =
            [&](func::FuncOp function) {
              for (const auto &step :
                   closure.bodies.at(function.getSymName().str()))
                for (func::FuncOp region : step.regions)
                  if (copied.insert(region).second) {
                    unit.getBody().front().push_back(region->clone());
                    copyRegions(region);
                  }
            };
        copyRegions(templateFunction);
        auto authored = cast<func::FuncOp>(templateFunction->clone());
        Builder builder(&context);
        authored.setSymName("authored_template");
        authored->setAttr(
            "runtime.origin",
            builder.getArrayAttr({builder.getStringAttr("authored_template"),
                                  builder.getArrayAttr({})}));
        unit.getBody().front().push_back(authored);
        require(succeeded(verify(*original)),
                "authored template lost formation");
        // Demand lowering freezes its input after independently checked
        // helper expansion. Compare at that boundary: outlining can rename
        // the template's control bodies and qualify its primitive sites.
        auto frozen = protocol::expandScopedHelpers(*original);
        require(bool(frozen), "authored template expansion refused");
        auto candidate = copy(*original);
        run(*candidate, protocol::createLowerMathPass());
        require(succeeded(mathematical::verifyProjectionPreserved(*frozen,
                                                                  *candidate)),
                "unmodified demand lowering lost the frozen source");
        auto call = calculations(*candidate)[1];
        auto generated = callee(call);
        auto old = call.getCalleeAttr();
        auto replacement =
            FlatSymbolRefAttr::get(&context, "authored_template");
        call.setCalleeAttr(replacement);
        candidate->walk([&](protocol_ir::ProjectionOp record) {
          SmallVector<Attribute> items;
          for (auto item : record.getCalculations()) {
            NamedAttrList fields(cast<DictionaryAttr>(item));
            if (fields.get("callee") == old)
              fields.set("callee", replacement);
            items.push_back(fields.getDictionary(&context));
          }
          record.setCalculationsAttr(builder.getArrayAttr(items));
        });
        generated.erase();
        require(succeeded(verify(*candidate)),
                "repurposed callee lost formation");
        bool freshness = false;
        std::string refusal;
        ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
          refusal += diagnostic.str();
          freshness |= diagnostic.str().find("callee must be fresh") !=
                       std::string::npos;
          return success();
        });
        auto checked =
            mathematical::verifyProjectionPreserved(*frozen, *candidate);
        require(failed(checked) && freshness,
                "authored callee freshness check did not fire: " + refusal);
      });
  cases.run("equivalent authored binding may supply a generated recipe", [&] {
    auto original = copy(*source);
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(&unit.getBody().front());
    runtime::BindingOp::create(builder, unit.getLoc(), "authored_and",
                               "bool.and", builder.getArrayAttr({}), "",
                               mlir::ArrayAttr{});
    require(succeeded(verify(*original)), "authored binding lost formation");
    auto candidate = copy(*original);
    run(*candidate, protocol::createLowerMathPass());
    auto logicalCandidate = copy(*candidate);
    run(*candidate, kernel::createLowerKernelsPass());
    runtime::BindingOp generated;
    candidate->walk([&](runtime::BindingOp binding) {
      if (binding.getContract() == "bool.and" &&
          binding.getSymName() != "authored_and")
        generated = binding;
    });
    require(bool(generated), "fixture has no generated AND binding");
    auto old = FlatSymbolRefAttr::get(&context, generated.getSymName());
    auto authored = FlatSymbolRefAttr::get(&context, "authored_and");
    candidate->walk([&](Operation *op) {
      if (op->getAttr("binding") == old)
        op->setAttr("binding", authored);
    });
    generated.erase();
    require(succeeded(verify(*candidate)), "binding reuse lost formation");
    require(
        succeeded(kernel::verifyKernelLowering(*logicalCandidate, *candidate)),
        "equivalent authored binding was refused");
  });
  cases.run("interfaces remain immutable across lowering", [&] {
    protocol_ir::ProjectionOp a, b;
    source->walk([&](protocol_ir::ProjectionOp op) { a = op; });
    bound->walk([&](protocol_ir::ProjectionOp op) { b = op; });
    require(a.getInterfaces() == b.getInterfaces(),
            "lowering rewrote source facts");
  });
  cases.run("received values remain distinct from shared inputs", [&] {
    auto common =
        parseSourceString<ModuleOp>(R"mlir(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%a: i1):
        %reply = protocol.exchange %a {sender="P", receiver="V", site="message"} : i1
        "protocol.return"(%reply) : (i1) -> ()
      }) {sym_name="main", function_type=(i1)->i1, roles=["P","V"],
          input_roles=[["P","V"]], output_roles=[["V"]]} : () -> ()
    }) {profile=#protocol.profile<protocol>} : () -> () })mlir",
                                    &context);
    require(bool(common), "received fixture refused");
    run(*common, protocol::createProjectProtocolPass());
    auto candidate = copy(*common);
    run(*candidate, protocol::createLowerMathPass());
    auto receiver = participant(*candidate, "V");
    receiver.getBody().front().back().setOperand(
        0, receiver.getBody().front().getArgument(0));
    require(succeeded(verify(*candidate)), "receive mutation lost formation");
    ScopedDiagnosticHandler expected(&context,
                                     [](Diagnostic &) { return success(); });
    require(
        failed(mathematical::verifyProjectionPreserved(*common, *candidate)),
        "received value was replaced by a shared input");
  });
  cases.run("long SSA chains are compared without recursive expansion", [&] {
    std::string text = R"mlir(module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%a: !algebra.field<"bls12-381.fr">, %b: !algebra.field<"bls12-381.fr">):
        %v0 = algebra.field_add %a, %b : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    )mlir";
    for (unsigned index = 1; index != 3000; ++index)
      text += "%v" + std::to_string(index) + " = algebra.field_add %v" +
              std::to_string(index - 1) +
              ", %b : (!algebra.field<\"bls12-381.fr\">, "
              "!algebra.field<\"bls12-381.fr\">) -> "
              "!algebra.field<\"bls12-381.fr\">\n";
    text +=
        R"mlir("protocol.return"(%v2999) : (!algebra.field<"bls12-381.fr">) -> ()
      }) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)->!algebra.field<"bls12-381.fr">, roles=["P"],
          input_roles=[["P"],["P"]], output_roles=[["P"]]} : () -> ()
    }) {profile=#protocol.profile<protocol>} : () -> () })mlir";
    auto common = parseSourceString<ModuleOp>(text, &context);
    require(bool(common), "long-chain fixture refused");
    run(*common, protocol::createProjectProtocolPass());
    unsigned operations = 0;
    common->walk([&](algebra::FieldAddOp) { ++operations; });
    require(operations == 3000, "chain was simplified before comparison");
    // An unused supplied expression keeps an intermediate return port alive
    // during outlining; cleanup must remove the port after participant DCE.
    auto program = participant(*common);
    auto &body = program.getBody().front();
    auto *unused = body.front().clone();
    unused->setOperand(0, body.front().getResult(0));
    OpBuilder builder(&body.back());
    builder.insert(unused);
    require(succeeded(verify(*common)), "dead expression lost formation");
    auto candidate = copy(*common);
    run(*candidate, protocol::createLowerMathPass());
    auto compare = [&] {
      return succeeded(
          mathematical::verifyProjectionPreserved(*common, *candidate));
    };
    if (llvm::llvm_is_multithreaded()) {
      bool checked = false;
      llvm::thread smallStack(std::optional<unsigned>(256 * 1024),
                              [&] { checked = compare(); });
      smallStack.join();
      require(checked, "long-chain lowering refused on a 256 KiB stack");
    } else {
      llvm::outs() << "SKIP 256 KiB stack control: LLVM threads disabled\n";
      require(compare(), "long-chain lowering refused");
    }
    auto calls = participant(*candidate)
                     .getBody()
                     .front()
                     .getOps<protocol_ir::LocalCallOp>();
    require(llvm::hasSingleElement(calls) &&
                (*calls.begin()).getNumResults() == 1,
            "dead expression leaked a result port");
  });
  return cases.result();
}
