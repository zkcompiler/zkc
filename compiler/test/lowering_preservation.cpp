#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
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
local::FuncOp callee(local::CallOp call) {
  return SymbolTable::lookupNearestSymbolFrom<local::FuncOp>(
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
  auto bound = copy(*source);
  run(*bound, protocol::createLowerMathPass());
  Cases cases;
  cases.run("all Boolean recipes, shared demand, received guard", [&] {
    require(succeeded(mathematical::verifyProjectionPreserved(*source, *bound)),
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
    auto call =
        *participant(*split).getBody().front().getOps<local::CallOp>().begin();
    auto function = callee(call);
    auto &body = function.getBody().front();
    auto &first = body.front();
    require(first.getNumResults() == 1 && body.getNumArguments() == 2,
            "split fixture recipe");
    OpBuilder builder(function);
    auto prefix = local::FuncOp::create(
        builder, function.getLoc(), "split_prefix", function.getFunctionType());
    prefix->setAttr("logical_origin",
                    builder.getArrayAttr({builder.getStringAttr("split_prefix"),
                                          builder.getArrayAttr({})}));
    auto *entry = prefix.addEntryBlock();
    builder.setInsertionPointToEnd(entry);
    IRMapping mapping;
    for (auto [a, b] : llvm::zip(body.getArguments(), entry->getArguments()))
      mapping.map(a, b);
    auto *andOperation = builder.clone(first, mapping);
    local::ReturnOp::create(builder, call.getLoc(), andOperation->getResults());
    builder.setInsertionPoint(call);
    auto prefixCall = local::CallOp::create(
        builder, call.getLoc(), call.getResultTypes(), call.getInputs(),
        prefix.getSymName(), "split_prefix");
    first.getResult(0).replaceAllUsesWith(body.getArgument(1));
    first.erase();
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
        failed(mathematical::verifyProjectionPreserved(*original, *split)) &&
            partition,
        "split escaped the closed lowering policy");
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
        code |= diagnostic.str().find("mathematical-lowering-preservation") !=
                std::string::npos;
        return success();
      });
      require(failed(mathematical::verifyProjectionPreserved(*source,
                                                             *candidate)) &&
                  code,
              "lowering mutation escaped data-flow comparison");
    });
  };
  auto calculations = [](ModuleOp module) {
    return SmallVector<local::CallOp>(
        participant(module).getBody().front().getOps<local::CallOp>());
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
  mutation(
      "extra generated function attribute",
      [&](ModuleOp module) {
        callee(calculations(module)[1])
            ->setAttr("sym_visibility", StringAttr::get(&context, "private"));
      },
      false, "interactive-local-visibility");
  mutation("wrong capture AND(a,b) becomes AND(a,a)", [&](ModuleOp module) {
    auto call = calculations(module)[1];
    call->setOperand(1, call->getOperand(0));
  });
  mutation("wrong primitive operand", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto &op = function.getBody().front().front();
    op.setOperand(1, op.getOperand(0));
  });
  mutation("swapped calculation results", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto returned = cast<local::ReturnOp>(function.getBody().front().back());
    auto first = returned.getInputs()[0], second = returned.getInputs()[1];
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
        function.walk([](local::LocalIfOp branch) {
          Region temporary;
          temporary.takeBody(branch.getThenRegion());
          branch.getThenRegion().takeBody(branch.getElseRegion());
          branch.getElseRegion().takeBody(temporary);
        });
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
    auto &first = function.getBody().front().front();
    auto *extra = first.clone();
    extra->setAttr("site", StringAttr::get(&context, "extra"));
    OpBuilder builder(&first);
    builder.setInsertionPointAfter(&first);
    builder.insert(extra);
  });
  mutation("changed selection arm", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    bool done = false;
    function.walk([&](local::LocalIfOp select) {
      if (done || select.getNumResults() != 1 || select.getNumOperands() != 3)
        return;
      auto &block = select.getThenRegion().front();
      auto yield = cast<local::LocalYieldOp>(block.back());
      yield->setOperand(
          0, block.getArgument(
                 1 - cast<BlockArgument>(yield.getInputs()[0]).getArgNumber()));
      done = true;
    });
    require(done, "no select in fixture");
  });
  mutation("wrong literal", [&](ModuleOp module) {
    callee(calculations(module)[1]).walk([](local::BoolConstantOp value) {
      value.setValue(false);
    });
  });
  mutation("changed primitive contract", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto &first = function.getBody().front().front();
    FlatSymbolRefAttr binding;
    module.walk([&](local::OperationBindingOp op) {
      if (op.getContract() == "bool.or")
        binding = FlatSymbolRefAttr::get(&context, op.getSymName());
    });
    require(bool(binding), "missing OR binding in fixture");
    OperationState state(first.getLoc(), "algebra.exec.bool_or");
    state.addOperands(first.getOperands());
    state.addTypes(first.getResultTypes());
    state.addAttributes(first.getAttrs());
    OpBuilder builder(&first);
    auto *replacement = builder.create(state);
    replacement->setAttr("binding", binding);
    first.replaceAllUsesWith(replacement->getResults());
    first.erase();
  });
  mutation("untracked executable definition", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    auto *extra = function->clone();
    Builder builder(&context);
    extra->setAttr("sym_name", builder.getStringAttr("extra_definition"));
    extra->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr("extra_definition"),
                              builder.getArrayAttr({})}));
    function->getBlock()->push_back(extra);
  });
  mutation("untracked binding declaration", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    OpBuilder builder(function);
    local::OperationBindingOp::create(builder, function.getLoc(),
                                      "unused_binding", "bool.and",
                                      builder.getArrayAttr({}), "");
  });
  mutation("generated logical origin", [&](ModuleOp module) {
    auto function = callee(calculations(module)[1]);
    Builder builder(&context);
    function->setAttr(
        "logical_origin",
        builder.getArrayAttr({builder.getStringAttr("different_origin"),
                              builder.getArrayAttr({})}));
  });
  cases.run(
      "an unused authored callee cannot become a generated calculation", [&] {
        auto original = copy(*source);
        auto unit =
            cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
        auto templateFunction = callee(calculations(*bound)[1]);
        bound->walk([&](local::OperationBindingOp binding) {
          unit.getBody().front().push_back(binding->clone());
        });
        auto authored = cast<local::FuncOp>(templateFunction->clone());
        Builder builder(&context);
        authored.setSymName("authored_template");
        authored->setAttr(
            "logical_origin",
            builder.getArrayAttr({builder.getStringAttr("authored_template"),
                                  builder.getArrayAttr({})}));
        unit.getBody().front().push_back(authored);
        require(succeeded(verify(*original)),
                "authored template lost formation");
        auto candidate = copy(*original);
        run(*candidate, protocol::createLowerMathPass());
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
        ScopedDiagnosticHandler expected(&context, [&](Diagnostic &diagnostic) {
          freshness |= diagnostic.str().find("callee must be fresh") !=
                       std::string::npos;
          return success();
        });
        require(failed(mathematical::verifyProjectionPreserved(*original,
                                                               *candidate)) &&
                    freshness,
                "authored callee was repurposed as generated work");
      });
  cases.run("equivalent authored binding may supply a generated recipe", [&] {
    auto original = copy(*source);
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
    OpBuilder builder(&context);
    builder.setInsertionPointToStart(&unit.getBody().front());
    local::OperationBindingOp::create(builder, unit.getLoc(), "authored_and",
                                      "bool.and", builder.getArrayAttr({}), "");
    require(succeeded(verify(*original)), "authored binding lost formation");
    auto candidate = copy(*original);
    run(*candidate, protocol::createLowerMathPass());
    local::OperationBindingOp generated;
    candidate->walk([&](local::OperationBindingOp binding) {
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
    require(succeeded(
                mathematical::verifyProjectionPreserved(*original, *candidate)),
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
    auto calls =
        participant(*candidate).getBody().front().getOps<local::CallOp>();
    require(llvm::hasSingleElement(calls) &&
                (*calls.begin()).getNumResults() == 1,
            "dead expression leaked a result port");
  });
  return cases.result();
}
