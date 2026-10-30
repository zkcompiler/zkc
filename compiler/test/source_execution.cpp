#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Exec/ExecutionModel.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Program/Admission.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
void accepted(llvm::Error error) {
  if (error)
    throw std::runtime_error(llvm::toString(std::move(error)));
}
void refused(llvm::Error error) {
  require(bool(error), "expected source execution refusal");
  llvm::consumeError(std::move(error));
}
std::string change(std::string source, StringRef from, StringRef to) {
  auto at = source.find(from.str());
  require(at != std::string::npos, "missing source mutation target");
  source.replace(at, from.size(), to.str());
  return source;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler capture(&context,
                                  [](Diagnostic &) { return success(); });
  auto buffer = llvm::MemoryBuffer::getFile(
      ZKC_FIXTURES "/runtime/execution-source-helpers.mlir");
  require(bool(buffer), "missing source execution fixture");
  auto source = (*buffer)->getBuffer().str();
  auto parse = [&](StringRef text) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(module && succeeded(verify(*module)),
            "source execution fixture must remain structurally valid");
    return module;
  };
  auto module = parse(source);
  auto expected = take(protocol::readSourceExecutionDefinitions(*module));
  cases.run("retain ordinary helper calls and all potential bodies", [&] {
    require(expected.functions.size() == 4 && expected.bindings.size() == 2,
            "source inventory incomplete");
    const auto &caller = expected.functions.front();
    auto call = caller.body.front().get<program::LocalApply>();
    require(call && call->callee == "sum" &&
                call->inputs == program::Names{caller.arguments[0].name,
                                               caller.arguments[1].name} &&
                caller.body[0].site == "sum_site" &&
                caller.body[1].get<program::LocalApply>() &&
                caller.body.back().get<program::Return>(),
            "source helper arguments, occurrences or continuation lost");
    accepted(protocol::verifySourceExecutionDefinitions(*module, expected));
    accepted(protocol::admitNativeLocalDefinitions(expected));
    auto native = protocol::readExecutionDefinitions(*module, false);
    require(!native, "native publication admitted unresolved source calls");
    llvm::consumeError(native.takeError());
    refused(protocol::verifyExecutionDefinitions(*module, expected, false));
  });
  cases.run(
      "neutral source definitions cannot resolve a synthetic callee", [&] {
        auto candidate = expected;
        candidate.functions.front()
            .body.front()
            .get<program::LocalApply>()
            ->callee = "absent_realization";
        auto error = protocol::admitNativeLocalDefinitions(candidate);
        require(bool(error) && namesIdentifier(llvm::toString(std::move(error)),
                                               "algorithm-call-symbol"),
                "neutral source admission accepted an unresolved callee");
        refused(protocol::verifySourceExecutionDefinitions(*module, candidate));
      });
  auto different = [&](StringRef name, StringRef from, StringRef to) {
    cases.run(name.str(), [&] {
      auto mutated = parse(change(source, from, to));
      take(protocol::readSourceExecutionDefinitions(*mutated));
      refused(protocol::verifySourceExecutionDefinitions(*mutated, expected));
    });
  };
  different("same-typed callee substitution changes correspondence",
            "func.call @sum(", "func.call @difference(");
  different("same-typed argument permutation changes correspondence",
            "func.call @sum(%scope, %a, %b)", "func.call @sum(%scope, %b, %a)");
  different("helper occurrence remains bound", "\"sum_site\"",
            "\"different_site\"");
  different("dormant actual helper body remains bound", "binding = @subtract",
            "binding = @add");
  auto invalid = [&](StringRef name, StringRef from, StringRef to) {
    cases.run(name.str(), [&] {
      auto mutated = parse(change(source, from, to));
      auto read = protocol::readSourceExecutionDefinitions(*mutated);
      require(!read, "invalid source profile was admitted");
      llvm::consumeError(read.takeError());
      refused(protocol::verifySourceExecutionDefinitions(*mutated, expected));
    });
  };
  invalid("recursive source call closure is refused", "func.call @sum(",
          "func.call @caller(");
  invalid("source return must not introduce a native completion tick",
          "\"exec.returned\"(%value) : (!F) -> !O",
          "\"exec.complete\"(%scope, %value) : (!S, !F) -> !O");
  invalid("failed helper cannot resume with an ordinary value",
          "\"exec.failed\"(%cause) : (!exec.stop) -> !O",
          "\"exec.returned\"(%a) : (!F) -> !O");
  invalid("source invocation requires an actual occurrence",
          "{runtime.site = \"sum_site\"}", "{}");
  cases.run(
      "an external signature cannot stand in for an actual helper body", [&] {
        auto actual = parse(source);
        auto helper = actual->lookupSymbol<func::FuncOp>("sum");
        helper.eraseBody();
        helper.setPrivate();
        require(succeeded(verify(*actual)),
                "external helper declaration formation");
        auto read = protocol::readSourceExecutionDefinitions(*actual);
        require(!read, "source helper accepted only a declared signature");
        llvm::consumeError(read.takeError());
        refused(protocol::verifySourceExecutionDefinitions(*actual, expected));
      });
  cases.run(
      "comparison rechecks current target after successful comparison", [&] {
        auto actual = parse(source);
        accepted(protocol::verifySourceExecutionDefinitions(*actual, expected));
        auto caller = actual->lookupSymbol<func::FuncOp>("caller");
        cast<func::CallOp>(caller.front().front()).setCallee("difference");
        require(succeeded(verify(*actual)), "retargeted call formation");
        refused(protocol::verifySourceExecutionDefinitions(*actual, expected));
        auto changed = take(protocol::readSourceExecutionDefinitions(*actual));
        require(
            changed.functions[0].body[0].get<program::LocalApply>()->callee ==
                "difference",
            "source reader reused stale target");
      });
  cases.run(
      "ordinary calls inside control bodies preserve the yield tick", [&] {
        auto fixture = llvm::MemoryBuffer::getFile(
            ZKC_FIXTURES "/runtime/execution-conditional.mlir");
        require(bool(fixture), "missing conditional fixture");
        auto actual =
            parse(change((*fixture)->getBuffer().str(),
                         "\"exec.complete\"(%scope, %value) : (!S, !F) -> !R",
                         "\"exec.returned\"(%value) : (!F) -> !R"));
        actual->getBody()->push_back(
            module->lookupSymbol<func::FuncOp>("sum").clone());
        auto region = actual->lookupSymbol<func::FuncOp>("yes");
        auto primitive = cast<exec::ApplyOp>(region.front().front());
        OpBuilder builder(primitive);
        auto call = func::CallOp::create(builder, primitive.getLoc(), "sum",
                                         primitive->getResultTypes(),
                                         primitive->getOperands());
        call->setAttr("runtime.site", builder.getStringAttr("sum"));
        primitive.getOutcome().replaceAllUsesWith(call.getResult(0));
        primitive.erase();
        require(succeeded(verify(*actual)), "nested source call formation");
        auto record = take(protocol::readSourceExecutionDefinitions(*actual));
        auto branch = record.functions[0].body[0].get<program::Conditional>();
        require(record.functions.size() == 2 && branch &&
                    branch->thenBody[0].get<program::LocalApply>() &&
                    branch->thenBody.back().get<program::Yield>(),
                "ordinary call and outlined yield conflated");
        accepted(protocol::verifySourceExecutionDefinitions(*actual, record));

        call.setCallee("yes");
        require(succeeded(verify(*actual)),
                "outlined target substitution formation");
        auto outlined = protocol::readSourceExecutionDefinitions(*actual);
        require(!outlined,
                "ordinary helper call selected an outlined control body");
        llvm::consumeError(outlined.takeError());
        refused(protocol::verifySourceExecutionDefinitions(*actual, record));
        call.setCallee("sum");

        exec::CompleteOp complete;
        region.walk([&](exec::CompleteOp op) { complete = op; });
        require(bool(complete), "missing charged yield");
        builder.setInsertionPoint(complete);
        auto packed = exec::ReturnOp::create(builder, complete.getLoc(),
                                             complete.getOutcome().getType(),
                                             complete.getValues());
        complete.getOutcome().replaceAllUsesWith(packed.getOutcome());
        complete.erase();
        require(succeeded(verify(*actual)), "packaged yield formation");
        auto read = protocol::readSourceExecutionDefinitions(*actual);
        require(!read,
                "source helper support silently removed a control yield tick");
        llvm::consumeError(read.takeError());
        refused(protocol::verifySourceExecutionDefinitions(*actual, record));
      });
  auto mixed = [&] {
    auto actual = parse(source);
    auto mathematics = parse(R"mlir(
      !F = !algebra.field<"koala-bear">
      module {
        func.func private @math_sum(%a: !F, %b: !F) -> !F {
          %v = algebra.field_add %a, %b : (!F, !F) -> !F
          func.return %v : !F
        }
        func.func private @math_caller(%a: !F, %b: !F) -> !F {
          %v = func.call @math_sum(%a, %b) : (!F, !F) -> !F
          func.return %v : !F
        }
      })mlir");
    for (auto function : mathematics->getOps<func::FuncOp>())
      actual->getBody()->push_back(function.clone());
    return actual;
  };
  cases.run("one source table checks both callable owners", [&] {
    auto actual = mixed();
    auto record = take(protocol::readSourceExecutionDefinitions(*actual));
    require(record.functions.size() == 4,
            "mathematical bodies entered the native scoped view");
    accepted(protocol::verifySourceExecutionDefinitions(*actual, expected));
    auto native = protocol::readExecutionDefinitions(*actual, false);
    require(!native, "prepared profile admitted unselected mathematics");
    llvm::consumeError(native.takeError());
    refused(protocol::verifyExecutionDefinitions(*actual, expected, false));
  });
  auto invalidMath = [&](StringRef label, auto mutate) {
    cases.run(label.str(), [&] {
      auto actual = mixed();
      accepted(protocol::verifySourceExecutionDefinitions(*actual, expected));
      mutate(*actual);
      require(succeeded(verify(*actual)),
              "mathematical negative control must remain formed MLIR");
      auto read = protocol::readSourceExecutionDefinitions(*actual);
      require(!read, "mathematical definition escaped both checking owners");
      llvm::consumeError(read.takeError());
      refused(protocol::verifySourceExecutionDefinitions(*actual, expected));
    });
  };
  invalidMath("dormant mathematical declaration needs an actual body",
              [](ModuleOp actual) {
                actual.lookupSymbol<func::FuncOp>("math_sum").eraseBody();
              });
  invalidMath(
      "dormant mathematical recursion remains rejected", [](ModuleOp actual) {
        auto function = actual.lookupSymbol<func::FuncOp>("math_caller");
        cast<func::CallOp>(function.front().front()).setCallee("math_caller");
      });
  invalidMath(
      "mathematical bodies cannot hide a terminal stop", [](ModuleOp actual) {
        auto function = actual.lookupSymbol<func::FuncOp>("math_sum");
        OpBuilder builder(&function.front().front());
        exec::StopOp::create(builder, function.getLoc(),
                             exec::StopType::get(actual.getContext()), "abort");
      });
  invalidMath("a source math helper cannot claim a public entry",
              [](ModuleOp actual) {
                actual.lookupSymbol<func::FuncOp>("math_sum").setPublic();
              });
  invalidMath("execution annotation cannot admit a mathematical signature",
              [](ModuleOp actual) {
                auto function = actual.lookupSymbol<func::FuncOp>("math_sum");
                Builder builder(actual.getContext());
                function->setAttr(
                    "runtime.origin",
                    builder.getArrayAttr({builder.getStringAttr("math_sum"),
                                          builder.getArrayAttr({})}));
              });
  invalidMath("removing an origin cannot hide an execution signature",
              [](ModuleOp actual) {
                actual.lookupSymbol<func::FuncOp>("identity")
                    ->removeAttr("runtime.origin");
              });
  cases.run(
      "mathematical admission does not claim equation correspondence", [&] {
        auto actual = mixed();
        auto function = actual->lookupSymbol<func::FuncOp>("math_sum");
        cast<func::ReturnOp>(function.front().back())
            ->setOperand(0, function.getArgument(0));
        // This different equation remains total. Its source binding is
        // checked by the mathematical/language owner, not this view.
        take(protocol::readSourceExecutionDefinitions(*actual));
        accepted(protocol::verifySourceExecutionDefinitions(*actual, expected));
      });
  cases.run(
      "mixed inventory does not verify another symbol table's bodies", [&] {
        auto actual = mixed();
        auto other = parse(R"mlir(
                 module @other {
                   func.func private @unchecked(
                       %xs: !algebra.field_vector<"koala-bear">, %i: ui64)
                       -> !algebra.field<"koala-bear"> {
                     %v = "data.bounded_at"(%xs, %i) :
                       (!algebra.field_vector<"koala-bear">, ui64)
                       -> !algebra.field<"koala-bear">
                     func.return %v : !algebra.field<"koala-bear">
                   }
                 })mlir");
        actual->getBody()->push_back(other->clone());
        // The nested owner's bound-premise checks fail. Merely placing
        // it beside this component must not transfer its ownership.
        require(succeeded(verify(*actual)), "nested owner formation");
        require(
            failed(mathematical::verifyTotalClosure(*other)),
            "unrelated mathematical control unexpectedly discharged its bound");
        take(protocol::readSourceExecutionDefinitions(*actual));
        accepted(protocol::verifySourceExecutionDefinitions(*actual, expected));
      });
  for (StringRef name :
       {"mathematical/helper-realization", "finite/realized-total",
        "structured-source/indexed-helper"})
    cases.run("mixed mathematical closure: " + name, [&] {
      auto fixture = llvm::MemoryBuffer::getFile(std::string(ZKC_FIXTURES) +
                                                 "/" + name.str() + ".mlir");
      require(bool(fixture), "missing mathematical source fixture");
      auto mathematical = parse((*fixture)->getBuffer());
      auto owner =
          *mathematical->getOps<protocol_ir::ProtocolModuleOp>().begin();
      auto actual = parse(source);
      for (auto &op : owner.getBody().front())
        if (isa<data::DomainOp>(op) ||
            (isa<func::FuncOp>(op) &&
             !protocol::isScopedExecutionFunction(cast<func::FuncOp>(op))))
          actual->getBody()->push_back(op.clone());
      require(succeeded(verify(*actual)), "mixed domain closure formation");
      take(protocol::readSourceExecutionDefinitions(*actual));
      accepted(protocol::verifySourceExecutionDefinitions(*actual, expected));
      if (name == "structured-source/indexed-helper") {
        auto step = actual->lookupSymbol<func::FuncOp>("step");
        auto call = cast<func::CallOp>(step.front().front());
        call->setOperand(0, step.getArgument(3));
        require(succeeded(verify(*actual)), "mutated domain closure formation");
        auto read = protocol::readSourceExecutionDefinitions(*actual);
        require(!read, "a same-typed vector inherited another vector's bound");
        llvm::consumeError(read.takeError());
        refused(protocol::verifySourceExecutionDefinitions(*actual, expected));
      }
    });
  return cases.result();
}
