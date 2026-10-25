#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Program/Admission.h"
#include "zkc/Translation/Execution.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string changed(std::string source, StringRef before, StringRef after) {
  auto at = source.find(before.str());
  require(at != std::string::npos, "missing mutation target");
  source.replace(at, before.size(), after.str());
  return source;
}
void refused(llvm::Error error, StringRef code = "execution-correspondence") {
  require(bool(error), "expected correspondence refusal");
  auto message = llvm::toString(std::move(error));
  require(namesIdentifier(message, code), message);
}
void accepted(llvm::Error error) {
  if (error)
    throw std::runtime_error(llvm::toString(std::move(error)));
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &value) {
    llvm::raw_string_ostream output(diagnostics);
    value.print(output);
    return success();
  });
  auto parse = [&](StringRef source) {
    diagnostics.clear();
    auto module = parseSourceString<ModuleOp>(source, &context);
    require(module && succeeded(verify(*module)),
            "comparison control must be structurally valid: " + diagnostics);
    return module;
  };
  auto fixture = [](StringRef name) {
    auto file = llvm::MemoryBuffer::getFile(std::string(ZKC_FIXTURES) +
                                            "/runtime/execution-" + name.str() +
                                            ".mlir");
    require(bool(file), "missing comparison fixture");
    return (*file)->getBuffer().str();
  };
  auto source = fixture("conditional");
  auto module = parse(source);
  auto expected = take(protocol::readLocalExecution(*module, false));
  auto checkMutation = [&](StringRef name, StringRef before, StringRef after) {
    cases.run(name, [&] {
      auto actual = parse(changed(source, before, after));
      refused(protocol::verifyLocalExecution(*actual, expected, false));
    });
  };
  cases.run("compare hand-authored actual CFG with admitted records", [&] {
    accepted(protocol::verifyLocalExecution(*module, expected, false));
  });
  checkMutation("same-typed arithmetic callee is bound", "binding=@add",
                "binding=@multiply");
  checkMutation("same-typed actual inputs are ordered",
                "\"exec.apply\"(%scope, %x, %y)",
                "\"exec.apply\"(%scope, %y, %x)");
  checkMutation("reached occurrence is bound", "site=\"sum\"",
                "site=\"other\"");
  checkMutation("actual completion values are bound",
                "\"exec.complete\"(%scope, %sum)",
                "\"exec.complete\"(%scope, %x)");
  checkMutation("native completion cannot become plain packaging",
                "\"exec.complete\"(%scope, %sum) : (!S, !F)",
                "\"exec.returned\"(%sum) : (!F)");
  checkMutation("terminal cause is bound", "reason=\"refused\"",
                "reason=\"reject\"");
  checkMutation("logical origin is bound", "runtime.origin=[\"work\", []]",
                "runtime.origin=[\"other\", []]");
  checkMutation("dormant binding declaration is compared",
                "contract=\"field.mul\"", "contract=\"field.sub\"");
  checkMutation("callee receives the acquired scope",
                "@yes(%child_yes, %x, %y)", "@yes(%scope, %x, %y)");
  checkMutation("outlined callee receives exact ordered captures",
                "@yes(%child_yes, %x, %y)", "@yes(%child_yes, %y, %x)");
  checkMutation("conditional selection matches reached arm",
                "selection=\"then\"", "selection=\"else\"");
  checkMutation("parent acceptance uses the actual parent",
                "\"runtime.accept_transfer\"(%scope, %held_yes)",
                "\"runtime.accept_transfer\"(%child_yes, %held_yes)");
  checkMutation("unknown executable attributes are refused", "binding=@add",
                "binding=@add, unchecked=true");
  checkMutation("dormant body attributes are refused",
                "reason=\"refused\", site=\"reject\"",
                "reason=\"refused\", site=\"reject\", unchecked=true");
  checkMutation("malformed region marker does not hide a root",
                "runtime.origin=[\"work\", []]",
                "runtime.origin=[\"work\", []], runtime.region=false");
  checkMutation("outlined boundaries cannot silently inline",
                "{no_inline, runtime.region}", "{runtime.region}");
  checkMutation("unused outlined definitions are not silently discarded",
                "module {",
                "module {\n func.func private @unused(%scope: !S) -> !R "
                "attributes {no_inline, runtime.region}\n");
  cases.run("missing comparison subject has a distinct refusal", [&] {
    refused(protocol::verifyLocalExecution({}, expected, false),
            "execution-correspondence-subject");
  });
  auto changedRecord = [&](StringRef name, auto mutate) {
    cases.run(name, [&] {
      auto record = expected;
      mutate(record);
      program::Participants admitted;
      admitted.functions = record.functions;
      admitted.bindings = record.bindings;
      accepted(protocol::admit(admitted));
      refused(protocol::verifyLocalExecution(*module, record, false));
    });
  };
  changedRecord("decoded body cannot substitute a same-typed callee",
                [](auto &record) {
                  record.functions[0]
                      .body[0]
                      .template get<program::Conditional>()
                      ->thenBody[0]
                      .template get<program::Operation>()
                      ->callee = "multiply";
                });
  changedRecord("decoded body cannot swap same-typed operands",
                [](auto &record) {
                  auto op = record.functions[0]
                                .body[0]
                                .template get<program::Conditional>()
                                ->thenBody[0]
                                .template get<program::Operation>();
                  std::swap(op->inputs[0], op->inputs[1]);
                });
  changedRecord("decoded capture order is bound", [](auto &record) {
    auto branch =
        record.functions[0].body[0].template get<program::Conditional>();
    std::swap(branch->captures[0], branch->captures[1]);
  });
  changedRecord(
      "decoded result projection cannot bypass an instruction",
      [](auto &record) {
        auto branch =
            record.functions[0].body[0].template get<program::Conditional>();
        branch->thenBody.back().template get<program::Yield>()->values = {
            branch->captures[0]};
      });
  changedRecord(
      "decoded program cannot omit a reached instruction", [](auto &record) {
        auto branch =
            record.functions[0].body[0].template get<program::Conditional>();
        branch->thenBody = {{"", program::Yield{{branch->captures[0]}}}};
      });
  changedRecord(
      "decoded program cannot insert an unused instruction", [](auto &record) {
        auto branch =
            record.functions[0].body[0].template get<program::Conditional>();
        branch->thenBody.insert(
            branch->thenBody.begin(),
            {"literal", program::BooleanConstant{"unused", false}});
      });
  changedRecord("decoded origin statics are bound", [](auto &record) {
    record.functions[0].origin->arguments = {{"F", "bls12-381.fr"}};
  });
  changedRecord("decoded stopped cause is bound", [](auto &record) {
    record.functions[0]
        .body[0]
        .template get<program::Conditional>()
        ->elseBody[0]
        .template get<program::Stop>()
        ->reason = "abort";
  });
  cases.run("SSA and decoded local variable names are not authority", [&] {
    auto text = source;
    size_t position = 0;
    while ((position = text.find("%sum", position)) != std::string::npos) {
      text.replace(position, 4, "%renamed_sum");
      position += 12;
    }
    auto renamed = parse(text);
    auto record = expected;
    auto &argument = record.functions[0].arguments[0];
    argument.name = "renamed_condition";
    record.functions[0].body[0].get<program::Conditional>()->condition =
        argument.name;
    accepted(protocol::verifyLocalExecution(*renamed, record, false));
  });
  cases.run("successful comparison grants no mutation cache", [&] {
    auto actual = parse(source);
    accepted(protocol::verifyLocalExecution(*actual, expected, false));
    actual->walk([&](exec::ApplyOp op) {
      op.setBindingAttr(FlatSymbolRefAttr::get(&context, "multiply"));
    });
    require(succeeded(verify(*actual)), "post-check mutation formation");
    refused(protocol::verifyLocalExecution(*actual, expected, false));
  });
  source = fixture("loop");
  module = parse(source);
  expected = take(protocol::readLocalExecution(*module, false));
  cases.run("compare conditional carried loop", [&] {
    accepted(protocol::verifyLocalExecution(*module, expected, false));
  });
  checkMutation("loop comparison must use admitted current coordinate",
                "arith.cmpi ult, %i, %high", "arith.cmpi ult, %low, %high");
  checkMutation("loop comparison predicate cannot change", "arith.cmpi ult",
                "arith.cmpi ule");
  checkMutation("loop increment is exactly one", "arith.constant 1 : i64",
                "arith.constant 2 : i64");
  checkMutation("iteration coordinate is bound",
                "\"runtime.iteration\"(%scope, %i)",
                "\"runtime.iteration\"(%scope, %low)");
  checkMutation("false continuation cannot perform another iteration",
                "^finish(%carried : !T)", "^increment(%carried : !T)");
  checkMutation("early failure cannot skip old carry cleanup",
                "[^body, ^release_failure]", "[^body, ^failed]");
  changedRecord("decoded loop bounds are ordered", [](auto &record) {
    auto loop = record.functions[0].body[0].template get<program::For>();
    std::swap(loop->lower, loop->upper);
  });
  changedRecord(
      "decoded loop cannot drop its continuation condition", [](auto &record) {
        auto loop = record.functions[0].body[0].template get<program::For>();
        loop->conditional = false;
        auto &values = loop->body.back().template get<program::Yield>()->values;
        values.erase(values.begin());
      });
  return cases.result();
}
