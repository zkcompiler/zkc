#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Translation/Execution.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string change(std::string source, StringRef from, StringRef to) {
  auto at = source.find(from.str());
  require(at != std::string::npos, "mutation target absent");
  source.replace(at, from.size(), to.str());
  return source;
}
std::string replaceAll(std::string source, StringRef from, StringRef to) {
  size_t at = 0;
  while ((at = source.find(from.str(), at)) != std::string::npos) {
    source.replace(at, from.size(), to.str());
    at += to.size();
  }
  return source;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostic;
  std::vector<std::string> codes;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &value) {
    llvm::raw_string_ostream stream(diagnostic);
    value.print(stream);
    for (const auto &refusal : diagnostics::refusals(value))
      codes.push_back(refusal.code);
    return success();
  });
  auto file = llvm::MemoryBuffer::getFile(
      ZKC_FIXTURES "/runtime/execution-conditional.mlir");
  require(bool(file), "missing execution fixture");
  auto source = (*file)->getBuffer().str();
  auto read = [&](const std::string &source, bool expected,
                  bool physical = false) {
    diagnostic.clear();
    auto module = parseSourceString<ModuleOp>(source, &context);
    require(module && succeeded(verify(*module)),
            "execution mutation must remain structurally valid: " + diagnostic);
    auto result = protocol::readLocalExecution(*module, physical);
    if (expected && !result)
      throw std::runtime_error(llvm::toString(result.takeError()));
    require(bool(result) == expected, "unexpected reconstruction result");
    if (!result) {
      std::string code;
      llvm::handleAllErrors(
          result.takeError(),
          [&](const Refusal &refusal) { code = refusal.code; },
          [&](const llvm::ErrorInfoBase &) {});
      require(code == "execution-cfg",
              "reader refusal lost its diagnostic identifier");
      return program::LocalDefinitions{};
    }
    return std::move(*result);
  };
  cases.run("reconstruct actual conditional, calls and terminal outcomes", [&] {
    auto model = read(source, true);
    require(model.functions.size() == 1 && model.bindings.size() == 2,
            "outlined helpers escaped into native callable inventory");
    auto &function = model.functions.front();
    require(function.body.size() == 2 && function.arguments.size() == 3,
            "wrong reconstructed function");
    auto branch = function.body.front().get<program::Conditional>();
    require(branch && branch->condition == function.arguments[0].name &&
                branch->captures ==
                    program::Names{function.arguments[1].name,
                                   function.arguments[2].name} &&
                branch->thenBody.size() == 2 && branch->elseBody.size() == 1,
            "lost branch/capture association");
    auto call = branch->thenBody.front().get<program::Operation>();
    require(call && call->callee == "add" && call->inputs == branch->captures &&
                branch->thenBody.back().get<program::Yield>() &&
                branch->elseBody.front().get<program::Stop>() &&
                function.body.back().get<program::Return>(),
            "lost native body or failure semantics");
  });
  auto reject = [&](StringRef name, StringRef from, StringRef to) {
    cases.run(name, [&] { read(change(source, from, to), false); });
  };
  reject("callee body cannot replace metered completion with packaging",
         "\"exec.complete\"(%scope, %sum) : (!S, !F)",
         "\"exec.returned\"(%sum) : (!F)");
  reject("entry and selected branch must agree", "selection=\"then\"",
         "selection=\"else\"");
  reject("entry occurrence must match reached test",
         "site=\"choose\", selection=\"then\"",
         "site=\"other\", selection=\"then\"");
  reject("body must borrow the acquired child scope",
         "@yes(%child_yes, %x, %y)", "@yes(%scope, %x, %y)");
  reject("body must receive actual captured operands",
         "@yes(%child_yes, %x, %y)", "@yes(%child_yes, %y, %x)");
  reject("arm entry captures must agree",
         "%entered_no = \"runtime.enter_scope\"(%scope, %x, %y)",
         "%entered_no = \"runtime.enter_scope\"(%scope, %y, %x)");
  reject("parent binding cannot select another scope",
         "\"runtime.accept_transfer\"(%scope, %held_yes)",
         "\"runtime.accept_transfer\"(%child_yes, %held_yes)");
  reject("binding symbol must resolve", "binding=@add", "binding=@absent");
  reject("binding arguments determine actual ports",
         "arguments=[\"koala-bear\"]", "arguments=[\"bls12-381.fr\"]");
  reject("reached parameter formation remains checked", "parameters=[]",
         "parameters=[\"unexpected\"]");
  reject("unknown invocation attributes cannot bypass checking", "binding=@add",
         "binding=@add, unchecked=true");
  reject("unconsumed region definitions are refused", "module {",
         "module {\n func.func private @unused(%scope: !S) -> !R "
         "attributes {no_inline, runtime.region} {\n"
         " %cause = \"exec.reject\"(%scope) {site=\"stop\", reason=\"stop\"} : "
         "(!S) -> !exec.stop\n"
         " %result = \"exec.failed\"(%cause) : (!exec.stop) -> !R\n"
         " func.return %result : !R\n }");
  reject("all potential arm bodies require native completion",
         "reason=\"refused\", site=\"reject\"",
         "reason=\"refused\", site=\"reject\", unchecked=true");
  reject("function boundary must retain no-inline contract",
         "{no_inline, runtime.region}", "{runtime.region}");
  reject("root cannot hide a malformed region marker",
         "runtime.origin=[\"work\", []]",
         "runtime.origin=[\"work\", []], runtime.region=false");
  auto unusedLiteral = change(
      source, "    %applied = \"exec.apply\"",
      "    %literal = \"exec.boolean\"(%scope) {site=\"unused_literal\", "
      "value=true} : (!S) -> !exec.outcome<(i1)>\n"
      "    \"exec.dispatch\"(%literal)[^literal_value, ^failed] : "
      "(!exec.outcome<(i1)>) -> ()\n"
      "  ^literal_value(%unused: i1):\n"
      "    %applied = \"exec.apply\"");
  cases.run("unused native instruction retains its reached occurrence", [&] {
    auto model = read(unusedLiteral, true);
    auto &arm =
        model.functions[0].body[0].get<program::Conditional>()->thenBody;
    require(arm.size() == 3 && arm[0].get<program::BooleanConstant>(),
            "unused literal lost its fallible reached instruction");
  });
  cases.run("unused instruction cannot mix execution stages", [&] {
    auto represented = replaceAll(
        unusedLiteral, "!exec.outcome<(i1)>",
        "!exec.outcome<(!runtime.represented<i1, \"native.bool/0\">)>");
    represented =
        change(represented, "%unused: i1",
               "%unused: !runtime.represented<i1, \"native.bool/0\">");
    // Keep the conditional admission's machine decision in i1.
    represented = change(
        represented,
        "!D = !exec.outcome<(!runtime.represented<i1, \"native.bool/0\">)>",
        "!D = !exec.outcome<(i1)>");
    read(represented, false);
  });
  cases.run(
      "changed same-typed binding changes reconstructed computation", [&] {
        auto model =
            read(change(source, "binding=@add", "binding=@multiply"), true);
        auto branch =
            model.functions.front().body.front().get<program::Conditional>();
        require(branch->thenBody.front().get<program::Operation>()->callee ==
                    "multiply",
                "reader substituted a retained or expected body");
      });
  cases.run("same-typed argument reorder is read from actual SSA", [&] {
    auto model = read(change(source, "\"exec.apply\"(%scope, %x, %y)",
                             "\"exec.apply\"(%scope, %y, %x)"),
                      true);
    auto branch =
        model.functions.front().body.front().get<program::Conditional>();
    require(branch->thenBody.front().get<program::Operation>()->inputs ==
                program::Names{branch->captures[1], branch->captures[0]},
            "reader replaced actual operands with metadata");
  });
  auto loopFile =
      llvm::MemoryBuffer::getFile(ZKC_FIXTURES "/runtime/execution-loop.mlir");
  require(bool(loopFile), "missing loop fixture");
  auto loopSource = (*loopFile)->getBuffer().str();
  cases.run("reconstruct conditional carry with checked bounds", [&] {
    auto model = read(loopSource, true);
    auto &function = model.functions.front();
    auto loop = function.body.front().get<program::For>();
    require(loop && loop->conditional &&
                loop->lower == function.arguments[0].name &&
                loop->upper == function.arguments[1].name &&
                loop->carried.size() == 1 &&
                loop->carried.front().second == function.arguments[2].name &&
                loop->captures == program::Names{function.arguments[3].name},
            "loop lost actual bounds, carry or capture");
    require(
        loop->body.size() == 1 &&
            loop->body.front().get<program::Yield>()->values ==
                program::Names{loop->captures[0], loop->carried.front().first},
        "loop lost its conditional result or body");
  });
  auto refuseLoop = [&](StringRef name, StringRef from, StringRef to) {
    cases.run(name, [&] { read(change(loopSource, from, to), false); });
  };
  refuseLoop("loop must start at its admitted lower bound",
             "^header(%low, %initial", "^header(%high, %initial");
  refuseLoop("loop must compare the admitted upper bound", "ult, %i, %high",
             "ult, %i, %low");
  refuseLoop("loop comparison is strictly unsigned", "cmpi ult", "cmpi ule");
  refuseLoop("loop must increment by one", "constant 1 : i64",
             "constant 2 : i64");
  refuseLoop("loop must increment the current coordinate", "addi %i, %one",
             "addi %low, %one");
  refuseLoop("iteration admission must use current coordinate",
             "\"runtime.iteration\"(%scope, %i)",
             "\"runtime.iteration\"(%scope, %low)");
  refuseLoop("frame origin must use current coordinate",
             "\"runtime.enter_scope\"(%scope, %i,",
             "\"runtime.enter_scope\"(%scope, %low,");
  refuseLoop("iteration must use the allocated native index",
             "@step(%child, %index,", "@step(%child, %lower,");
  refuseLoop("iteration cannot replace live carry with initial value",
             "@step(%child, %index, %value,", "@step(%child, %index, %seed,");
  refuseLoop("iteration failure cannot bypass carry release",
             "(%allocated)[^enter, ^release_failure]",
             "(%allocated)[^enter, ^failed]");
  refuseLoop("failed child exit cannot bypass carry release",
             "(%left)[^replace, ^release_failure]",
             "(%left)[^replace, ^failed]");
  refuseLoop("early completion cannot perform another iteration",
             "^finish(%carried : !T)", "^increment(%carried : !T)");
  auto unconditional = change(loopSource, "!B = !exec.outcome<(i1, !F)>",
                              "!B = !exec.outcome<(!F)>");
  unconditional = change(unconditional, "!C = !runtime.transfer<(i1, !F)>",
                         "!C = !runtime.transfer<(!F)>");
  unconditional = change(
      unconditional, "\"exec.complete\"(%scope, %again, %value) : (!S, i1, !F)",
      "\"exec.complete\"(%scope, %value) : (!S, !F)");
  auto begin = unconditional.find("    %test = \"runtime.take_condition\"");
  auto end = unconditional.find("  ^increment", begin);
  require(begin != std::string::npos && end != std::string::npos,
          "missing conditional-loop fixture section");
  unconditional.replace(begin, end - begin,
                        "    cf.br ^increment(%returned : !T)\n");
  cases.run("unconditional loop preserves the same carry lifecycle", [&] {
    auto model = read(unconditional, true);
    require(
        !model.functions.front().body.front().get<program::For>()->conditional,
        "unconditional loop gained an early decision");
  });
  auto variant = protocol::encodeVariant(
      {"ExecutionChoice",
       {{"left", {"field:koala-bear"}}, {"right", {"field:koala-bear"}}}});
  require(bool(variant), "variant fixture descriptor refused");
  auto matching = change(source, "module {",
                         "!V = !data.variant<\"" + *variant + "\">\nmodule {");
  begin = matching.find("    %tested = \"exec.test\"");
  end = matching.find("  ^yes:", begin);
  require(begin != std::string::npos && end != std::string::npos,
          "missing conditional fixture section");
  matching.replace(
      begin, end - begin,
      "    %constructed = \"exec.variant\"(%scope, %x) {site=\"construct\", "
      "alternative=\"left\"} : (!S, !F) -> !exec.outcome<(!V)>\n"
      "    \"exec.dispatch\"(%constructed)[^selected, ^failed] : "
      "(!exec.outcome<(!V)>) -> ()\n"
      "  ^selected(%choice: !V):\n"
      "    \"exec.match\"(%scope, %choice, %y)[^failed, ^yes, ^no] "
      "{site=\"choose\", alternatives=[\"left\", \"right\"]} : (!S, !V, !F) -> "
      "()\n");
  for (StringRef arm : {"yes", "no"}) {
    matching = change(matching, "^" + arm.str() + ":",
                      "^" + arm.str() + "(%payload_" + arm.str() +
                          ": !F, %capture_" + arm.str() + ": !F):");
    matching = change(matching,
                      "%entered_" + arm.str() +
                          " = \"runtime.enter_scope\"(%scope, %x, %y)",
                      "%entered_" + arm.str() +
                          " = \"runtime.enter_scope\"(%scope, %payload_" +
                          arm.str() + ", %capture_" + arm.str() + ")");
    matching =
        change(matching, "@" + arm.str() + "(%child_" + arm.str() + ", %x, %y)",
               "@" + arm.str() + "(%child_" + arm.str() + ", %payload_" +
                   arm.str() + ", %capture_" + arm.str() + ")");
  }
  matching = replaceAll(matching, "kind=\"conditional\"", "kind=\"match\"");
  matching = change(matching, "selection=\"then\"", "selection=\"left\"");
  matching = change(matching, "selection=\"else\"", "selection=\"right\"");
  cases.run(
      "variant dispatch exposes actual payload and unchanged captures", [&] {
        auto model = read(matching, true);
        auto &body = model.functions.front().body;
        auto construct = body[0].get<program::VariantConstruct>();
        auto match = body[1].get<program::Match>();
        require(
            construct && match && match->input == construct->output &&
                match->arms.size() == 2 && match->arms[0].payload.size() == 1 &&
                match->arms[0].body[0].get<program::Operation>()->inputs ==
                    program::Names{match->arms[0].payload[0],
                                   match->captures[0]},
            "selected variant payload was reconstructed from the wrong source");
      });
  cases.run("variant scope cannot substitute another equal-typed payload", [&] {
    read(change(matching, "@yes(%child_yes, %payload_yes, %capture_yes)",
                "@yes(%child_yes, %capture_yes, %payload_yes)"),
         false);
  });
  cases.run("variant frame selection must match actual arm", [&] {
    read(change(matching, "selection=\"left\"", "selection=\"right\""), false);
  });
  cases.run("physical ports retain the installed representation", [&] {
    auto physical =
        change(source, "!F = !algebra.field<\"koala-bear\">",
               "!F = !runtime.represented<!algebra.field<\"koala-bear\">, "
               "\"plonky3.koala-bear/0\">\n"
               "!P = !runtime.represented<i1, \"native.bool/0\">");
    physical = change(physical, "%condition: i1", "%condition: !P");
    physical = change(physical, ": (!S, i1) -> !D", ": (!S, !P) -> !D");
    physical = change(physical, "implementation=\"\"",
                      "implementation=\"plonky3/field.add\"");
    physical = change(physical, "implementation=\"\"",
                      "implementation=\"plonky3/field.mul\"");
    auto model = read(physical, true, true);
    require(model.functions.front().arguments[1].type ==
                "field:koala-bear@plonky3.koala-bear/0",
            "represented port was erased");
    read(physical, false, false);
  });
  auto shape = [&](StringRef name, StringRef operation) {
    cases.run(name, [&] {
      codes.clear();
      std::string text =
          "module { func.func @bad(%scope: !runtime.scope, %f: "
          "!algebra.field<\"koala-bear\">, %b: i1, %i: ui64, %raw: i64) {\n";
      text += operation.str() + "\nfunc.return\n} }";
      require(!parseSourceString<ModuleOp>(text, &context) &&
                  llvm::is_contained(codes, "execution-formation"),
              "malformed instruction bypassed formation check");
    });
  };
  shape("instruction cannot return a scope as ordinary data",
        "%r = \"exec.apply\"(%scope) {binding=@none, parameters=[], "
        "site=\"call\"} : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>");
  shape("native completion must preserve its payload",
        "%r = \"exec.complete\"(%scope, %b) : (!runtime.scope, i1) -> "
        "!exec.outcome<(ui64)>");
  shape("Boolean allocation requires a Boolean carrier",
        "%r = \"exec.boolean\"(%scope) {site=\"literal\", value=true} : "
        "(!runtime.scope) -> !exec.outcome<(ui64)>");
  shape("rejection cannot lose its occurrence",
        "%r = \"exec.reject\"(%scope) {site=\"\", reason=\"stop\"} : "
        "(!runtime.scope) -> !exec.stop");
  shape("conditional admission requires a Boolean input",
        "%r = \"exec.test\"(%scope, %i) {site=\"choose\"} : (!runtime.scope, "
        "ui64) -> !exec.outcome<(i1)>");
  shape("range admission cannot reinterpret field bounds",
        "%r = \"exec.range\"(%scope, %f, %f) {site=\"loop\"} : "
        "(!runtime.scope, !algebra.field<\"koala-bear\">, "
        "!algebra.field<\"koala-bear\">) -> !exec.outcome<(i64, i64)>");
  shape("iteration must allocate a native index",
        "%r = \"runtime.iteration\"(%scope, %raw) {site=\"loop\"} : "
        "(!runtime.scope, i64) -> !exec.outcome<(i1)>");
  shape("release cannot discard an execution scope",
        "\"runtime.release_bindings\"(%scope, %scope) : (!runtime.scope, "
        "!runtime.scope) -> ()");
  cases.run("variant payload API refuses a missing carrier", [&] {
    auto result = data::variantPayloadTypes(Type{}, "left");
    require(!result, "null variant carrier accepted");
    llvm::consumeError(result.takeError());
  });
  cases.run(
      "Boolean instruction keeps reached allocation before completion", [&] {
        auto model = read(R"mlir(module {
      func.func @literal(%scope: !runtime.scope) -> !exec.outcome<(i1)>
          attributes {no_inline, runtime.origin=["literal", []]} {
        %value = "exec.boolean"(%scope) {site="literal", value=true}
          : (!runtime.scope) -> !exec.outcome<(i1)>
        "exec.dispatch"(%value)[^done, ^failed] : (!exec.outcome<(i1)>) -> ()
      ^done(%b: i1):
        %r = "exec.complete"(%scope, %b) : (!runtime.scope, i1) -> !exec.outcome<(i1)>
        func.return %r : !exec.outcome<(i1)>
      ^failed(%cause: !exec.stop):
        %failure = "exec.failed"(%cause) : (!exec.stop) -> !exec.outcome<(i1)>
        func.return %failure : !exec.outcome<(i1)>
      }
    })mlir",
                          true);
        require(
            model.functions[0].body[0].get<program::BooleanConstant>()->value,
            "literal was replaced with an unmetered host constant");
      });
  cases.run("empty native return still has completion", [&] {
    auto model = read(R"mlir(module {
      func.func @empty(%scope: !runtime.scope) -> !exec.outcome<>
          attributes {no_inline, runtime.origin=["empty", []]} {
        %r = "exec.complete"(%scope) : (!runtime.scope) -> !exec.outcome<>
        func.return %r : !exec.outcome<>
      }
    })mlir",
                      true);
    require(model.functions[0].body[0].get<program::Return>()->values.empty(),
            "empty return lost its native completion");
  });
  cases.run(
      "reconstruction rechecks the current body after earlier success", [&] {
        auto module = parseSourceString<ModuleOp>(source, &context);
        require(bool(module), "freshness fixture did not parse");
        auto before = take(protocol::readLocalExecution(*module, false));
        module->walk([&](exec::ApplyOp apply) {
          apply.setBindingAttr(FlatSymbolRefAttr::get(&context, "multiply"));
        });
        auto after = take(protocol::readLocalExecution(*module, false));
        require(before.functions[0]
                            .body[0]
                            .get<program::Conditional>()
                            ->thenBody[0]
                            .get<program::Operation>()
                            ->callee == "add" &&
                    after.functions[0]
                            .body[0]
                            .get<program::Conditional>()
                            ->thenBody[0]
                            .get<program::Operation>()
                            ->callee == "multiply",
                "reconstruction reused a stale successful read");
      });
  return cases.result();
}
