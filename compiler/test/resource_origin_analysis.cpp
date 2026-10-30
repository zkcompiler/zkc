#include "../lib/Dialect/Protocol/IR/ResourceOrigins.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "support/ResourceSources.h"
#include "support/ScopedFixture.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Mathematical.h"
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
std::string source(StringRef body = "", unsigned captures = 0,
                   StringRef definitions = "", StringRef yielded = "%r") {
  std::string args, nestedArgs, inputs, types, roles;
  for (unsigned i = 0; i < captures; ++i) {
    args += ",%c" + std::to_string(i) + ":i1";
    nestedArgs += ",%k" + std::to_string(i) + ":i1";
    inputs += ",%c" + std::to_string(i);
    types += ",i1";
    roles += ",[\"P\"]";
  }
  return "!s = !runtime.capability<rng, \"bls12-381.fr\">\n"
         "module { \"protocol.module\"() ({" +
         definitions.str() + "\"protocol.func\"() ({ ^entry(%n:ui64,%s:!s" +
         args +
         "):\n"
         "%done = \"protocol.repeat\"(%n,%s" +
         inputs +
         ") ({\n"
         "^body(%i:ui64,%r:!s" +
         nestedArgs + "):\n" + body.str() + "\"protocol.yield\"(" +
         yielded.str() +
         ") : (!s)->()\n"
         "}) {site=\"loop\",carried=1:i64,maximum=8:i64,roles=[\"P\"],"
         "carried_roles=[[\"P\"]]} : (ui64,!s" +
         types +
         ")->!s\n"
         "\"protocol.return\"(%done) : (!s)->()\n"
         "}) {sym_name=\"main\",function_type=(ui64,!s" +
         types +
         ")->!s,"
         "roles=[\"P\"],input_roles=[[\"P\"],[\"P\"]" +
         roles +
         "],"
         "output_roles=[[\"P\"]]} : ()->()\n"
         "}) {profile=#protocol.profile<protocol>} : ()->() }";
}
std::string definitions(resource_sources::Source &source) {
  std::string text;
  llvm::raw_string_ostream out(text);
  for (auto &op : source.owner.getBody().front()) {
    op.print(out);
    out << "\n";
  }
  return text;
}
std::string scopedChain(unsigned length, bool twice = false) {
  resource_sources::Source source;
  for (unsigned i = 0; i < length; ++i) {
    auto function =
        source.function("f" + std::to_string(i), source.rng, source.rng);
    exec::ScopedExecutionBuilder control(source.builder, function);
    Value result = function.getArgument(1);
    if (i) {
      result = source.call(control, "f" + std::to_string(i - 1), result,
                           source.rng, "first")[0];
      if (twice)
        result = source.call(control, "f" + std::to_string(i - 1), result,
                             source.rng, "second")[0];
    }
    control.returned(result);
  }
  return definitions(source);
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostic;
  ScopedDiagnosticHandler handler(&context, [&](Diagnostic &d) {
    llvm::raw_string_ostream stream(diagnostic);
    d.print(stream);
    return success();
  });
  auto query = [&](StringRef text, uint64_t work, unsigned depth, bool accepted,
                   bool verified = true,
                   StringRef refusal = "mathematical-analysis-limit") {
    diagnostic.clear();
    auto module =
        parseSourceString<ModuleOp>(text, ParserConfig(&context, verified));
    require(bool(module), "invalid analysis fixture: " + diagnostic);
    protocol_ir::RepeatOp repeat;
    module->walk([&](protocol_ir::RepeatOp op) { repeat = op; });
    require(bool(repeat), "missing repeat");
    SymbolTableCollection symbols;
    mathematical::NativeTypePolicies types(*module);
    mathematical::ResourceOrigins origins(symbols, types, work, depth);
    bool result = succeeded(origins.verify(repeat));
    require(result == accepted, "unexpected origin result: " + diagnostic);
    if (!accepted)
      require(diagnostic.find(refusal.str()) != std::string::npos,
              "limit reported as root mismatch: " + diagnostic);
  };
  cases.run("exact work charge and exhaustion", [&] {
    // Two block arguments plus one yield operation with one operand.
    query(source(), 4, 64, true);
    query(source(), 3, 64, false);
    query(source(), 100000, 0, false);
  });
  cases.run("copyable signature scans are charged", [&] {
    query(source("", 200), 204, 64, true);
    query(source("", 200), 203, 64, false);
  });
  cases.run("production work boundary and one over", [&] {
    std::string body;
    for (unsigned i = 0; i < 49998; ++i)
      body += "%unused" + std::to_string(i) +
              " = \"data.index\"() {value=0 : ui64} : ()->ui64\n";
    // Independently valid body shapes. Isolate this query from availability and
    // other formation limits; those have their own end-to-end controls.
    query(source(body), 100000, 64, true, false);
    query(source(body, 1), 100000, 64, false, false);
  });
  cases.run("no affine obligation spends no origin work", [&] {
    std::string text = source();
    auto alias = text.find("!runtime.capability<rng, \"bls12-381.fr\">");
    text.replace(
        alias, std::string("!runtime.capability<rng, \"bls12-381.fr\">").size(),
        "i1");
    query(text, 0, 0, true);
  });
  cases.run("cached callee depth cannot hide nested calls", [&] {
    auto chain = [&](unsigned length, bool warmFirst) {
      auto definitions = scopedChain(length);
      std::string shallow =
          "%warm = \"protocol.local_call\"(%r) "
          "{callee=@f0,role=\"P\",site=\"warm\"} : (!s)->!s\n";
      std::string deep = "%deep = \"protocol.local_call\"(%warm) {callee=@f" +
                         std::to_string(length - 1) +
                         ",role=\"P\",site=\"deep\"} : (!s)->!s\n";
      if (warmFirst)
        return source(shallow + deep, 0, definitions, "%deep");
      deep.replace(deep.find("(%warm)"), 7, "(%r)");
      shallow.replace(shallow.find("(%r)"), 4, "(%deep)");
      return source(deep + shallow, 0, definitions, "%warm");
    };
    for (bool warmFirst : {true, false}) {
      query(chain(63, warmFirst), 100000, 64, true, false);
      query(chain(64, warmFirst), 100000, 64, false, false);
    }
  });
  cases.run("per-program analysis accepts a verified module", [&] {
    auto module = parseSourceString<ModuleOp>(source(), &context);
    require(bool(module), "formed query fixture refused");
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(&module->getBody()->front());
    require(succeeded(mathematical::verifyModule(unit)), "module verification");
    SymbolTableCollection symbols;
    mathematical::Availability availability;
    for (auto program :
         unit.getBody().front().getOps<protocol_ir::MathematicalOp>())
      require(succeeded(mathematical::analyze(program, availability, symbols)),
              "per-program analysis disagrees");
  });
  cases.run("per-program analysis accepts every verified composition", [&] {
    for (StringRef name : {"if", "for", "match", "apply", "execution"}) {
      diagnostic.clear();
      resource_sources::Source source;
      if (name == "execution")
        resource_sources::execution(source, name);
      else
        resource_sources::simple(source, name, false);
      auto text = std::string();
      llvm::raw_string_ostream stream(text);
      source.module->print(stream);
      auto module = parseSourceString<ModuleOp>(text, &context);
      require(bool(module), "composed module refused: " + diagnostic);
      auto unit =
          cast<protocol_ir::ProtocolModuleOp>(&module->getBody()->front());
      require(succeeded(mathematical::verifyModule(unit)),
              "module verification");
      SymbolTableCollection symbols;
      mathematical::Availability availability;
      for (auto program :
           unit.getBody().front().getOps<protocol_ir::MathematicalOp>())
        require(
            succeeded(mathematical::analyze(program, availability, symbols)),
            "composed per-program query disagrees: " + diagnostic);
    }
  });
  cases.run("one invocation shares work across demanded queries", [&] {
    auto module = parseSourceString<ModuleOp>(source(), &context);
    require(bool(module), "formed query fixture refused");
    protocol_ir::RepeatOp repeat;
    module->walk([&](protocol_ir::RepeatOp op) { repeat = op; });
    SymbolTableCollection symbols;
    mathematical::NativeTypePolicies types(*module);
    mathematical::ResourceOrigins origins(symbols, types, 7);
    require(succeeded(origins.verify(repeat)), "first query");
    diagnostic.clear();
    require(failed(origins.verify(repeat)),
            "queries reset the shared work budget");
    require(diagnostic.find("mathematical-analysis-limit") != std::string::npos,
            "aggregate work is not a semantic root mismatch");
  });
  cases.run("repeated acyclic calls reuse formal summaries", [&] {
    auto definitions = scopedChain(30, true);
    // Linear analysis of the authored DAG; ordinary expansion refuses this
    // exponentially large executable using its separate formation limit.
    auto text = source("%out = \"protocol.local_call\"(%r) "
                       "{callee=@f29,role=\"P\",site=\"dag\"} : (!s)->!s\n",
                       0, definitions, "%out");
    // Seven common visits, thirty declaration entries, five visits for the
    // identity, sixteen per added two-call function and one returned root.
    // Native SSA charges both port visits and each call substitution.
    query(text, 507, 64, true, false);
    query(text, 506, 64, false, false);
  });
  cases.run("common calls without affine results need no callee summary", [&] {
    resource_sources::Source scoped;
    auto function = scoped.function("large", {}, {});
    exec::ScopedExecutionBuilder control(scoped.builder, function);
    for (unsigned i = 0; i < 100; ++i)
      control.invoke("exec.boolean", scoped.boolean, control.scoped({}),
                     {scoped.text("site", "v" + std::to_string(i)),
                      scoped.builder.getNamedAttr(
                          "value", scoped.builder.getBoolAttr(true))});
    control.returned({});
    auto definitions = ::definitions(scoped);
    // The copyable body is still formed by ordinary verification. It does not
    // provide a root or common continuation and is outside this query's work.
    auto text = source("\"protocol.local_call\"() "
                       "{callee=@large,role=\"P\",site=\"large\"} : ()->()\n",
                       0, definitions);
    query(text, 5, 64, true);
    query(text, 4, 64, false);
  });
  cases.run("forward callee shape is checked before origin summaries", [&] {
    std::string child = source();
    auto begin = child.find("\"protocol.func\"");
    child = child.substr(begin, child.find("}) {profile=") - begin);
    child.replace(child.find("sym_name=\"main\""), 15, "sym_name=\"child\"");
    auto text =
        source("%out = \"protocol.apply\"(%i,%r) "
               "{callee=@child,roles=[\"P\"],site=\"child\"} : (ui64,!s)->!s\n",
               0, "", "%out");
    text.insert(text.find("}) {profile="), child);
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "forward application fixture: " + diagnostic);
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(&module->getBody()->front());
    protocol_ir::RepeatOp nested;
    auto callee = *std::next(
        unit.getBody().front().getOps<protocol_ir::MathematicalOp>().begin());
    callee.walk([&](protocol_ir::RepeatOp op) { nested = op; });
    require(bool(nested), "missing callee repeat");
    nested->setOperands(ValueRange{});
    diagnostic.clear();
    require(failed(mathematical::verifyModule(unit)),
            "unformed callee admitted");
    require(
        diagnostic.find("invalid repeat count, bound or carried interface") !=
            std::string::npos,
        "origin analysis displaced the callee formation diagnostic: " +
            diagnostic);
  });
  cases.run("scoped loop shape is checked before origin summaries", [&] {
    diagnostic.clear();
    resource_sources::Source scoped;
    resource_sources::simple(scoped, "for", false);
    std::string text;
    llvm::raw_string_ostream stream(text);
    scoped.module->print(stream);
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "scoped loop fixture: " + diagnostic);
    auto unit =
        cast<protocol_ir::ProtocolModuleOp>(&module->getBody()->front());
    exec::RangeOp range;
    module->walk([&](exec::RangeOp op) { range = op; });
    require(bool(range), "missing scoped range");
    // A malformed result is an ordinary source-profile failure before roots.
    range.getOutcome().setType(
        exec::OutcomeType::get(&context, {IntegerType::get(&context, 1)}));
    diagnostic.clear();
    require(failed(mathematical::verifyModule(unit)),
            "unformed scoped range admitted");
    require(diagnostic.find("execution-formation") != std::string::npos,
            "origin query bypassed scoped range formation: " + diagnostic);
  });
  cases.run("structured region nesting has its own depth boundary", [&] {
    // Native source admission does not inherit the byte carrier's JSON array
    // depth. The consumer's origin nesting remains its independent ceiling.
    for (unsigned depth : {10u, 11u, 29u, 30u}) {
      resource_sources::Source scoped;
      auto outer =
          scoped.function("nested", {scoped.rng, scoped.boolean}, scoped.rng);
      auto nested = [&](auto &self, func::FuncOp function,
                        unsigned remaining) -> void {
        exec::ScopedExecutionBuilder control(scoped.builder, function);
        Value result = function.getArgument(1);
        if (remaining)
          result = control.conditional(
              function.getArgument(2), function.getArguments().drop_front(),
              scoped.rng, "branch" + std::to_string(remaining),
              [&](unsigned arm) {
                auto body =
                    scoped.region({scoped.rng, scoped.boolean}, scoped.rng);
                self(self, body, arm ? 0 : remaining - 1);
                return body;
              })[0];
        if (function == outer)
          control.returned(result);
        else
          control.complete(result);
      };
      nested(nested, outer, depth);
      auto definitions = ::definitions(scoped);
      auto text =
          source("%out = \"protocol.local_call\"(%r,%k0) "
                 "{callee=@nested,role=\"P\",site=\"nested\"} : (!s,i1)->!s\n",
                 1, definitions, "%out");
      query(text, 100000, depth <= 11 ? 12 : 64, depth != 11, false,
            "mathematical-analysis-limit");
    }
  });
  cases.run(
      "private summary cycles are formation errors rather than limits", [&] {
        auto text =
            source("%out = \"protocol.local_call\"(%r) "
                   "{callee=@cycle,role=\"P\",site=\"cycle\"} : (!s)->!s\n",
                   0,
                   R"mlir(
func.func @cycle(%scope:!runtime.scope,%x:!s)->!exec.outcome<(!s)> attributes {no_inline,runtime.origin=["cycle",[]]} {
  %next = func.call @cycle(%scope,%x) {runtime.site="again"} : (!runtime.scope,!s)->!exec.outcome<(!s)>
  "exec.dispatch"(%next)[^next,^failed] : (!exec.outcome<(!s)>)->()
^next(%out:!s):
  %done = "exec.returned"(%out) : (!s)->!exec.outcome<(!s)>
  func.return %done : !exec.outcome<(!s)>
^failed(%reason:!exec.stop):
  %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!s)>
  func.return %failure : !exec.outcome<(!s)>
}
)mlir",
                   "%out");
        diagnostic.clear();
        auto module =
            parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
        require(bool(module), "cycle fixture must parse");
        protocol_ir::RepeatOp repeat;
        module->walk([&](protocol_ir::RepeatOp op) { repeat = op; });
        SymbolTableCollection symbols;
        mathematical::NativeTypePolicies types(*module);
        mathematical::ResourceOrigins origins(symbols, types);
        require(failed(origins.verify(repeat)),
                "cycle accepted by isolated analysis");
        require(diagnostic.find("execution-call-cycle") != std::string::npos &&
                    diagnostic.find("mathematical-analysis-limit") ==
                        std::string::npos,
                "cycle hidden by limit diagnostic: " + diagnostic);
      });
  return cases.result();
}
