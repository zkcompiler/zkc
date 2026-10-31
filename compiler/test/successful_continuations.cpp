#include "OracleQueryBlocks.h"
#include "mlir/IR/AsmState.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Interactions.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Analysis/SuccessfulContinuations.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include <string>

using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
namespace pir = protocol_ir;
using Status = SuccessfulContinuationAnalysis::Status;

std::string source(StringRef body, StringRef declarations = "") {
  return R"mlir(
!F = !algebra.field<"goldilocks.ext2-binomial7">
!D = !algebra.field_vector<"goldilocks.ext2-binomial7">
#K = #protocol.oracle_kind<"table", [!F,16:ui64]>
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64):
   "protocol.return"() : ()->()
 }) {sym_name="other",function_type=(ui64)->(),roles=["P","V"],
     input_roles=[["P","V"]],output_roles=[]} : ()->()
)mlir" + declarations.str() +
         R"mlir(
 "protocol.func"() ({
 ^entry(%data:!D,%position:ui64,%unrelated:ui64,%upper:ui64,%trips:ui64,%condition:i1):
   %rows = "data.index"() {value=16:ui64} : ()->ui64
   %eight = "data.index"() {value=8:ui64} : ()->ui64
   %wide = "data.index"() {value=32:ui64} : ()->ui64
   %zero = "data.index"() {value=0:ui64} : ()->ui64
   %one = "data.index"() {value=1:ui64} : ()->ui64
   %yes = arith.constant true
   %no = arith.constant false
   %word = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="word"} : (!D,ui64)->!H
)mlir" + body.str() +
         R"mlir(
   "protocol.return"() : ()->()
 }) {sym_name="subject",function_type=(!D,ui64,ui64,ui64,ui64,i1)->(),
     roles=["P","V"],input_roles=[["P"],["P","V"],["P","V"],["P","V"],["P","V"],["P","V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
const StringLiteral query = R"mlir(
 %answer = "protocol.oracle_query"(%word,%position) {owner="V",site="read"} : (!H,ui64)->!F
)mlir";
std::string less(StringRef lhs = "%position", StringRef rhs = "%rows") {
  return "%within = \"data.index_less\"(" + lhs.str() + "," + rhs.str() +
         ") : (ui64,ui64)->i1\n";
}
std::string guard(StringRef role = "V", StringRef condition = "%within",
                  StringRef site = "checked") {
  return "\"protocol.guard\"(" + condition.str() + ") {owner=\"" + role.str() +
         "\",site=\"" + site.str() + "\"} : (i1)->()\n";
}
std::string guardLoop(StringRef count) {
  return "\"protocol.repeat\"(" + count.str() + R"mlir(,%position,%rows) ({
 ^body(%i:ui64,%p:ui64,%r:ui64):
  %inside = "data.index_less"(%p,%r) : (ui64,ui64)->i1
  "protocol.guard"(%inside) {owner="V",site="inside_checked"} : (i1)->()
  "protocol.yield"() : ()->()
 }) {site="loop",carried=0:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64,ui64)->()
)mlir";
}
const StringLiteral nested = R"mlir(
 "protocol.repeat"(%trips,%position,%word,%rows,%trips) ({
 ^outer(%i:ui64,%p:ui64,%w:!H,%r:ui64,%n:ui64):
  "protocol.repeat"(%n,%p,%w,%r) ({
  ^inner(%j:ui64,%index:ui64,%handle:!H,%limit:ui64):
   %local_index = "protocol.restrict_roles"(%index) {roles=["V"]} : (ui64)->ui64
   %answer = "protocol.oracle_query"(%handle,%local_index) {owner="V",site="read"} : (!H,ui64)->!F
   "protocol.yield"() : ()->()
  }) {site="inner",carried=0:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64,!H,ui64)->()
  "protocol.yield"() : ()->()
 }) {site="outer",carried=0:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[]} : (ui64,ui64,!H,ui64,ui64)->()
)mlir";
std::string carried(bool checkBody) {
  return R"mlir(
 %last = "protocol.repeat"(%trips,%position,%word,%rows) ({
 ^body(%i:ui64,%current:ui64,%handle:!H,%limit:ui64):
)mlir" + (checkBody ? less("%current", "%limit") + guard() : "") +
         R"mlir(
  %answer = "protocol.oracle_query"(%handle,%current) {owner="V",site="read"} : (!H,ui64)->!F
  "protocol.yield"(%current) : (ui64)->()
 }) {site="loop",carried=1:i64,maximum=1048576:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,ui64,!H,ui64)->ui64
)mlir";
}
pir::MathematicalOp declaration(ModuleOp module, StringRef name = "subject") {
  auto unit = cast<pir::ProtocolModuleOp>(module.getBody()->front());
  auto result = SymbolTable(unit).lookup<pir::MathematicalOp>(name);
  require(bool(result), "missing fixture declaration");
  return result;
}
Operation *point(pir::MathematicalOp program, StringRef site = "read") {
  Operation *result = nullptr;
  program.walk([&](Operation *operation) {
    if (auto name = operation->getAttrOfType<StringAttr>("site");
        name && name.getValue() == site) {
      require(!result, "duplicate fixture site");
      result = operation;
    }
  });
  require(result != nullptr, "missing fixture point");
  return result;
}
Value rows(pir::MathematicalOp program) {
  return cast<pir::OracleSendOp>(point(program, "word"))
      .getShapeOperand("rows");
}
std::string print(Operation *operation) {
  std::string text;
  raw_string_ostream stream(text);
  operation->print(stream);
  return text;
}
Status observe(SuccessfulContinuationAnalysis &analysis,
               pir::MathematicalOp program, facts::Work &work,
               uint64_t upper = 16, StringRef participant = "V") {
  auto actual = cast<pir::OracleQueryOp>(point(program));
  return take(analysis.bound(program, actual, participant, actual.getPosition(),
                             upper, work));
}
} // namespace

int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    raw_string_ostream stream(diagnostics);
    diagnostic.print(stream);
    return success();
  });
  auto parse = [&](StringRef text) {
    diagnostics.clear();
    auto module =
        parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
    require(bool(module), "fixture did not parse: " + diagnostics);
    require(succeeded(admitStage(*module)),
            "fixture was not admitted: " + diagnostics);
    return module;
  };
  auto expects = [&](StringRef body, Status expected, uint64_t upper = 16) {
    auto module = parse(source(body));
    auto before = print(*module);
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(observe(analysis, declaration(*module), work, upper) == expected,
            "unexpected successful-point status");
    require(print(*module) == before,
            "analysis changed actual guards or operations");
  };
  Cases cases;
  cases.run("only a same-participant successful guard establishes the bound",
            [&] { expects(less() + guard() + query.str(), Status::Proven); });
  cases.run("a later guard does not establish a fact before the query",
            [&] { expects(query.str() + less() + guard(), Status::Unknown); });
  cases.run("computing the Boolean supplies no successful check",
            [&] { expects(less() + query.str(), Status::Unknown); });
  cases.run("another participant's guard supplies no successful check", [&] {
    expects(less() + guard("P") + query.str(), Status::Unknown);
  });
  cases.run("same-typed unrelated operands retain distinct identities", [&] {
    expects(less("%unrelated") + guard() + query.str(), Status::Unknown);
  });
  cases.run("the guard itself has not yet established its condition", [&] {
    auto module = parse(source(less() + guard() + query.str()));
    auto program = declaration(*module);
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(take(analysis.bound(program, point(program, "checked"), "V",
                                program.getBody().front().getArgument(1),
                                rows(program), work)) == Status::Unknown,
            "the query included its own guard occurrence");
  });
  cases.run("SSA upper bounds require the exact RHS", [&] {
    auto module =
        parse(source(less("%position", "%upper") + guard() + query.str()));
    auto program = declaration(*module);
    auto actual = cast<pir::OracleQueryOp>(point(program));
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(take(analysis.bound(program, actual, "V", actual.getPosition(),
                                program.getBody().front().getArgument(3),
                                work)) == Status::Proven,
            "exact SSA RHS was not recognized");
    require(take(analysis.bound(program, actual, "V", actual.getPosition(),
                                rows(program), work)) == Status::Unknown,
            "unrelated upper value supplied the RHS");
    require(observe(analysis, program, work) == Status::Unknown,
            "an unknown RHS became an exact integer");
  });
  cases.run(
      "constant weakening never substitutes SSA contents for identity", [&] {
        auto module =
            parse(source(less("%position", "%eight") + guard() + query.str()));
        auto program = declaration(*module);
        auto actual = cast<pir::OracleQueryOp>(point(program));
        SuccessfulContinuationAnalysis analysis(*module);
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        require(observe(analysis, program, work, 16) == Status::Proven &&
                    observe(analysis, program, work, 8) == Status::Proven &&
                    observe(analysis, program, work, 7) == Status::Unknown,
                "constant weakening used the wrong direction or strictness");
        require(take(analysis.bound(program, actual, "V", actual.getPosition(),
                                    rows(program), work)) == Status::Unknown,
                "equal/related integer contents replaced exact SSA identity");
      });
  cases.run("distinct equal integer constants do not merge SSA bounds", [&] {
    auto module = parse(source(R"mlir(
 %copy = "data.index"() {value=16:ui64} : ()->ui64
)mlir" + less("%position", "%copy") +
                               guard() + query.str()));
    auto program = declaration(*module);
    auto actual = cast<pir::OracleQueryOp>(point(program));
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(take(analysis.bound(program, actual, "V", actual.getPosition(),
                                rows(program), work)) == Status::Unknown &&
                observe(analysis, program, work) == Status::Proven,
            "literal equality became SSA identity");
  });
  cases.run("a larger checked RHS does not prove a smaller queried upper", [&] {
    expects(less("%position", "%wide") + guard() + query.str(),
            Status::Unknown);
  });
  cases.run("exact helper integers can weaken a guarded RHS", [&] {
    auto module = parse(source(R"mlir(
 %limit = func.call @fixed() : ()->ui64
)mlir" + less("%position", "%limit") +
                                   guard() + query.str(),
                               R"mlir(
 func.func private @fixed()->ui64 {
  %eight = "data.index"() {value=8:ui64} : ()->ui64
  %wide = "data.index"() {value=32:ui64} : ()->ui64
  func.return %eight : ui64
 }
)mlir"));
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(observe(analysis, declaration(*module), work) == Status::Proven,
            "exact mathematical helper result was not observed");
    auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
    auto fixed = SymbolTable(unit).lookup<func::FuncOp>("fixed");
    auto returned = cast<func::ReturnOp>(fixed.front().back());
    Value wide = returned->getPrevNode()->getResult(0);
    analysis.clear();
    returned->setOperand(0, wide);
    require(succeeded(admitStage(*module)), "changed helper was not admitted");
    require(observe(analysis, declaration(*module), work) == Status::Unknown,
            "a stale helper result survived clear before mutation");
  });
  cases.run("helper forwarding does not merge exact index identities", [&] {
    auto module = parse(source(R"mlir(
 %copy = func.call @identity(%position) : (ui64)->ui64
)mlir" + less("%copy") + guard() + query.str(),
                               R"mlir(
 func.func private @identity(%index:ui64)->ui64 {
  func.return %index : ui64
 }
)mlir"));
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(observe(analysis, declaration(*module), work) == Status::Unknown,
            "a helper result was normalized as exact SSA forwarding");
  });
  cases.run("a guarded helper Boolean supplies no interpreted Less fact", [&] {
    auto module = parse(source(R"mlir(
 %within = func.call @predicate(%position,%rows) : (ui64,ui64)->i1
)mlir" + guard() + query.str(),
                               R"mlir(
 func.func private @predicate(%index:ui64,%limit:ui64)->i1 {
  %inside = "data.index_less"(%index,%limit) : (ui64,ui64)->i1
  func.return %inside : i1
 }
)mlir"));
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(observe(analysis, declaration(*module), work) == Status::Unknown,
            "an opaque Boolean helper became a successful-point predicate");
  });
  cases.run("nested invariant captures and role restrictions preserve identity",
            [&] { expects(less() + guard() + nested.str(), Status::Proven); });
  cases.run(
      "SSA upper captures and enclosing iteration prefixes supply exact facts",
      [&] {
        auto body = nested.str();
        auto start = body.find("\"protocol.repeat\"(%n,");
        require(start != std::string::npos,
                "missing inner repeat fixture slot");
        body.insert(start, less("%p", "%r") + guard());
        auto module = parse(source(body));
        auto program = declaration(*module);
        auto actual = cast<pir::OracleQueryOp>(point(program));
        SuccessfulContinuationAnalysis analysis(*module);
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        require(take(analysis.bound(program, actual, "V", actual.getPosition(),
                                    actual->getBlock()->getArgument(3),
                                    work)) == Status::Proven,
                "an enclosing repeat prefix did not preserve invariant SSA "
                "operands");
      });
  cases.run("role-restricted conditions and RHS preserve exact identity", [&] {
    expects(R"mlir(
 %local_rows = "protocol.restrict_roles"(%rows) {roles=["V"]} : (ui64)->ui64
 %within = "data.index_less"(%position,%local_rows) : (ui64,ui64)->i1
 %local_condition = "protocol.restrict_roles"(%within) {roles=["V"]} : (i1)->i1
)mlir" + guard("V", "%local_condition") +
                query.str(),
            Status::Proven);
  });
  cases.run(
      "a carried initializer does not describe the current iteration",
      [&] { expects(less() + guard() + carried(false), Status::Unknown); });
  cases.run("a guard on the actual carried argument applies in this iteration",
            [&] { expects(carried(true), Status::Proven); });
  for (StringRef count : {"%zero", "%too_many"}) {
    cases.run("an unreached loop body supplies no positive bound: " + count,
              [&] {
                auto body = carried(true);
                body.replace(body.find("%trips"), StringRef("%trips").size(),
                             count.str());
                expects("%too_many = \"data.index\"() {value=1048577:ui64} : "
                        "()->ui64\n" +
                            body,
                        Status::Unreachable);
              });
  }
  cases.run(
      "a value from an exited repeat cannot name a current occurrence", [&] {
        auto module =
            parse(source(less() + guard() + guardLoop("%one") + query.str()));
        auto program = declaration(*module);
        auto loop = cast<pir::RepeatOp>(point(program, "loop"));
        auto actual = cast<pir::OracleQueryOp>(point(program));
        SuccessfulContinuationAnalysis analysis(*module);
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        require(take(analysis.bound(program, actual, "V",
                                    loop.getBody().front().getArgument(1),
                                    uint64_t(16), work)) == Status::Unknown,
                "capture normalization imported an expired iteration");
      });
  for (StringRef count : {"%zero", "%one", "%trips"}) {
    cases.run("body guards do not escape a repeat with count " + count, [&] {
      expects(guardLoop(count) + query.str(), Status::Unknown);
    });
  }
  cases.run("a failed guard after a matching bound is Unreachable", [&] {
    expects(less() + guard() + guard("V", "%no", "stop") + query.str(),
            Status::Unreachable);
  });
  cases.run("a literal true finish is Unreachable, not an arbitrary proof",
            [&] {
              expects(less() + guard() + R"mlir(
 "protocol.finish_if"(%yes) {owner="V",site="stop"} : (i1)->()
)mlir" + query.str(),
                      Status::Unreachable);
            });
  cases.run("other-participant stops and unknown finishes add no facts", [&] {
    expects(guard("P", "%no", "stop") + query.str(), Status::Unknown);
    expects(R"mlir(
 "protocol.finish_if"(%condition) {owner="V",site="stop"} : (i1)->()
)mlir" + query.str(),
            Status::Unknown);
    expects(less() + guard() + R"mlir(
 "protocol.finish_if"(%condition) {owner="V",site="stop"} : (i1)->()
)mlir" + query.str(),
            Status::Proven);
  });
  cases.run("the outer prefix stop dominates a nested successful guard", [&] {
    expects(guard("V", "%no", "stop") + less() + guard() + nested.str(),
            Status::Unreachable);
  });
  cases.run("unexpanded applications supply no caller facts", [&] {
    auto module = parse(source(R"mlir(
 protocol.apply @checked(%position,%rows) {roles=["P","V"],site="call"} : (ui64,ui64)->()
)mlir" + query.str(),
                               R"mlir(
 "protocol.func"() ({ ^entry(%index:ui64,%limit:ui64):
  %inside = "data.index_less"(%index,%limit) : (ui64,ui64)->i1
  "protocol.guard"(%inside) {owner="V",site="callee_check"} : (i1)->()
  "protocol.return"() : ()->()
 }) {sym_name="checked",function_type=(ui64,ui64)->(),roles=["P","V"],input_roles=[["P","V"],["P","V"]],output_roles=[]} : ()->()
)mlir"));
    SuccessfulContinuationAnalysis analysis(*module);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(observe(analysis, declaration(*module), work) == Status::Unknown,
            "a callee guard became a caller premise");
  });
  cases.run(
      "values, points and participant must belong to the exact subject", [&] {
        auto module = parse(source(less() + guard() + query.str()));
        auto program = declaration(*module);
        auto other = declaration(*module, "other");
        auto actual = cast<pir::OracleQueryOp>(point(program));
        SuccessfulContinuationAnalysis analysis(*module);
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        require(take(analysis.bound(program, actual, "V",
                                    other.getBody().front().getArgument(0),
                                    rows(program), work)) == Status::Unknown,
                "another declaration's formal supplied the index");
        require(take(analysis.bound(program, actual, "V", actual.getPosition(),
                                    other.getBody().front().getArgument(0),
                                    work)) == Status::Unknown,
                "another declaration's formal supplied the upper");
        require(take(analysis.bound(other, actual, "V", actual.getPosition(),
                                    uint64_t(16), work)) == Status::Unknown,
                "a foreign declaration point was accepted");
        require(observe(analysis, program, work, 16, "absent") ==
                    Status::Unknown,
                "an undeclared participant supplied successful evidence");
        require(take(analysis.bound(program, rows(program).getDefiningOp(), "V",
                                    actual.getPosition(), uint64_t(16),
                                    work)) == Status::Unknown,
                "a mathematical expression became a Protocol action point");
      });
  cases.run(
      "fresh and cloned modules require independent analysis instances", [&] {
        auto module = parse(source(less() + guard() + query.str()));
        auto fresh = parse(source(less() + guard() + query.str()));
        OwningOpRef<ModuleOp> clone(cast<ModuleOp>(module->clone()));
        require(succeeded(admitStage(*clone)), "clone was not admitted");
        SuccessfulContinuationAnalysis original(*module);
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        require(original.getOwner() == module->getOperation(),
                "wrong module owner");
        for (ModuleOp candidate : {fresh.get(), clone.get()}) {
          auto program = declaration(candidate);
          auto actual = cast<pir::OracleQueryOp>(point(program));
          refuses(original.bound(program, actual, "V", actual.getPosition(),
                                 uint64_t(16), work),
                  "interaction-analysis-owner");
          SuccessfulContinuationAnalysis separate(candidate);
          require(observe(separate, program, work) == Status::Proven,
                  "independent candidate could not establish its own bound");
          require(take(original.bound(declaration(*module), actual, "V",
                                      actual.getPosition(), uint64_t(16),
                                      work)) == Status::Unknown,
                  "a clone's point crossed source identity");
        }
        SuccessfulContinuationAnalysis local(declaration(*module));
        auto program = declaration(*module);
        auto actual = cast<pir::OracleQueryOp>(point(program));
        refuses(local.bound(program, actual, "V", actual.getPosition(),
                            uint64_t(16), work),
                "interaction-analysis-owner");
      });
  cases.run("clear before mutation expires cached structural and fact views",
            [&] {
              auto module = parse(source(less() + guard() + query.str()));
              auto program = declaration(*module);
              SuccessfulContinuationAnalysis analysis(*module);
              uint64_t remaining = 100000;
              facts::Work work(remaining);
              require(observe(analysis, program, work) == Status::Proven,
                      "missing initial bound");
              auto check = cast<pir::GuardOp>(point(program, "checked"));
              analysis.clear();
              check->erase();
              require(succeeded(admitStage(*module)),
                      "changed fixture was not admitted");
              require(observe(analysis, program, work) == Status::Unknown,
                      "erased guard survived clear and mutation");
              analysis.clear();
              require(observe(analysis, program, work) == Status::Unknown,
                      "repeated clearing replenished facts");
            });
  cases.run(
      "AnalysisManager tracks structural, mathematical and symbol dependencies",
      [&] {
        auto module = parse(source(less() + guard() + query.str()));
        auto program = declaration(*module);
        ModuleAnalysisManager storage(*module, nullptr);
        AnalysisManager manager = storage;
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        require(observe(manager.getAnalysis<SuccessfulContinuationAnalysis>(),
                        program, work) == Status::Proven,
                "managed analysis missed a bound");
        require(
            manager.getCachedAnalysis<InteractionAnalysis>().has_value() &&
                manager.getCachedAnalysis<MathematicalFactAnalysis>()
                    .has_value() &&
                manager.getCachedAnalysis<SymbolClosureAnalysis>().has_value(),
            "module dependencies were not registered");
        AnalysisManager::PreservedAnalyses all;
        all.preserve<SuccessfulContinuationAnalysis>();
        all.preserve<InteractionAnalysis>();
        all.preserve<MathematicalFactAnalysis>();
        all.preserve<SymbolClosureAnalysis>();
        manager.invalidate(all);
        require(manager.getCachedAnalysis<SuccessfulContinuationAnalysis>()
                    .has_value(),
                "immutable managed view was not preserved");
        for (unsigned missing = 0; missing < 4; ++missing) {
          AnalysisManager::PreservedAnalyses partial;
          if (missing != 0)
            partial.preserve<SuccessfulContinuationAnalysis>();
          if (missing != 1)
            partial.preserve<InteractionAnalysis>();
          if (missing != 2)
            partial.preserve<MathematicalFactAnalysis>();
          if (missing != 3)
            partial.preserve<SymbolClosureAnalysis>();
          manager.invalidate(partial);
          require(
              !manager.getCachedAnalysis<SuccessfulContinuationAnalysis>(),
              "an invalidated dependency left a successful-point view cached");
          require(observe(manager.getAnalysis<SuccessfulContinuationAnalysis>(),
                          program, work) == Status::Proven,
                  "invalidated view could not be reconstructed");
        }
        manager.invalidate(AnalysisManager::PreservedAnalyses{});
        point(program, "checked")->erase();
        require(succeeded(admitStage(*module)),
                "mutated fixture was not admitted");
        require(observe(manager.getAnalysis<SuccessfulContinuationAnalysis>(),
                        program, work) == Status::Unknown,
                "invalidated guard evidence survived mutation");
      });
  cases.run("cold and warm queries debit the same cumulative caller Work", [&] {
    auto module = parse(source(less() + guard() + nested.str()));
    auto program = declaration(*module);
    SuccessfulContinuationAnalysis warm(*module);
    uint64_t first = 100000, second = 100000;
    facts::Work firstWork(first), secondWork(second);
    require(observe(warm, program, firstWork) == Status::Proven &&
                observe(warm, program, secondWork) == Status::Proven &&
                first == second && first < 100000,
            "cache warmth changed the query allowance");
    uint64_t cost = 100000 - first;
    for (uint64_t budget : {uint64_t(0), uint64_t(1), cost - 1}) {
      SuccessfulContinuationAnalysis cold(*module);
      uint64_t a = budget, b = budget;
      facts::Work coldWork(a), warmWork(b);
      require(observe(cold, program, coldWork) == Status::Capacity &&
                  observe(warm, program, warmWork) == Status::Capacity &&
                  a == b && coldWork.exhausted() && warmWork.exhausted(),
              "exhausted shared work became a proof or a fresh allowance");
      b = 100000;
      require(observe(warm, program, warmWork) == Status::Capacity &&
                  b == 100000,
              "an exhausted Work object was replenished");
    }
    uint64_t remaining = cost * 2;
    facts::Work cumulative(remaining);
    require(observe(warm, program, cumulative) == Status::Proven &&
                observe(warm, program, cumulative) == Status::Proven &&
                remaining == 0 && !cumulative.exhausted(),
            "queries did not share their cumulative allowance");
    require(observe(warm, program, cumulative) == Status::Capacity,
            "a third query escaped the cumulative allowance");
  });
  cases.run("structural and forwarding limits produce sticky Capacity", [&] {
    auto module = parse(source(less() + guard() + nested.str()));
    auto program = declaration(*module);
    for (auto limits : {SuccessfulContinuationAnalysis::Limits{1, 100000},
                        SuccessfulContinuationAnalysis::Limits{64, 2}}) {
      SuccessfulContinuationAnalysis limited(*module, limits);
      uint64_t remaining = 100000;
      facts::Work work(remaining);
      require(observe(limited, program, work) == Status::Capacity &&
                  work.exhausted(),
              "structural limit was ordinary absence");
    }
    std::string chain = less() + guard();
    std::string previous = "%position";
    for (unsigned i = 0; i < 65; ++i) {
      auto next = "%view" + std::to_string(i);
      chain += next + " = \"protocol.restrict_roles\"(" + previous +
               ") {roles=[\"V\"]} : (ui64)->ui64\n";
      previous = next;
    }
    chain += "%answer = \"protocol.oracle_query\"(%word," + previous +
             ") {owner=\"V\",site=\"read\"} : (!H,ui64)->!F\n";
    auto forwarded = parse(source(chain));
    SuccessfulContinuationAnalysis analysis(*forwarded);
    uint64_t remaining = 100000;
    facts::Work work(remaining);
    require(observe(analysis, declaration(*forwarded), work) ==
                    Status::Capacity &&
                work.exhausted(),
            "invariant forwarding depth was not sticky capacity");
  });
  for (StringRef mode :
       {"guarded", "before", "unchecked", "other-role", "unrelated", "wide",
        "nested", "carried", "post-repeat", "stopped", "finished",
        "dynamic-exact", "dynamic-bound"}) {
    cases.run("production direct-query consumer: " + mode, [&] {
      std::string body = less() + guard() + query.str();
      bool expected =
          mode == "guarded" || mode == "nested" || mode == "dynamic-exact";
      if (mode == "before")
        body = query.str() + less() + guard();
      else if (mode == "unchecked")
        body = less() + query.str();
      else if (mode == "other-role")
        body = less() + guard("P") + query.str();
      else if (mode == "unrelated")
        body = less("%unrelated") + guard() + query.str();
      else if (mode == "wide")
        body = less("%position", "%wide") + guard() + query.str();
      else if (mode == "nested")
        body = less() + guard() + nested.str();
      else if (mode == "carried")
        body = less() + guard() + carried(false);
      else if (mode == "post-repeat")
        body = guardLoop("%zero") + query.str();
      else if (mode == "stopped")
        body = less() + guard() + guard("V", "%no", "stop") + query.str();
      else if (mode == "finished")
        body = less() + guard() + R"mlir(
 "protocol.finish_if"(%yes) {owner="V",site="stop"} : (i1)->()
)mlir" + query.str();
      auto text = source(body);
      auto replace = [&](StringRef before, StringRef after) {
        auto at = text.find(before);
        require(at != std::string::npos, "missing production fixture slot");
        text.replace(at, before.size(), after);
      };
      if (mode.starts_with("dynamic-")) {
        replace("[!F,16:ui64]", "[!F]");
        replace("shape_bounds={}", "shape_bounds={rows=16:ui64}");
        if (mode == "dynamic-bound")
          replace("(%data,%rows)", "(%data,%upper)");
      }
      auto module = parse(text);
      auto program = declaration(*module);
      auto actual = cast<pir::OracleQueryOp>(point(program));
      auto frozen = print(*module);
      auto storage = take(protocol::planOracleAnchorStorage(
          *module, "subject", [](const auto &) -> Expected<std::string> {
            return std::string(
                "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0");
          }));
      unsigned remaining = 100000;
      auto result =
          take(protocol::admitOracleDirectQuery(actual, storage, remaining));
      require(bool(result) == expected, "incorrect direct-query admission");
      if (result)
        require(
            result->operation == actual && result->rows == 16 &&
                !result->literal &&
                result->position == program.getBody().front().getArgument(1),
            "direct query lost exact occurrence, extent or position identity");
      require(print(*module) == frozen,
              "direct admission changed actual source operations");
      unsigned used = 100000 - remaining;
      unsigned limited = used - 1;
      refuses(protocol::admitOracleDirectQuery(actual, storage, limited),
              "oracle-query-block-limit");
      unsigned empty = 0;
      refuses(protocol::admitOracleDirectQuery(actual, storage, empty),
              "oracle-query-block-limit");
    });
  }
  cases.run(
      "direct-query custody and concrete scheme requirements remain unchanged",
      [&] {
        auto module = parse(source(less() + guard() + query.str()));
        auto program = declaration(*module);
        auto actual = cast<pir::OracleQueryOp>(point(program));
        auto storage = take(protocol::planOracleAnchorStorage(
            *module, "subject", [](const auto &) -> Expected<std::string> {
              return std::string();
            }));
        unsigned remaining = 100000;
        require(
            !take(protocol::admitOracleDirectQuery(actual, storage, remaining)),
            "guard evidence admitted an ideal table as a concrete opening");
        require(storage.constructors.size() == 1,
                "unexpected source constructor count");
        storage.constructors.front().scheme =
            "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0";
        storage.constructors.front().holder = "V";
        require(
            !take(protocol::admitOracleDirectQuery(actual, storage, remaining)),
            "guard evidence bypassed the existing holder check");
      });
  cases.run(
      "virtual definitions supply structure but no participant facts", [&] {
        auto module = parse(source("", R"mlir(
 relation.declare @admissible {kind="external",key="test/successful-point",revision="0",
   signature=(!D)->i1,purposes=["witness"]}
 "protocol.oracle"() ({ ^entry(%word:!H,%position:ui64):
   %answer = "protocol.oracle_query"(%word,%position) {site="read"} : (!H,ui64)->!F
   "protocol.oracle_yield"(%answer) : (!F)->()
 }) {sym_name="virtual_word",function_type=(!H,ui64)->!F,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
)mlir"));
        auto unit = cast<pir::ProtocolModuleOp>(module->getBody()->front());
        auto definition =
            SymbolTable(unit).lookup<pir::OracleDefinitionOp>("virtual_word");
        auto query =
            cast<pir::OracleQueryOp>(definition.getBody().front().front());
        uint64_t remaining = 100000;
        facts::Work work(remaining);
        InteractionAnalysis interactions(*module);
        auto *view = take(interactions.get(definition, work));
        require(view->getActions().size() == 2 &&
                    view->getActions()[0].getOperation() == query,
                "virtual declaration lost its ordered actual query");
        SuccessfulContinuationAnalysis analysis(*module);
        require(take(analysis.bound(definition, query, "V", query.getPosition(),
                                    uint64_t(16), work)) == Status::Unknown,
                "virtual definition acquired a Protocol participant scope");
      });
  return cases.result();
}
