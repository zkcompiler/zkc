#include "../lib/Transforms/OracleQueryBlocks.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::protocol;
namespace pir = zkc::protocol_ir;
namespace {
std::string source(StringRef second = "%position", StringRef between = "",
                   StringRef owner = "V") {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [ui64,16:ui64]>
!H = !protocol.oracle<#K>
!D = !algebra.indices
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%data:!D,%position:ui64):
  %rows = "data.index"() {value=16:ui64} : ()->ui64
  %word = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V","W"],shape_names=["rows"],shape_bounds={},site="word"} : (!D,ui64)->!H
  %a = "protocol.oracle_query"(%word,%position) {owner="V",site="first"} : (!H,ui64)->ui64
)mlir" + between.str() + R"mlir(
  %b = "protocol.oracle_query"(%word,)mlir" + second.str() +
         R"mlir() {owner=")mlir" + owner.str() + R"mlir(",site="second"} : (!H,ui64)->ui64
  "protocol.return"(%a) : (ui64)->()
 }) {sym_name="main",function_type=(!D,ui64)->ui64,roles=["P","V","W"],input_roles=[["P"],["V","W"]],output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  std::string diagnostic;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    diagnostic += message.str();
    return success();
  });
  auto module = parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module) && succeeded(admitStage(*module)), diagnostic);
  return module;
}
SmallVector<pir::OracleQueryOp> queries(ModuleOp module) {
  SmallVector<pir::OracleQueryOp> result;
  module.walk([&](pir::OracleQueryOp op) { result.push_back(op); });
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  cases.run("unknown positions keep an ordered domain-cut window", [&] {
    auto module = parse(context, source());
    auto actual = queries(*module);
    auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
    DominanceInfo dominance(*module);
    unsigned remaining = 1000;
    auto selected = take(selectOracleQueryWindow(
        actual.front(), OracleAuthentication::AtomicBlocks, capacity,
        dominance, remaining));
    require(selected.queries.size() == 2 && selected.leaves == 2 &&
                selected.queries[0] == actual[0] &&
                selected.queries[1] == actual[1],
            "unknown domain or unused answer changed the selected order");
  });
  cases.run("per-query policy retains exactly one source root", [&] {
    auto module = parse(context, source());
    auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
    DominanceInfo dominance(*module);
    unsigned remaining = 1000;
    auto selected = take(selectOracleQueryWindow(
        queries(*module).front(), OracleAuthentication::PerQuery, capacity,
        dominance, remaining));
    require(selected.queries.size() == 1 && selected.leaves == 1,
            "per-query selected another root");
  });
  cases.run("an earlier answer cannot become a discovery operand", [&] {
    auto module = parse(context, source("%a"));
    auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
    DominanceInfo dominance(*module);
    unsigned remaining = 1000;
    auto selected = take(selectOracleQueryWindow(
        queries(*module).front(), OracleAuthentication::AtomicBlocks,
        capacity, dominance, remaining));
    require(selected.queries.size() == 1,
            "adaptive position crossed its answer dependency");
  });
  for (StringRef barrier : {
           R"(%same = "data.index"() {value=0:ui64} : ()->ui64)",
           R"(%ok = arith.constant true
              protocol.guard %ok {owner="V",site="guard"})",
           R"(%sent = protocol.exchange %a {sender="V",receiver="P",site="message"} : ui64)"})
    cases.run("an intervening operation ends the source window", [&] {
      auto module = parse(context, source("%position", barrier));
      auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
      DominanceInfo dominance(*module);
      unsigned remaining = 1000;
      auto selected = take(selectOracleQueryWindow(
          queries(*module).front(), OracleAuthentication::AtomicBlocks,
          capacity, dominance, remaining));
      require(selected.queries.size() == 1, "source barrier crossed");
    });
  cases.run("a different receiver ends the source window", [&] {
    auto module = parse(context, source("%position", "", "W"));
    auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
    DominanceInfo dominance(*module);
    unsigned remaining = 1000;
    auto selected = take(selectOracleQueryWindow(
        queries(*module).front(), OracleAuthentication::AtomicBlocks,
        capacity, dominance, remaining));
    require(selected.queries.size() == 1, "receiver boundary crossed");
  });
  cases.run("exhausted work refuses rather than selecting a shorter window", [&] {
    auto module = parse(context, source());
    auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
    DominanceInfo dominance(*module);
    for (unsigned budget : {0u, 1u, 3u, 5u}) {
      auto remaining = budget;
      refuses(selectOracleQueryWindow(
                  queries(*module).front(), OracleAuthentication::AtomicBlocks,
                  capacity, dominance, remaining),
              "oracle-query-block-limit");
    }
  });
  cases.run("capacity overflow is a compilation refusal", [&] {
    auto module = parse(context, source());
    auto actual = queries(*module);
    auto capacity = take(analyzeOracleQueryCapacity(*module, "main"));
    capacity.queries[actual[0]].leaves = 1048576;
    DominanceInfo dominance(*module);
    unsigned remaining = 1000;
    refuses(selectOracleQueryWindow(
                actual[0], OracleAuthentication::AtomicBlocks, capacity,
                dominance, remaining),
            "oracle-query-block-limit");
  });
  return cases.result();
}
