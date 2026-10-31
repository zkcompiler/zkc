#include "../lib/Transforms/OracleQueryCapacity.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
using namespace zkc::protocol;
using namespace zkc::protocol_ir;
namespace {
std::string source(uint64_t maximum, StringRef operands = "%previous,%other",
                   bool empty = false) {
  std::string query = empty ? R"mlir(
    %answer = "data.index"() {value=0 : ui64} : ()->ui64
)mlir"
                            : R"mlir(
    %answer = "protocol.oracle_query"(%a,%position) {site="first"} : (!H,ui64)->ui64
    %unused = "protocol.oracle_query"(%b,%position) {site="second"} : (!H,ui64)->ui64
)mlir";
  return R"mlir(
#K = #protocol.oracle_kind<"table", [ui64, 2 : ui64]>
!D = !algebra.indices
!H = !protocol.oracle<#K>
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/capacity",revision="0",
   signature=(!D,!D)->i1,purposes=["witness","witness"]}
 "protocol.oracle"() ({
  ^bb0(%a:!H,%b:!H,%position:ui64):
)mlir" + query +
         R"mlir(
   "protocol.oracle_yield"(%answer) : (ui64)->()
 }) {sym_name="combine",function_type=(!H,!H,ui64)->ui64,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
 "protocol.func"() ({
  ^bb0(%data:!D,%count:ui64,%position:ui64):
   %rows = "data.index"() {value=2 : ui64} : ()->ui64
   %first = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},
     sender="P",receivers=["V"],site="data"} : (!D,ui64)->!H
   %last = "protocol.repeat"(%count,%first,%first) ({
    ^bb0(%iteration:ui64,%previous:!H,%other:!H):
     %next = "protocol.oracle_virtual"()mlir" +
         operands.str() +
         R"mlir() {callee=@combine,holder="P",receivers=["V"]} : (!H,!H)->!H
     "protocol.yield"(%next) : (!H)->()
   }) {site="chain",carried=1:i64,maximum=)mlir" +
         std::to_string(maximum) + R"mlir(:i64,
       roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!H)->!H
   %answer = "protocol.oracle_query"(%last,%position) {owner="V",site="read"} : (!H,ui64)->ui64
   "protocol.return"(%answer) : (ui64)->()
 }) {sym_name="main",function_type=(!D,ui64,ui64)->ui64,
     roles=["P","V"],input_roles=[["P"],["P","V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string replace(std::string text, StringRef before, StringRef after) {
  auto offset = text.find(before.str());
  require(offset != std::string::npos, "missing fixture fragment");
  text.replace(offset, before.size(), after.str());
  return text;
}
OwningOpRef<ModuleOp> parse(MLIRContext &context, StringRef text) {
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &message) {
    raw_string_ostream stream(diagnostics);
    message.print(stream);
    return success();
  });
  auto result =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(result), "parse: " + diagnostics);
  require(succeeded(zkc::admitStage(*result)), "formation: " + diagnostics);
  return result;
}
OracleQuerySize bound(ModuleOp source, const OracleQueryCapacity &capacity) {
  auto unit = cast<ProtocolModuleOp>(source.getBody()->front());
  auto program =
      cast<MathematicalOp>(SymbolTable::lookupSymbolIn(unit, "main"));
  auto query = *program.getBody().front().getOps<OracleQueryOp>().begin();
  return capacity.queries.lookup(query);
}
std::string print(Operation *op) {
  std::string result;
  raw_string_ostream stream(result);
  op->print(stream);
  return result;
}
} // namespace
int main() {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  for (uint64_t count = 0; count <= 8; ++count) {
    cases.run("linear recursive query count " + Twine(count), [&] {
      auto original = parse(context, source(count));
      auto before = print(*original);
      auto result = take(analyzeOracleQueryCapacity(*original, "main"));
      require(bound(*original, result) ==
                  OracleQuerySize{count + 1, 2 * count + 1},
              "linear unfolding bound differs");
      require(before == print(*original), "analysis mutated the source");
    });
    cases.run("duplicated unused query count " + Twine(count), [&] {
      auto original = parse(context, source(count, "%previous,%previous"));
      auto result = take(analyzeOracleQueryCapacity(*original, "main"));
      require(bound(*original, result) ==
                  OracleQuerySize{uint64_t(1) << count,
                                  (uint64_t(1) << (count + 1)) - 1},
              "duplicate or unused query was dropped");
    });
  }
  cases.run(
      "a fixed capture reaches a bound independently of the repeat maximum",
      [&] {
        auto original = parse(context, source(1048576, "%other,%other"));
        auto result = take(analyzeOracleQueryCapacity(*original, "main", 500));
        require(bound(*original, result) == OracleQuerySize{2, 3},
                "fixed capture did not stabilize");
      });
  cases.run("zero-query virtuals retain the zero-trip alternative", [&] {
    auto original = parse(context, source(1048576, "%previous,%other", true));
    auto result = take(analyzeOracleQueryCapacity(*original, "main", 500));
    require(bound(*original, result) == OracleQuerySize{1, 1},
            "zero-trip root was lost");
    original->walk([&](OracleVirtualOp created) {
      require(result.constructors.lookup(created) == OracleQuerySize{0, 1},
              "zero-query virtual invented a leaf");
    });
  });
  cases.run("nested repeat bounds retain both backedges", [&] {
    auto text = replace(
        source(3),
        R"mlir(     %next = "protocol.oracle_virtual"(%previous,%other) {callee=@combine,holder="P",receivers=["V"]} : (!H,!H)->!H)mlir",
        R"mlir(     %two = "data.index"() {value=2 : ui64} : ()->ui64
     %next = "protocol.repeat"(%two,%previous,%other) ({
      ^bb0(%j:ui64,%prior:!H,%fixed:!H):
       %created = "protocol.oracle_virtual"(%prior,%fixed) {callee=@combine,holder="P",receivers=["V"]} : (!H,!H)->!H
       "protocol.yield"(%created) : (!H)->()
     }) {site="inner",carried=1:i64,maximum=2:i64,
       roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!H)->!H)mlir");
    auto original = parse(context, text);
    auto result = take(analyzeOracleQueryCapacity(*original, "main"));
    require(bound(*original, result) == OracleQuerySize{7, 13},
            "nested recurrence lost an iteration");
  });
  cases.run("sequence selection joins possible actual anchors", [&] {
    auto text = replace(
        source(3), "!H = !protocol.oracle<#K>",
        "!H = !protocol.oracle<#K>\n!S = !protocol.oracle_sequence<#K, 2>");
    text = replace(
        text,
        R"mlir(   %answer = "protocol.oracle_query"(%last,%position))mlir",
        R"mlir(   %empty = "protocol.oracle_sequence_empty"() : ()->!S
   %a = "protocol.oracle_sequence_append"(%empty,%first) {roles=["P","V"],site="append_first"} : (!S,!H)->!S
   %b = "protocol.oracle_sequence_append"(%a,%last) {roles=["P","V"],site="append_last"} : (!S,!H)->!S
   %selected = "protocol.oracle_sequence_at"(%b,%position) {roles=["V"],site="select"} : (!S,ui64)->!H
   %answer = "protocol.oracle_query"(%selected,%position))mlir");
    auto original = parse(context, text);
    auto result = take(analyzeOracleQueryCapacity(*original, "main"));
    require(bound(*original, result) == OracleQuerySize{4, 7},
            "sequence selection lost the recurrent anchor");
  });
  cases.run("component rebinding retains bounds without a fresh constructor", [&] {
    auto text = replace(
        source(3),
        R"mlir(   %answer = "protocol.oracle_query"(%last,%position))mlir",
        R"mlir(   %parts:2 = "protocol.oracle_components"(%last) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
   %same = "protocol.oracle_input"(%parts#0,%parts#1) {holder="P",receivers=["V"],shape_bounds={}} : (!D,!H)->!H
   %answer = "protocol.oracle_query"(%same,%position))mlir");
    auto original = parse(context, text);
    auto result = take(analyzeOracleQueryCapacity(*original, "main"));
    require(bound(*original, result) == OracleQuerySize{4, 7},
            "component rebinding lost the recurrent anchor");
    require(result.constructors.size() == 2,
            "component rebinding allocated a fresh anchor");
  });
  cases.run("unfolding overflow is a compilation refusal", [&] {
    auto original = parse(context, source(64, "%previous,%previous"));
    refuses(analyzeOracleQueryCapacity(*original, "main"),
            "oracle-query-capacity-overflow");
  });
  for (unsigned count : {0, 1, 3})
    cases.run(
        "exact count tightens a large declared recurrence maximum " +
            Twine(count),
        [&] {
          auto text = replace(
              source(64, "%previous,%previous"),
              "   %last = \"protocol.repeat\"(%count,",
              "   %actual = \"data.index\"() {value=" + std::to_string(count) +
                  ":ui64} : ()->ui64\n"
                  "   %last = \"protocol.repeat\"(%actual,");
          auto original = parse(context, text);
          auto result = take(analyzeOracleQueryCapacity(*original, "main"));
          require(bound(*original, result) ==
                      OracleQuerySize{uint64_t(1) << count,
                                      (uint64_t(1) << (count + 1)) - 1},
                  "known count did not tighten the recurrence");
        });
  for (bool agreed : {false, true})
    cases.run(
        agreed ? "uniform role count tightens capacity"
               : "one participant cannot supply a common count",
        [&] {
          auto text =
              replace(source(3, "%previous,%previous"),
                      "   %last = \"protocol.repeat\"(%count,",
                      R"mlir(   %one = "data.index"() {value=1:ui64} : ()->ui64
   %two = "data.index"() {value=2:ui64} : ()->ui64
   %actual = "protocol.assemble_roles"(%one,)mlir" +
                          std::string(agreed ? "%one" : "%two") +
                          R"mlir() {roles=["P","V"]} : (ui64,ui64)->ui64
   %last = "protocol.repeat"(%actual,)mlir");
          auto original = parse(context, text);
          auto result = take(analyzeOracleQueryCapacity(*original, "main"));
          require(bound(*original, result) ==
                      (agreed ? OracleQuerySize{2, 3} : OracleQuerySize{8, 15}),
                  "role components were incorrectly joined as a count");
        });
  cases.run("an out-of-range count does not create a new admitted maximum",
            [&] {
              auto text = replace(source(1), "\"protocol.repeat\"(%count,",
                                  "\"protocol.repeat\"(%rows,");
              auto original = parse(context, text);
              auto result = take(analyzeOracleQueryCapacity(*original, "main"));
              require(bound(*original, result) == OracleQuerySize{2, 3},
                      "out-of-range count changed the source maximum");
            });
  cases.run("analysis work is bounded without inventing an execution premise",
            [&] {
              auto original = parse(context, source(1048576));
              refuses(analyzeOracleQueryCapacity(*original, "main", 500),
                      "oracle-query-capacity-limit");
              refuses(analyzeOracleQueryCapacity(*original, "main", 0),
                      "oracle-query-capacity-limit");
              refuses(analyzeOracleQueryCapacity(*original, "missing"),
                      "oracle-query-capacity-source");
            });
  return cases.result();
}
