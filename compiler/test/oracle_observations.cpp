#include "../lib/Compiler/OracleSchedule.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Mathematical.h"
using namespace llvm;
using namespace mlir;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
std::string source(StringRef body, StringRef declarations = "") {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"bls12-381.fr">, 16 : ui64]>
!F = !algebra.field<"bls12-381.fr">
!D = !algebra.field_vector<"bls12-381.fr">
!H = !protocol.oracle<#K>
!R = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
)mlir" + declarations.str() +
         R"mlir(
 "protocol.func"() ({
  ^bb0(%data:!D,%position:ui64,%trips:ui64,%random:!R,%condition:i1):
   %rows = "data.index"() {value="16"} : ()->ui64
   %zero = "data.index"() {value="0"} : ()->ui64
   %one = "data.index"() {value="1"} : ()->ui64
   %two = "data.index"() {value="2"} : ()->ui64
   %yes = arith.constant true
   %no = arith.constant false
   %word = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="word"} : (!D,ui64)->!H
)mlir" + body.str() +
         R"mlir(
   "protocol.return"(%yes) : (i1)->()
 }) {sym_name="example",function_type=(!D,ui64,ui64,!R,i1)->i1,
     roles=["P","V"],input_roles=[["P"],["V"],["P","V"],["V"],["P","V"]],output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
const std::string query = R"mlir(
 %answer = "protocol.oracle_query"(%word,%position) {owner="V",site="read"} : (!H,ui64)->!F
)mlir";
const std::string draw = R"mlir(
 %challenge = "protocol.query"(%random) {owner="V",method="draw",site="challenge"} : (!R)->!F
)mlir";
std::string loop(StringRef count, StringRef body, StringRef maximum = "2",
                 StringRef condition = "%condition") {
  auto inner = body.str();
  for (StringRef name :
       {"word", "position", "random", "condition", "answer", "challenge"}) {
    std::string before = "%" + name.str(), after = "%inner_" + name.str();
    size_t position = 0;
    while ((position = inner.find(before, position)) != std::string::npos) {
      inner.replace(position, before.size(), after);
      position += after.size();
    }
  }
  return "\"protocol.repeat\"(" + count.str() + ",%word,%position,%random," +
         condition.str() + R"mlir() ({
 ^bb0(%i:ui64,%inner_word:!H,%inner_position:ui64,%inner_random:!R,%inner_condition:i1):
)mlir" + inner +
         R"mlir(
 "protocol.yield"() : ()->()
 }) {site="loop",carried=0:i64,maximum=)mlir" +
         maximum.str() +
         R"mlir(:i64,roles=["P","V"],carried_roles=[]} : (ui64,!H,ui64,!R,i1)->()
)mlir";
}

} // namespace
int main() {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
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
    require(succeeded(verify(*module)), "fixture not admitted: " + diagnostics);
    return module;
  };
  auto analyzes = [&](StringRef text, StringRef observer = "V") {
    auto module = parse(text);
    return take(analyzeOracleObservations(*module, "example", observer));
  };
  auto expects = [&](StringRef body, bool bad) {
    require(analyzes(source(body)).queryBeforeDraw() == bad,
            "reached query/draw order changed");
  };
  Cases cases;
  cases.run("final-draw order follows the selected observer", [&] {
    expects(query + draw, true);
    expects(draw + query, false);
    require(!analyzes(source(query + draw), "P").queryBeforeDraw(),
            "another role acquired the verifier's observations");
  });
  cases.run("only the selected participant's failed guard ends its flow", [&] {
    expects(query + R"mlir(protocol.guard %no {owner="V",site="reject"})mlir" +
                draw,
            false);
    expects(query + R"mlir(protocol.guard %no {owner="P",site="reject"})mlir" +
                draw,
            true);
    expects(
        query +
            R"mlir(protocol.guard %condition {owner="V",site="reject"})mlir" +
            draw,
        true);
    expects(query + R"mlir(protocol.guard %yes {owner="V",site="reject"})mlir" +
                draw,
            true);
  });
  cases.run("completion preserves other participant continuations", [&] {
    expects(
        query +
            R"mlir("protocol.finish_if"(%yes,%no) {owner="V",site="done"} : (i1,i1)->())mlir" +
            draw,
        false);
    expects(
        query +
            R"mlir("protocol.finish_if"(%yes) {owner="P",site="done"} : (i1)->())mlir" +
            draw,
        true);
    expects(
        query +
            R"mlir("protocol.finish_if"(%condition,%no) {owner="V",site="done"} : (i1,i1)->())mlir" +
            draw,
        true);
  });
  cases.run("counted repeats retain cross-iteration observations", [&] {
    expects(loop("%zero", query + draw), false);
    expects(loop("%one", draw + query), false);
    expects(loop("%two", draw + query), true);
    expects(loop("%trips", draw + query), true);
    expects(loop("%trips", draw + query, "1"), false);
  });
  cases.run("invariant loop captures retain early stops", [&] {
    auto body =
        query +
        R"mlir(protocol.guard %condition {owner="V",site="reject"})mlir";
    expects(loop("%two", body, "2", "%no") + draw, false);
    expects(loop("%two", body) + draw, true);
  });
  cases.run("carried loop values are not their initial constants", [&] {
    auto body = R"mlir(
 %last = "protocol.repeat"(%two,%no,%word,%position) ({
  ^bb0(%iteration:ui64,%carried:i1,%inner_word:!H,%inner_position:ui64):
   %answer = "protocol.oracle_query"(%inner_word,%inner_position) {owner="V",site="read"} : (!H,ui64)->!F
   "protocol.guard"(%carried) {owner="V",site="maybe_stop"} : (i1)->()
   %next = arith.constant true
   "protocol.yield"(%next) : (i1)->()
 }) {site="loop",carried=1:i64,maximum=2:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,i1,!H,ui64)->i1
)mlir";
    // The summary conservatively considers each carried argument unknown.
    // Treating it as %no on every iteration would incorrectly discard paths.
    expects(std::string(body) + draw, true);
    expects(query + loop("%two", "", "1") + draw, false);
  });
  cases.run(
      "source applications require checked expansion and role substitution",
      [&] {
        const char *child = R"mlir(
 "protocol.func"() ({
  ^bb0(%rng:!R):
   %x = "protocol.query"(%rng) {owner="A",method="draw",site="child_draw"} : (!R)->!F
   "protocol.return"() : ()->()
 }) {sym_name="child",function_type=(!R)->(),roles=["A","B"],input_roles=[["A"]],output_roles=[]} : ()->()
)mlir";
        auto module = parse(source(
            query +
                R"mlir(protocol.apply @child(%random) {roles=["V","P"],site="call"} : (!R)->())mlir",
            child));
        refuses(analyzeOracleObservations(*module, "example", "V"),
                "oracle-observation-preparation");
        auto prepared = zkc::mathematical::prepareProtocol(*module, false);
        require(bool(prepared), "preparation failed: " + diagnostics);
        require(take(analyzeOracleObservations(*prepared, "example", "V"))
                    .queryBeforeDraw(),
                "expanded child's draw lost its substituted role");
        require(!take(analyzeOracleObservations(*prepared, "example", "P"))
                     .queryBeforeDraw(),
                "callee-local role leaked into another observer");
      });
  cases.run("unknown entry roles and mutated source refuse", [&] {
    auto module = parse(source(query + draw));
    refuses(analyzeOracleObservations(*module, "absent", "V"),
            "oracle-observation-interface");
    refuses(analyzeOracleObservations(*module, "example", "absent"),
            "oracle-observation-interface");
    module->getBody()->clear();
    refuses(analyzeOracleObservations(*module, "example", "V"),
            "oracle-observation-source");
  });
  return cases.result();
}
