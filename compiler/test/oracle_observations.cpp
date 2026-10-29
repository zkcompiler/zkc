#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/OracleSchedule.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/Support/JSON.h"
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
    require(succeeded(verify(*module)), "fixture not admitted: " + diagnostics);
    return module;
  };
  auto analyzes = [&](StringRef text, StringRef observer = "V") {
    auto module = parse(text);
    return take(analyzeOracleObservations(*module, "example", observer));
  };
  auto expectsText = [&](StringRef text, bool bad) {
    auto module = parse(text);
    require(take(analyzeOracleObservations(*module, "example", "V"))
                    .queryBeforeDraw() == bad,
            "reached query/draw order changed");
    OracleRealizationPolicy policy;
    policy.flush = OracleQueryFlush::AfterFinalDraw;
    auto selection = resolveOracleRealizationSelection(*module, policy);
    if (bad)
      refuses(std::move(selection), "oracle-realization-flush-profile");
    else
      (void)take(std::move(selection));
  };
  auto expects = [&](StringRef body, bool bad) {
    expectsText(source(body), bad);
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
  cases.run("the final-draw policy covers index requests", [&] {
    const std::string index = R"mlir(
 %challenge = "protocol.query"(%random,%rows) {owner="V",method="index",site="challenge"} : (!R,ui64)->ui64
)mlir";
    for (bool bad : {false, true}) {
      auto text = source(bad ? query + index : index + query);
      const std::string before = "random.bls12-381.fr/0";
      text.replace(text.find(before), before.size(),
                   "random.goldilocks.ext2-binomial7/0");
      expectsText(text, bad);
    }
  });
  cases.run("each query owner has its own final-draw obligation", [&] {
    auto atP = [](std::string text) {
      const std::string before = "owner=\"V\"";
      text.replace(text.find(before), before.size(), "owner=\"P\"");
      return text;
    };
    auto selected = [&](StringRef body, StringRef serviceOwner) {
      auto text = source(body);
      const std::string before =
          "input_roles=[[\"P\"],[\"V\"],[\"P\",\"V\"],[\"V\"],[\"P\",\"V\"]]";
      text.replace(text.find(before), before.size(),
                   "input_roles=[[\"P\"],[\"P\",\"V\"],[\"P\",\"V\"],"
                   "[\"" +
                       serviceOwner.str() + "\"],[\"P\",\"V\"]]");
      auto module = parse(text);
      OracleRealizationPolicy policy;
      policy.flush = OracleQueryFlush::AfterFinalDraw;
      return resolveOracleRealizationSelection(*module, policy);
    };
    (void)take(selected(query + atP(draw), "P"));
    (void)take(selected(atP(query) + draw, "V"));
    refuses(selected(atP(query) + atP(draw), "P"),
            "oracle-realization-flush-profile");
    refuses(
        selected(
            atP(query) +
                R"mlir("protocol.finish_if"(%yes,%no) {owner="V",site="done"} : (i1,i1)->())mlir" +
                atP(draw),
            "P"),
        "oracle-realization-flush-profile");
  });
  cases.run("unused virtual query bodies do not create observations", [&] {
    const char *declarations = R"mlir(
 relation.declare @identity_ok {kind="external",key="test/identity",revision="0",
  signature=(!D)->i1,purposes=["witness"]}
 "protocol.oracle"() ({
 ^entry(%a:!H,%position:ui64):
  %answer = "protocol.oracle_query"(%a,%position) {site="child"} : (!H,ui64)->!F
  "protocol.oracle_yield"(%answer) : (!F)->()
 }) {sym_name="identity",function_type=(!H,ui64)->!F,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@identity_ok} : ()->()
)mlir";
    auto module = parse(source(draw, declarations));
    OracleRealizationPolicy policy;
    policy.flush = OracleQueryFlush::AfterFinalDraw;
    (void)take(resolveOracleRealizationSelection(*module, policy));
  });
  cases.run(
      "readback rechecks source ordering under the requested policy", [&] {
        auto checked = [&](Error failure) {
          if (failure)
            throw std::runtime_error(toString(std::move(failure)));
        };
        auto prepare = [&](StringRef text) {
          auto module = parse(text);
          auto prepared = zkc::mathematical::prepareProtocol(*module, false);
          require(bool(prepared), "preparation failed: " + diagnostics);
          return prepared;
        };
        OracleRealizationPolicy policy;
        policy.flush = OracleQueryFlush::AfterFinalDraw;
        auto good = prepare(source(draw + query));
        auto realized = take(emitOracleRealization(*good, policy));
        auto record = take(serializeOracleRealization(*good, realized, policy));
        std::string candidateText;
        raw_string_ostream(candidateText) << *realized.module;
        auto independent = parse(candidateText);
        checked(checkOracleRealization(*good, *independent, record, policy));

        auto altered = take(json::parse(record));
        auto *ports = altered.getAsObject()
                          ->getArray("entries")
                          ->front()
                          .getAsObject()
                          ->getObject("interface")
                          ->getArray("inputs");
        require(ports && ports->size() == 5, "wrong input interface");
        auto *servicePort = (*ports)[3].getAsObject();
        require(servicePort && servicePort->getString("service") ==
                                   "random.bls12-381.fr/0",
                "service input lost its installed identity");
        (*servicePort)["service"] = "random.bn254.fr/0";
        std::string alteredRecord;
        raw_string_ostream(alteredRecord) << altered;
        auto alteredFailure =
            checkOracleRealization(*good, *independent, alteredRecord, policy);
        require(bool(alteredFailure), "substituted service input accepted");
        consumeError(std::move(alteredFailure));

        auto bad = prepare(source(query + draw));
        refuses(emitOracleRealization(*bad, policy),
                "oracle-realization-flush-profile");
        auto immediate = take(emitOracleRealization(*bad));
        auto immediateRecord =
            take(serializeOracleRealization(*bad, immediate));
        auto forged = take(json::parse(immediateRecord));
        (*forged.getAsObject()->getObject("selection"))["flush"] =
            "after-final-draw";
        std::string forgedRecord;
        raw_string_ostream(forgedRecord) << forged;
        auto failure = checkOracleRealization(*bad, *immediate.module,
                                              forgedRecord, policy);
        require(bool(failure), "record authorized an invalid source schedule");
        require(namesIdentifier(toString(std::move(failure)),
                                "oracle-realization-flush-profile"),
                "readback did not rederive the source schedule");
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
