#include "zkc/Analysis/OracleAccess.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace zkc;
using namespace llvm;
namespace {
void require(bool condition, StringRef description) {
  if (!condition) {
    errs() << description << '\n';
    std::exit(1);
  }
}
struct Fixture {
  source::Execution execution;
  void op(std::string path, std::string name, source::Names inputs,
          source::Names outputs, std::string role, source::Names attrs = {}) {
    execution.operations.emplace(
        path,
        source::ExecutionOperation{
            name, inputs, outputs, role, {}, attrs, execution.order.size()});
    if (name == "message")
      execution.operations.at(path).receiver = role == "P" ? "V" : "P";
    execution.order.push_back(path);
  }
  void reorder() {
    for (size_t i = 0; i < execution.order.size(); ++i)
      execution.operations.at(execution.order[i]).ordinal = i;
  }
  void moveBefore(const std::string &path, const std::string &before) {
    auto &order = execution.order;
    order.erase(llvm::find(order, path));
    order.insert(llvm::find(order, before), path);
    reorder();
  }
  Fixture(bool guarded = true, bool collection = false) {
    op("width", "index.constant", {}, {"width"}, "V", {"1"});
    op("height", "index.constant", {}, {"height"}, "V", {"16"});
    op("publish", "oracle.commit", {"table", "width"}, {"root", "state"}, "P");
    op("root-message", "message", {"root"}, {"received-root"}, "P");
    op("draw", "random.index", {"coins", "height"}, {"index", "after"}, "V");
    op("index-message", "message", {"index"}, {"received-index"}, "V");
    std::string state = "state", root = "received-root";
    if (collection) {
      op("zero", "index.constant", {}, {"zero"}, "P", {"0"});
      op("states", "opening_states.empty", {}, {"states"}, "P");
      op("save-state", "opening_states.append", {"states", "state"}, {"saved"},
         "P");
      op("get-state", "opening_states.at", {"saved", "zero"}, {"chosen-state"},
         "P");
      op("roots", "commitments.empty", {}, {"roots"}, "V");
      op("save-root", "commitments.append", {"roots", "received-root"},
         {"saved-roots"}, "V");
      op("v-zero", "index.constant", {}, {"v-zero"}, "V", {"0"});
      op("get-root", "commitments.at", {"saved-roots", "v-zero"},
         {"chosen-root"}, "V");
      state = "chosen-state";
      root = "chosen-root";
    }
    op("open", "oracle.open", {state, "received-index"}, {"row", "proof"}, "P");
    op("row-message", "message", {"row"}, {"received-row"}, "P");
    op("proof-message", "message", {"proof"}, {"received-proof"}, "P");
    op("check", "oracle.check",
       {root, "width", "height", "index", "received-row", "received-proof"},
       {"ok"}, "V");
    if (guarded) {
      op("and", "bool.and", {"ok", "other"}, {"both"}, "V");
      op("guard", "control.require", {"both"}, {}, "V");
    }
  }
  OracleAccessReport analyze(OraclePolicy policy = {true, true}) {
    return analyzeOracleAccess(execution, policy);
  }
};
bool has(const OracleAccessReport &report, StringRef code) {
  return llvm::any_of(report.findings, [&](const auto &finding) {
    return finding.code == code;
  });
}
} // namespace
int main() {
  for (bool collections : {false, true}) {
    Fixture f(true, collections);
    auto report = f.analyze();
    require(report.findings.empty(), "honest static access rejected");
    require(report.accesses.size() == 1, "missing access");
    const auto &a = report.accesses.front();
    require(a.publication == "publish" && a.opening == "open",
            "custody provenance lost");
    require(a.coordinateDraws == source::Names{"draw"}, "query draw lost");
    require(a.coordinateSample == "draw" && a.sampleBoundMatchesHeight,
            "direct bounded sample identity lost");
    require(a.guards == source::Names{"guard"}, "conjunctive guard lost");
    require(a.row == "received-row" && a.proof == "received-proof",
            "received identity collapsed");
  }
  require(has(Fixture(false).analyze(), "oracle-check-unguarded"),
          "unguarded authentication accepted");
  Fixture returned(false);
  returned.execution.results = {"ok"};
  returned.execution.values.emplace(
      "ok", source::ExecutionValue{"bool", "check", "ok", "V"});
  require(has(returned.analyze(), "oracle-check-unguarded"),
          "return silently became acceptance");
  require(returned.analyze({true, true, 0}).findings.empty(),
          "explicit acceptance result not recognized");
  require(has(returned.analyze({true, true, 1}), "oracle-acceptance-result"),
          "missing acceptance result accepted");
  returned.execution.values.at("ok").role = "P";
  require(has(returned.analyze({true, true, 0}), "oracle-check-unguarded"),
          "peer acceptance result used as verifier guard");
  Fixture wrongRole;
  wrongRole.execution.operations.at("guard").role = "P";
  require(has(wrongRole.analyze(), "oracle-check-unguarded"),
          "peer guard used for verifier");
  for (const auto *combine : {"bool.or", "bool.not"}) {
    Fixture alternative;
    auto &op = alternative.execution.operations.at("and");
    op.callee = combine;
    if (op.callee == "bool.not")
      op.inputs.resize(1);
    require(has(alternative.analyze(), "oracle-check-unguarded"),
            "non-conjunctive predicate discharged authentication");
  }
  Fixture wrongCustody;
  wrongCustody.execution.operations.at("open").inputs[0] = "other-state";
  require(has(wrongCustody.analyze(), "oracle-publication-unresolved"),
          "unrelated custody linked");
  require(!has(wrongCustody.analyze({}), "oracle-publication-unresolved"),
          "generic authentication requires in-source publication");
  Fixture swapped;
  std::swap(swapped.execution.operations.at("check").inputs[4],
            swapped.execution.operations.at("check").inputs[5]);
  require(has(swapped.analyze(), "oracle-publication-unresolved"),
          "row and evidence confused");
  Fixture repeated;
  repeated.op("check-again", "oracle.check",
              repeated.execution.operations.at("check").inputs, {"ok2"}, "V");
  repeated.op("guard-again", "control.require", {"ok2"}, {}, "V");
  require(repeated.analyze().accesses.size() == 2,
          "duplicate coordinate occurrences deduplicated");
  Fixture late;
  late.op("late-draw", "random.index", {"after", "height"},
          {"late-index", "after2"}, "V");
  require(has(late.analyze(), "oracle-query-after-response"),
          "responses absorbed before remaining queries");
  Fixture early;
  early.moveBefore("draw", "root-message");
  require(has(early.analyze(), "oracle-query-before-publication"),
          "query before publication accepted");
  Fixture earlyTranscript;
  earlyTranscript.execution.operations.at("draw").callee =
      "transcript.draw_index";
  earlyTranscript.moveBefore("draw", "root-message");
  require(has(earlyTranscript.analyze(), "oracle-query-before-publication"),
          "early transcript sample accepted");
  Fixture lateTranscript;
  lateTranscript.op("late", "transcript.draw_index", {"transcript", "height"},
                    {"late-index", "next"}, "V");
  require(has(lateTranscript.analyze(), "oracle-query-after-response"),
          "late transcript index omitted from query policy");
  Fixture absorbed;
  absorbed.op("observe", "transcript.observe.commitment",
              {"coins", "received-root"}, {"observed"}, "V");
  auto &absorbedOrder = absorbed.execution.order;
  absorbedOrder.pop_back();
  absorbedOrder.insert(llvm::find(absorbedOrder, "draw"), "observe");
  for (size_t i = 0; i < absorbedOrder.size(); ++i)
    absorbed.execution.operations.at(absorbedOrder[i]).ordinal = i;
  absorbed.execution.operations.at("draw").callee = "transcript.draw_index";
  absorbed.execution.operations.at("draw").inputs[0] = "observed";
  auto absorbedReport = absorbed.analyze();
  require(absorbedReport.findings.empty(),
          "absorbed root confused with a peer coordinate");
  require(absorbedReport.accesses.front().coordinateProviderHistory ==
              source::Names{"root-message"},
          "transcript history erased");
  require(absorbedReport.accesses.front().coordinateReceptions.empty(),
          "provider history leaked into direct coordinate provenance");
  require(absorbedReport.accesses.front().publicationBoundDraws ==
              source::Names{"draw"},
          "exact root absorption not recognized");
  // Admitted controls for separate providers, lossy observations and received
  // bounds live in oracle_provenance.py. Synthetic structure is not admission.
  Fixture unsupported;
  unsupported.execution.operations.at("draw").callee = "unknown.sampler";
  require(has(unsupported.analyze(), "oracle-unsupported-provenance"),
          "unknown operation supplied positive sampling evidence");
  Fixture unknown(true, true);
  unknown.execution.operations.at("get-root").inputs[1] = "runtime-index";
  require(has(unknown.analyze(), "oracle-publication-unresolved"),
          "unknown collection coordinate invented");
  Fixture wrongCoordinate;
  wrongCoordinate.execution.operations.at("open").inputs[1] = "unrelated-index";
  require(
      has(wrongCoordinate.analyze(), "oracle-opening-coordinate-unresolved"),
      "unrelated opening coordinate linked");
  Fixture derived;
  // Both roles derive the paired-query coordinate from the same communicated
  // draw and separately computed constants. Their SSA values remain distinct.
  derived.op("p-half", "index.constant", {}, {"p-half"}, "P", {"8"});
  derived.op("v-two", "index.constant", {}, {"v-two"}, "V", {"2"});
  derived.op("v-half", "index.div", {"height", "v-two"}, {"v-half"}, "V");
  derived.op("p-index", "index.mod", {"received-index", "p-half"}, {"p-index"},
             "P");
  derived.op("v-index", "index.mod", {"index", "v-half"}, {"v-index"}, "V");
  auto &order = derived.execution.order;
  auto suffix = source::Names(order.end() - 5, order.end());
  order.erase(order.end() - 5, order.end());
  order.insert(order.begin() + 6, suffix.begin(), suffix.end());
  for (size_t i = 0; i < order.size(); ++i)
    derived.execution.operations.at(order[i]).ordinal = i;
  derived.execution.operations.at("open").inputs[1] = "p-index";
  derived.execution.operations.at("check").inputs[3] = "v-index";
  require(derived.analyze().findings.empty(),
          "paired coordinate congruence lost");
  derived.execution.operations.at("p-half").attributes = {"7"};
  require(has(derived.analyze(), "oracle-opening-coordinate-unresolved"),
          "different modulus equated");
  Fixture noOverflow(true, true);
  noOverflow.execution.operations.at("zero").attributes = {
      "18446744073709551616"};
  require(has(noOverflow.analyze(), "oracle-publication-unresolved"),
          "constant index overflow wrapped");
  Fixture echo;
  echo.op("echo", "message", {"received-index"}, {"echoed"}, "P");
  auto &echoOrder = echo.execution.order;
  echoOrder.pop_back();
  echoOrder.insert(echoOrder.begin() + 6, "echo");
  for (size_t i = 0; i < echoOrder.size(); ++i)
    echo.execution.operations.at(echoOrder[i]).ordinal = i;
  echo.execution.operations.at("check").inputs[3] = "echoed";
  auto echoReport = echo.analyze();
  require(echoReport.accesses.front().coordinateDraws.empty(),
          "peer echo inherited verifier randomness");
  require(echoReport.accesses.front().coordinateReceptions ==
              source::Names{"echo"},
          "received coordinate provenance lost");
  require(has(echoReport, "oracle-query-coordinate-received"),
          "peer coordinate passed query-order policy");
  require(!has(echo.analyze({}), "oracle-query-coordinate-received"),
          "generic authentication forbids peer-selected deterministic opening");
  Fixture peerIndex(true, true);
  peerIndex.op("index-echo", "message", {"zero"}, {"peer-zero"}, "P");
  auto &peerOrder = peerIndex.execution.order;
  peerOrder.pop_back();
  auto getRoot = llvm::find(peerOrder, "get-root");
  peerOrder.insert(getRoot, "index-echo");
  for (size_t i = 0; i < peerOrder.size(); ++i)
    peerIndex.execution.operations.at(peerOrder[i]).ordinal = i;
  peerIndex.execution.operations.at("get-root").inputs[1] = "peer-zero";
  require(has(peerIndex.analyze(), "oracle-publication-unresolved"),
          "peer root selector treated as an honest constant");
  Fixture relayedRoots(true, true);
  relayedRoots.op("roots-out", "message", {"saved-roots"}, {"p-roots"}, "V");
  relayedRoots.op("roots-back", "message", {"p-roots"}, {"v-roots"}, "P");
  auto &relayOrder = relayedRoots.execution.order;
  relayOrder.erase(relayOrder.end() - 2, relayOrder.end());
  auto relaySelection = llvm::find(relayOrder, "get-root");
  relayOrder.insert(relaySelection, {"roots-out", "roots-back"});
  for (size_t i = 0; i < relayOrder.size(); ++i)
    relayedRoots.execution.operations.at(relayOrder[i]).ordinal = i;
  relayedRoots.execution.operations.at("get-root").inputs[0] = "v-roots";
  require(has(relayedRoots.analyze(), "oracle-publication-unresolved"),
          "relayed commitment list inherited local element provenance");
  Fixture unchecked;
  auto &uncheckedOrder = unchecked.execution.order;
  uncheckedOrder.erase(llvm::find(uncheckedOrder, "check"));
  unchecked.execution.operations.erase("check");
  unchecked.reorder();
  require(has(unchecked.analyze(), "oracle-response-unauthenticated"),
          "received oracle response bypassed authentication");
  require(has(Fixture(false).analyze(), "oracle-response-unauthenticated"),
          "unused authentication result counted as a guard");
  // The API accepts execution views, but must reject malformed structure before
  // using operation ports or order. These intentionally are NOT admitted
  // sources.
  for (const auto *path : {"guard", "root-message", "get-root", "save-root",
                           "open", "check", "draw"}) {
    Fixture malformed(true, true);
    malformed.execution.operations.at(path).inputs.clear();
    const auto *code = StringRef(path) == "check"  ? "oracle-check-signature"
                       : StringRef(path) == "draw" ? "oracle-sampler-signature"
                                                   : "oracle-execution-invalid";
    require(has(malformed.analyze(), code), "malformed input arity accepted");
  }
  for (const auto *path : {"root-message", "get-state", "publish", "draw"}) {
    Fixture malformed(true, true);
    malformed.execution.operations.at(path).outputs.clear();
    require(has(malformed.analyze(), StringRef(path) == "draw"
                                         ? "oracle-sampler-signature"
                                         : "oracle-execution-invalid"),
            "malformed output arity accepted");
  }
  absorbed.execution.operations.at("observe").inputs.pop_back();
  require(has(absorbed.analyze(), "oracle-observation-signature"),
          "malformed observation arity accepted");
  Fixture absent;
  absent.execution.operations.erase("draw");
  require(has(absent.analyze(), "oracle-execution-invalid"),
          "missing path crashed");
  Fixture missingPath;
  missingPath.execution.order[0] = "absent";
  require(has(missingPath.analyze(), "oracle-execution-invalid"),
          "unknown path accepted");
  Fixture duplicatePath;
  duplicatePath.execution.order[1] = duplicatePath.execution.order[0];
  require(has(duplicatePath.analyze(), "oracle-execution-invalid"),
          "duplicate path accepted");
  Fixture ordinal;
  ordinal.execution.operations.at("draw").ordinal = 100;
  require(has(ordinal.analyze(), "oracle-execution-invalid"),
          "false ordinal accepted");
  Fixture duplicateValue;
  duplicateValue.execution.operations.at("draw").outputs[0] = "height";
  require(has(duplicateValue.analyze(), "oracle-execution-invalid"),
          "duplicate SSA accepted");
  Fixture cycle;
  cycle.execution.operations.at("draw").inputs[0] = "after";
  require(has(cycle.analyze(), "oracle-execution-invalid"),
          "cyclic value accepted");
  Fixture receiver;
  receiver.execution.operations.at("root-message").receiver.clear();
  require(has(receiver.analyze(), "oracle-execution-invalid"),
          "missing receiver accepted");
  require(has(analyzeOracleAccess(Fixture().execution, {}, 0),
              "oracle-analysis-limit"),
          "zero work budget ignored");
  Fixture selection(false);
  selection.execution.results = {"missing"};
  require(has(selection.analyze({false, false, 0}), "oracle-acceptance-result"),
          "unrecorded acceptance result accepted");
  selection.execution.results = {"n"};
  selection.execution.values.emplace(
      "n", source::ExecutionValue{"index", {}, "n", "V"});
  require(has(selection.analyze({false, false, 0}), "oracle-acceptance-result"),
          "non-Boolean acceptance result accepted");
  selection.execution.values.at("n").type = "bool";
  selection.execution.values.at("n").role.clear();
  require(has(selection.analyze({false, false, 0}), "oracle-acceptance-result"),
          "acceptance result with no owner accepted");
  OraclePolicy sampled{true, true, {}, true};
  require(Fixture().analyze(sampled).findings.empty(),
          "exact sample policy rejected");
  require(has(derived.analyze(sampled), "oracle-query-not-exact-sample"),
          "derived coordinate passed exact sampling policy");

  // Thousands of observations retain one node each. Prefix copying would use
  // quadratic work and exceed this supplied budget, even before checking a
  // root.
  Fixture chain;
  auto &chainDraw = chain.execution.operations.at("draw");
  chainDraw.callee = "transcript.draw_index";
  std::string provider = "coins";
  source::Names observationOrder;
  for (unsigned i = 0; i < 4096; ++i) {
    auto path = "observe-" + std::to_string(i);
    chain.op(path, "transcript.observe.commitment", {provider, "received-root"},
             {path}, "V");
    observationOrder.push_back(path);
    provider = path;
  }
  chainDraw.inputs[0] = provider;
  auto &chainOrder = chain.execution.order;
  chainOrder.erase(chainOrder.end() - observationOrder.size(),
                   chainOrder.end());
  chainOrder.insert(llvm::find(chainOrder, "draw"), observationOrder.begin(),
                    observationOrder.end());
  chain.reorder();
  require(
      analyzeOracleAccess(chain.execution, sampled, 200000).findings.empty(),
      "observation prefixes still require quadratic storage/work");

  // First pass fits; repeated exact-root searches exhaust the same budget in
  // the second pass. Partial accesses prove that the first pass completed.
  Fixture searches;
  searches.execution.operations.at("draw").callee = "transcript.draw_index";
  provider = "coins";
  for (unsigned i = 0; i < 256; ++i) {
    auto path = "observe-" + std::to_string(i);
    searches.op(path, "transcript.observe.bool", {provider, "other"}, {path},
                "V");
    searches.moveBefore(path, "draw");
    provider = path;
  }
  searches.execution.operations.at("draw").inputs[0] = provider;
  for (unsigned i = 0; i < 256; ++i) {
    auto path = "check-" + std::to_string(i);
    searches.op(path, "oracle.check",
                searches.execution.operations.at("check").inputs, {path}, "V");
    searches.op(path + "-guard", "control.require", {path}, {}, "V");
  }
  auto limited = analyzeOracleAccess(searches.execution, sampled, 30000);
  require(has(limited, "oracle-analysis-limit") && !limited.accesses.empty() &&
              limited.accesses.size() < 257,
          "second-pass observation search did not stop at the work budget");
  require(llvm::count_if(limited.findings,
                         [](const auto &f) {
                           return f.code == "oracle-analysis-limit";
                         }) == 1,
          "work exhaustion reported repeatedly");
  require(!has(analyzeOracleAccess(searches.execution, sampled, 200000),
               "oracle-analysis-limit"),
          "small stress input unexpectedly expensive");
  outs() << encodeOracleAccess(repeated.analyze()) << '\n';
}
