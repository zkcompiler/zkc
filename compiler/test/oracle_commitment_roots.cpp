#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/PreparedProtocol.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include <filesystem>
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::test;
namespace {
constexpr StringLiteral scheme =
    "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0";
std::string source(bool input, bool fixed) {
  std::string result = R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">EXTENT]>
!H = !protocol.oracle<#K>
!D = !algebra.field_vector<"koala-bear.ext4-binomial3">
module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%data:!D,%anchor:ANCHOR):
  BINDING
  %rows = "protocol.oracle_shape"(%handle) {dimension="rows"} : (!H)->ui64
  "protocol.return"(%rows) : (ui64)->()
 }) {sym_name="main",function_type=(!D,ANCHOR)->ui64,roles=["P","V"],input_roles=[["P"],ROLES],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  auto replace = [&](StringRef from, StringRef to) {
    size_t position = 0;
    while ((position = result.find(from.str(), position)) !=
           std::string::npos) {
      result.replace(position, from.size(), to.str());
      position += to.size();
    }
  };
  replace("EXTENT", fixed ? ",8:ui64" : "");
  replace("ANCHOR", input ? "!H" : "ui64");
  replace("ROLES", input ? "[\"V\"]" : "[\"P\",\"V\"]");
  std::string bounds = fixed ? "{}" : "{rows=16:ui64}";
  replace("BINDING", input
                         ? "%handle = \"protocol.oracle_input\"(%data,%anchor) "
                           "{holder=\"P\",receivers=[\"V\"],shape_bounds=" +
                               bounds + "} : (!D,!H)->!H"
                         : "%handle = \"protocol.oracle_send\"(%data,%anchor) "
                           "{sender=\"P\",receivers=[\"V\"],shape_names=["
                           "\"rows\"],shape_bounds=" +
                               bounds + ",site=\"word\"} : (!D,ui64)->!H");
  return result;
}
std::string print(ModuleOp module) {
  std::string text;
  raw_string_ostream stream(text);
  module.print(stream);
  return text;
}
void checked(Error e) {
  if (e)
    throw std::runtime_error(toString(std::move(e)));
}
void refused(Error e) {
  require(bool(e), "expected refusal");
  consumeError(std::move(e));
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  Cases cases;
  for (bool input : {false, true})
    for (bool fixed : {false, true}) {
      std::string name = std::string(input ? "input" : "send") +
                         (fixed ? "-fixed" : "-dynamic");
      auto text = source(input, fixed);
      auto original = parseSourceString<ModuleOp>(text, &context);
      require(bool(original), "root fixture did not parse");
      auto owner = mathematical::PreparedProtocol::prepare(*original);
      require(bool(owner), "root fixture did not prepare");
      auto prepared = owner->snapshot();
      auto selections = take(resolveOracleRealizationSelection(*prepared, {}));
      require(selections.size() == 1, "wrong root inventory");
      auto root = selections[0];
      root.realization = {scheme.str(), OracleLeafGrouping::AntipodalPairs,
                          OracleLeafOrder::Natural};
      OracleRealizationPolicy policy;
      policy.roots = std::vector<OracleRootSelection>{root};
      cases.run(name + " selected root and native compilation", [&] {
        auto candidate = take(emitOracleRealization(*prepared, policy));
        auto record =
            take(serializeOracleRealization(*prepared, candidate, policy));
        checked(checkOracleRealization(*prepared, *candidate.module, record,
                                       policy));
        auto copy =
            parseSourceString<ModuleOp>(print(*candidate.module), &context);
        require(bool(copy), "realized root did not parse");
        checked(checkOracleRealization(*prepared, *copy, record, policy));
        bool changedPosition = false;
        copy->walk([&](protocol_ir::LocalCallOp call) {
          if (call.getCallee() !=
              candidate.entries[0].merkle[0].position.getSymName())
            return;
          require(call.getNumOperands() == 2, "wrong position call arity");
          call->setOperand(0, call.getOperand(1));
          changedPosition = true;
        });
        require(changedPosition && succeeded(verify(*copy)),
                "position mutation must preserve formation");
        refused(checkOracleRealization(*prepared, *copy, record, policy));
        const auto &shapes = candidate.entries[0].inputShapes;
        require(shapes.size() == unsigned(input && !fixed),
                "incorrect shape expansion");
        if (!shapes.empty())
          require(shapes[0].anchor == 1 && shapes[0].port == 2,
                  "wrong shape association");
        RunOptions options;
        options.oracleRealization = policy;
        auto run =
            take(compileRun(text, "oracle-roots.mlir", options, registry));
        auto edge = run.compilation.oracleRealizationSnapshot();
        require(bool(edge), "joint compilation lost realization edge");
        checked(checkOracleRealization(*edge->original, *edge->candidate,
                                       edge->record, policy));
        if (argc == 2) {
          std::filesystem::create_directories(argv[1]);
          std::ofstream out(std::filesystem::path(argv[1]) /
                            ("root-" + name + ".bundle"));
          out << run.bundle;
          require(bool(out), "could not retain root bundle");
        }
        // The record cannot authorize a change to the requested scheme/layout.
        refused(checkOracleRealization(*prepared, *candidate.module, record));
        auto changed = policy;
        changed.roots->front().realization.order = OracleLeafOrder::BitReversed;
        refused(checkOracleRealization(*prepared, *candidate.module, record,
                                       changed));
        changed = policy;
        changed.flush = OracleQueryFlush::AfterFinalDraw;
        refused(checkOracleRealization(*prepared, *candidate.module, record,
                                       changed));
        auto parsedRecord = take(json::parse(record));
        (*parsedRecord.getAsObject()->getObject("selection"))["flush"] =
            "after-final-draw";
        std::string mutated;
        raw_string_ostream(mutated) << parsedRecord;
        refused(checkOracleRealization(*prepared, *candidate.module, mutated,
                                       policy));
        if (input && !fixed) {
          auto changed = take(json::parse(record));
          auto *entry =
              changed.getAsObject()->getArray("entries")->front().getAsObject();
          (*entry->getArray("input_shapes"))[0].getAsObject()->operator[](
              "port") = 1;
          std::string mutated;
          raw_string_ostream(mutated) << changed;
          refused(checkOracleRealization(*prepared, *candidate.module, mutated,
                                         policy));
        }
      });
      cases.run(name + " exact selection coverage", [&] {
        auto bad = policy;
        bad.roots->clear();
        refuses(emitOracleRealization(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->push_back(root);
        refuses(emitOracleRealization(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().path[0] += 1;
        refuses(emitOracleRealization(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().entry = "missing";
        refuses(emitOracleRealization(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().realization.scheme.clear();
        refuses(emitOracleRealization(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.flush = static_cast<OracleQueryFlush>(99);
        refuses(resolveOracleRealizationSelection(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().path.clear();
        refuses(resolveOracleRealizationSelection(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().path.assign(65, 0);
        refuses(resolveOracleRealizationSelection(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().realization.grouping =
            static_cast<OracleLeafGrouping>(99);
        refuses(resolveOracleRealizationSelection(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().realization.order = static_cast<OracleLeafOrder>(99);
        refuses(resolveOracleRealizationSelection(*prepared, bad),
                "oracle-realization-selection");
        bad = policy;
        bad.roots->front().realization.scheme =
            "rows.merkle-poseidon2-16.koala-bear/0";
        refuses(emitOracleRealization(*prepared, bad), "oracle-storage-scheme");
        bad = policy;
        bad.roots->resize(100001);
        refuses(resolveOracleRealizationSelection(*prepared, bad),
                "oracle-realization-selection-limit");
      });
    }
  cases.run("selection order is canonical", [&] {
    auto text = source(false, false);
    auto begin = text.find("%handle =");
    auto end = text.find('\n', begin);
    std::string second = text.substr(begin, end - begin);
    second.replace(0, 7, "%second");
    auto site = second.find("word");
    second.replace(site, 4, "other");
    text.insert(end, "\n  " + second);
    auto original = parseSourceString<ModuleOp>(text, &context);
    require(bool(original), "two-root fixture did not parse");
    auto owner = mathematical::PreparedProtocol::prepare(*original);
    require(bool(owner), "two-root fixture did not prepare");
    auto prepared = owner->snapshot();
    auto roots = take(resolveOracleRealizationSelection(*prepared, {}));
    require(roots.size() == 2, "wrong two-root inventory");
    for (auto &root : roots)
      root.realization = {scheme.str(), OracleLeafGrouping::AntipodalPairs,
                          OracleLeafOrder::Natural};
    OracleRealizationPolicy policy;
    policy.roots = roots;
    auto candidate = take(emitOracleRealization(*prepared, policy));
    auto record =
        take(serializeOracleRealization(*prepared, candidate, policy));
    std::reverse(policy.roots->begin(), policy.roots->end());
    checked(
        checkOracleRealization(*prepared, *candidate.module, record, policy));
    require(take(serializeOracleRealization(*prepared, candidate, policy)) ==
                record,
            "selector input order changed the record");
  });
  cases.run("query policies never silently fall back", [&] {
    auto text = source(false, false);
    text.insert(text.find("  \"protocol.return\""), R"mlir(
  %answer = "protocol.oracle_query"(%handle,%rows) {owner="V",site="read"} : (!H,ui64)->!algebra.field<"koala-bear.ext4-binomial3">
)mlir");
    auto original = parseSourceString<ModuleOp>(text, &context);
    require(bool(original), "query fixture did not parse");
    auto owner = mathematical::PreparedProtocol::prepare(*original);
    require(bool(owner), "query fixture did not prepare");
    auto prepared = owner->snapshot();
    auto roots = take(resolveOracleRealizationSelection(*prepared, {}));
    OracleRealizationPolicy policy;
    policy.flush = OracleQueryFlush::AfterFinalDraw;
    refuses(emitOracleRealization(*prepared, policy),
            "oracle-realization-flush-profile");
    policy.flush = OracleQueryFlush::Immediate;
    for (auto &root : roots)
      root.realization = {scheme.str(), OracleLeafGrouping::AntipodalPairs,
                          OracleLeafOrder::Natural};
    policy.roots = roots;
    refuses(emitOracleRealization(*prepared, policy), "oracle-common-helper");
  });
  return cases.result();
}
