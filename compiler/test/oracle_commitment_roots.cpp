#include "../lib/Transforms/OracleCommonRealization.h"
#include "../lib/Transforms/PreparedProtocol.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
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
std::string source(bool input, bool fixed, bool query = false) {
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
  if (query) {
    replace("%anchor:!H)", "%anchor:!H,%position:ui64)");
    replace("%anchor:ui64)", "%anchor:ui64,%position:ui64)");
    replace("function_type=(!D,!H)->ui64",
            "function_type=(!D,!H,ui64)->!algebra.field<\"koala-bear.ext4-"
            "binomial3\">");
    replace("function_type=(!D,ui64)->ui64",
            "function_type=(!D,ui64,ui64)->!algebra.field<\"koala-bear.ext4-"
            "binomial3\">");
    replace("input_roles=[[\"P\"],[\"V\"]]",
            "input_roles=[[\"P\"],[\"V\"],[\"V\"]]");
    replace("input_roles=[[\"P\"],[\"P\",\"V\"]]",
            "input_roles=[[\"P\"],[\"P\",\"V\"],[\"V\"]]");
    replace("\"protocol.return\"(%rows) : (ui64)->()",
            "%answer = \"protocol.oracle_query\"(%handle,%position) "
            "{owner=\"V\",site=\"read\"} : "
            "(!H,ui64)->!algebra.field<\"koala-bear.ext4-binomial3\">\n"
            "  \"protocol.return\"(%answer) : "
            "(!algebra.field<\"koala-bear.ext4-binomial3\">)->()");
  }
  return result;
}
std::string virtualSource(bool zero) {
  std::string text = R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">,8:ui64]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
!D = !algebra.field_vector<"koala-bear.ext4-binomial3">
module { "protocol.module"() ({
 relation.declare @empty_ok {kind="external",key="test/empty",revision="0",
  signature=(!D,!F)->i1,purposes=["witness","parameter"]}
 relation.declare @combine_ok {kind="external",key="test/combine",revision="0",
  signature=(!D,!D,ui64)->i1,purposes=["witness","witness","parameter"]}
 "protocol.oracle"() ({
 ^entry(%a:!H,%value:!F,%position:ui64):
  "protocol.oracle_yield"(%value) : (!F)->()
 }) {sym_name="empty",function_type=(!H,!F,ui64)->!F,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@empty_ok} : ()->()
 "protocol.oracle"() ({
 ^entry(%a:!H,%b:!H,%mapped:ui64,%position:ui64):
  %answer = "protocol.oracle_query"(%a,%position) {site="left"} : (!H,ui64)->!F
  %unused = "protocol.oracle_query"(%b,%mapped) {site="right"} : (!H,ui64)->!F
  "protocol.oracle_yield"(%answer) : (!F)->()
 }) {sym_name="combine",function_type=(!H,!H,ui64,ui64)->!F,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@combine_ok} : ()->()
 "protocol.func"() ({
 ^entry(%data:!D,%constant:!F,%mapped:ui64,%position:ui64,%trips:ui64):
  %rows = "data.index"() {value=8 : ui64} : ()->ui64
  %a = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},
    sender="P",receivers=["V"],site="word"} : (!D,ui64)->!H
  %empty = "protocol.oracle_virtual"(%a,%constant) {callee=@empty,holder="P",receivers=["V"]} : (!H,!F)->!H
  %last = "protocol.repeat"(%trips,%a,OTHER,%mapped) ({
   ^body(%iteration:ui64,%previous:!H,%other:!H,%map:ui64):
    %next = "protocol.oracle_virtual"(%previous,%other,%map) {callee=@combine,holder="P",receivers=["V"]} : (!H,!H,ui64)->!H
    "protocol.yield"(%next) : (!H)->()
  }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!H,ui64)->!H
  %answer = "protocol.oracle_query"(%last,%position) {owner="V",site="read"} : (!H,ui64)->!F
  "protocol.return"(%answer) : (!F)->()
 }) {sym_name="main",function_type=(!D,!F,ui64,ui64,ui64)->!F,roles=["P","V"],
     input_roles=[["P"],["P","V"],["P","V"],["V"],["P","V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
  text.replace(text.find("OTHER"), 5, zero ? "%empty" : "%a");
  return text;
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
  bool selectedCase = false;
  auto runCase = [&](const Twine &name, llvm::function_ref<void()> body) {
    auto label = name.str();
    if (argc > 2 && !StringRef(label).contains(argv[2]))
      return;
    selectedCase = true;
    cases.run(label, body);
  };
  if (argc >= 2)
    std::filesystem::create_directories(argv[1]);
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
      runCase(name + " selected root and native compilation", [&] {
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
        if (argc >= 2) {
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
        changed.order = OracleQueryOrder::AfterFinalDraw;
        refused(checkOracleRealization(*prepared, *candidate.module, record,
                                       changed));
        auto parsedRecord = take(json::parse(record));
        (*parsedRecord.getAsObject()->getObject("selection"))["order"] =
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
      runCase(name + " authenticated common query", [&] {
        auto queryText = source(input, fixed, true);
        auto original = parseSourceString<ModuleOp>(queryText, &context);
        require(bool(original), "query did not parse");
        auto owner = mathematical::PreparedProtocol::prepare(*original);
        require(bool(owner), "query did not prepare");
        auto prepared = owner->snapshot();
        auto candidate = take(emitOracleRealization(*prepared, policy));
        auto record =
            take(serializeOracleRealization(*prepared, candidate, policy));
        checked(checkOracleRealization(*prepared, *candidate.module, record,
                                       policy));
        auto copy =
            parseSourceString<ModuleOp>(print(*candidate.module), &context);
        require(bool(copy), "query realization did not parse");
        checked(checkOracleRealization(*prepared, *copy, record, policy));
        bool changed = false;
        copy->walk([&](func::CallOp call) {
          if (call.getCallee() !=
              candidate.entries[0].merkle[0].authenticate.getSymName())
            return;
          call->setOperand(3, call.getOperand(2));
          changed = true;
        });
        require(changed && succeeded(verify(*copy)),
                "authentication mutation must be well formed");
        refused(checkOracleRealization(*prepared, *copy, record, policy));
        copy = parseSourceString<ModuleOp>(print(*candidate.module), &context);
        changed = false;
        copy->walk([&](exec::VariantOp request) {
          if (request.getSite() != "window_request")
            return;
          require(request.getPayload().size() == 3,
                  "missing request coordinates");
          request.getPayloadMutable()[1].set(request.getPayload()[2]);
          changed = true;
        });
        require(changed && succeeded(verify(*copy)),
                "request mutation must be well formed");
        refused(checkOracleRealization(*prepared, *copy, record, policy));
        RunOptions options;
        options.oracleRealization = policy;
        auto run =
            take(compileRun(queryText, "oracle-query.mlir", options, registry));
        if (argc >= 2) {
          std::ofstream out(std::filesystem::path(argv[1]) /
                            ("query-" + name + ".bundle"));
          out << run.bundle;
          require(bool(out), "could not retain query bundle");
        }
      });
      runCase(name + " exact selection coverage", [&] {
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
        bad.order = static_cast<OracleQueryOrder>(99);
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
  for (unsigned mode : {0, 1, 2}) {
    std::string name = mode == 2   ? "query-zero-only"
                       : mode == 1 ? "query-zero-trailing"
                                   : "query-recurrence";
    runCase(name, [&] {
      auto text = virtualSource(mode != 0);
      if (mode == 2)
        text.replace(text.find("(%last,%position)"), 17, "(%empty,%position)");
      auto original = parseSourceString<ModuleOp>(text, &context);
      require(bool(original), "virtual query did not parse");
      auto owner = mathematical::PreparedProtocol::prepare(*original);
      require(bool(owner), "virtual query did not prepare");
      auto prepared = owner->snapshot();
      auto roots = take(resolveOracleRealizationSelection(*prepared, {}));
      for (auto &root : roots)
        root.realization = {scheme.str(), OracleLeafGrouping::AntipodalPairs,
                            OracleLeafOrder::Natural};
      OracleRealizationPolicy policy;
      policy.roots = roots;
      auto candidate = take(emitOracleRealization(*prepared, policy));
      auto record =
          take(serializeOracleRealization(*prepared, candidate, policy));
      checked(
          checkOracleRealization(*prepared, *candidate.module, record, policy));
      RunOptions options;
      options.oracleRealization = policy;
      auto run = take(
          compileRun(text, "oracle-virtual-query.mlir", options, registry));
      if (argc >= 2) {
        std::ofstream out(std::filesystem::path(argv[1]) / (name + ".bundle"));
        out << run.bundle;
        require(bool(out), "could not retain virtual query bundle");
      }
    });
  }
  for (StringRef mode : {"multiple", "mixed-kind", "mixed-scheme"}) {
    runCase("query-" + mode, [&] {
      std::ifstream input(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                          "query-constructors.mlir");
      require(bool(input), "missing constructor query fixture");
      std::string text((std::istreambuf_iterator<char>(input)), {});
      auto replace = [&](StringRef from, StringRef to) {
        size_t at = 0;
        while ((at = text.find(from.str(), at)) != std::string::npos) {
          text.replace(at, from.size(), to.str());
          at += to.size();
        }
      };
      if (mode == "multiple")
        replace("\"koala-bear\"", "\"koala-bear.ext4-binomial3\"");
      else if (mode == "mixed-scheme")
        replace("koala-bear.ext4-binomial3", "koala-bear");
      auto original = parseSourceString<ModuleOp>(text, &context);
      require(bool(original), "constructor query did not parse");
      auto owner = mathematical::PreparedProtocol::prepare(*original);
      require(bool(owner), "constructor query did not prepare");
      auto prepared = owner->snapshot();
      auto roots = take(resolveOracleRealizationSelection(*prepared, {}));
      require(roots.size() == 2, "wrong constructor inventory");
      roots[0].realization = {
          mode == "mixed-scheme" ? "rows.merkle-poseidon2-16.koala-bear/0"
                                 : scheme.str(),
          OracleLeafGrouping::AntipodalPairs, OracleLeafOrder::Natural};
      roots[1].realization = {
          mode == "multiple" ? scheme.str()
                             : "rows.merkle-keccak256.koala-bear/0",
          OracleLeafGrouping::AntipodalPairs, OracleLeafOrder::Natural};
      OracleRealizationPolicy policy;
      policy.roots = roots;
      auto candidate = take(emitOracleRealization(*prepared, policy));
      auto record =
          take(serializeOracleRealization(*prepared, candidate, policy));
      auto copy =
          parseSourceString<ModuleOp>(print(*candidate.module), &context);
      require(bool(copy), "constructor realization did not parse");
      checked(checkOracleRealization(*prepared, *copy, record, policy));
      bool changed = false;
      copy->walk([&](exec::ApplyOp op) {
        if (!op.getSite().ends_with("_request_constructor_equal"))
          return;
        require(op.getInputs().size() == 2,
                "missing constructor comparison inputs");
        op.getInputsMutable()[1].set(op.getInputs()[0]);
        changed = true;
      });
      require(changed && succeeded(verify(*copy)),
              "constructor guard mutation must be well formed");
      refused(checkOracleRealization(*prepared, *copy, record, policy));
      if (mode == "multiple") {
        copy = parseSourceString<ModuleOp>(print(*candidate.module), &context);
        changed = false;
        copy->walk([&](exec::VariantOp op) {
          if (!op.getSite().ends_with("_response") ||
              op.getAlternative() != "Constructor0")
            return;
          op->setAttr("alternative", StringAttr::get(&context, "Constructor1"));
          changed = true;
        });
        require(changed && succeeded(verify(*copy)),
                "response alternative mutation must be well formed");
        refused(checkOracleRealization(*prepared, *copy, record, policy));
      }
      RunOptions options;
      options.oracleRealization = policy;
      auto run =
          take(compileRun(text, "oracle-constructors.mlir", options, registry));
      if (argc >= 2) {
        std::ofstream output(std::filesystem::path(argv[1]) /
                             ("query-" + mode.str() + ".bundle"));
        output << run.bundle;
        require(bool(output), "could not retain constructor query bundle");
      }
    });
  }
  runCase("selection order is canonical", [&] {
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
    auto returned = text.find("  \"protocol.return\"");
    text.insert(returned,
                "%answer = \"protocol.oracle_query\"(%handle,%rows) "
                "{owner=\"V\",site=\"read\"} : "
                "(!H,ui64)->!algebra.field<\"koala-bear.ext4-binomial3\">\n");
    auto withQuery = parseSourceString<ModuleOp>(text, &context);
    require(bool(withQuery), "two-root query did not parse");
    auto queryOwner = mathematical::PreparedProtocol::prepare(*withQuery);
    require(bool(queryOwner), "two-root query did not prepare");
    auto queryPrepared = queryOwner->snapshot();
    auto queried = take(emitOracleRealization(*queryPrepared, policy));
    auto queryRecord =
        take(serializeOracleRealization(*queryPrepared, queried, policy));
    checked(checkOracleRealization(*queryPrepared, *queried.module, queryRecord,
                                   policy));
  });
  runCase("query policies never silently fall back", [&] {
    auto text = source(false, false, true);
    auto replace = [&](StringRef before, StringRef after) {
      auto found = text.find(before);
      require(found != std::string::npos, "missing service fixture slot");
      text.replace(found, before.size(), after);
    };
    replace("module {",
            "!R = !protocol.service_ref<\"random.bls12-381.fr/0\">\nmodule {");
    replace("%position:ui64)", "%position:ui64,%random:!R)");
    replace("function_type=(!D,ui64,ui64)", "function_type=(!D,ui64,ui64,!R)");
    replace("input_roles=[[\"P\"],[\"P\",\"V\"],[\"V\"]]",
            "input_roles=[[\"P\"],[\"P\",\"V\"],[\"V\"],[\"V\"]]");
    replace("%answer = ", "%challenge = \"protocol.query\"(%random) "
                          "{owner=\"V\",method=\"draw\",site=\"challenge\"} : "
                          "(!R)->!algebra.field<\"bls12-381.fr\">\n%answer = ");
    auto original = parseSourceString<ModuleOp>(text, &context);
    require(bool(original), "query fixture did not parse");
    auto owner = mathematical::PreparedProtocol::prepare(*original);
    require(bool(owner), "query fixture did not prepare");
    auto prepared = owner->snapshot();
    auto roots = take(resolveOracleRealizationSelection(*prepared, {}));
    OracleRealizationPolicy policy;
    policy.order = OracleQueryOrder::AfterFinalDraw;
    auto ideal = take(emitOracleRealization(*prepared, policy));
    auto idealRecord =
        take(serializeOracleRealization(*prepared, ideal, policy));
    checked(
        checkOracleRealization(*prepared, *ideal.module, idealRecord, policy));
    for (auto &root : roots)
      root.realization = {scheme.str(), OracleLeafGrouping::AntipodalPairs,
                          OracleLeafOrder::Natural};
    policy.roots = roots;
    auto candidate = take(emitOracleRealization(*prepared, policy));
    auto record =
        take(serializeOracleRealization(*prepared, candidate, policy));
    checked(
        checkOracleRealization(*prepared, *candidate.module, record, policy));
    RunOptions options;
    options.oracleRealization = policy;
    auto run =
        take(compileRun(text, "oracle-final-draw.mlir", options, registry));
    auto edge = run.compilation.oracleRealizationSnapshot();
    require(bool(edge), "service-bearing compilation lost realization edge");
    checked(checkOracleRealization(*edge->original, *edge->candidate,
                                   edge->record, policy));
  });
  for (StringRef mode : {"paired", "individual", "reversed", "invalid-first",
                         "invalid-later", "guard", "guarded-position"})
    runCase("batch-" + mode, [&] {
      std::ifstream file(std::filesystem::path(ZKC_ORACLE_FIXTURES) /
                         "query-blocks.mlir");
      std::string text((std::istreambuf_iterator<char>(file)), {});
      auto replace = [&](StringRef before, StringRef after) {
        auto found = text.find(before);
        require(found != std::string::npos, "missing batch fixture slot");
        text.replace(found, before.size(), after);
      };
      if (mode == "invalid-first")
        replace("%x = \"protocol.oracle_query\"(%a,%zero)",
                "%x = \"protocol.oracle_query\"(%a,%position)");
      if (mode == "invalid-later")
        replace("%y = \"protocol.oracle_query\"(%a,%four)",
                "%y = \"protocol.oracle_query\"(%a,%position)");
      if (mode == "guard")
        replace("  %y = ",
                "  \"protocol.guard\"(%allow) "
                "{owner=\"V\",site=\"early_barrier\"} : (i1)->()\n  %y = ");
      if (mode == "guarded-position") {
        replace("  %x = ",
                "  %within = \"data.index_less\"(%position,%rows) : "
                "(ui64,ui64)->i1\n"
                "  \"protocol.guard\"(%within) "
                "{owner=\"V\",site=\"position_bound\"} : (i1)->()\n  %x = ");
        replace("%x = \"protocol.oracle_query\"(%a,%zero)",
                "%x = \"protocol.oracle_query\"(%a,%position)");
        replace("%z = \"protocol.oracle_query\"(%a,%zero)",
                "%z = \"protocol.oracle_query\"(%a,%position)");
      }
      auto original = parseSourceString<ModuleOp>(text, &context);
      require(bool(original), "batch fixture did not parse");
      auto owner = mathematical::PreparedProtocol::prepare(*original);
      require(bool(owner), "batch fixture did not prepare");
      auto prepared = owner->snapshot();
      OracleRealizationPolicy policy;
      policy.order = OracleQueryOrder::AfterFinalDraw;
      policy.authentication = OracleAuthentication::AtomicBlocks;
      policy.roots = take(resolveOracleRealizationSelection(*prepared, policy));
      for (auto &root : *policy.roots)
        root.realization = {scheme.str(),
                            mode == "individual"
                                ? OracleLeafGrouping::Individual
                                : OracleLeafGrouping::AntipodalPairs,
                            mode == "reversed" ? OracleLeafOrder::BitReversed
                                               : OracleLeafOrder::Natural};
      auto candidate = take(emitOracleRealization(*prepared, policy));
      auto record =
          take(serializeOracleRealization(*prepared, candidate, policy));
      auto copy =
          parseSourceString<ModuleOp>(print(*candidate.module), &context);
      require(bool(copy), "batch candidate did not parse");
      checked(checkOracleRealization(*prepared, *copy, record, policy));
      auto encoded = take(json::parse(record));
      auto *blocks = encoded.getAsObject()
                         ->getArray("entries")
                         ->front()
                         .getAsObject()
                         ->getArray("query_blocks");
      unsigned count = mode == "guard" ? 3 : 2;
      require(blocks && blocks->size() == count,
              "wrong batch barrier partition");
      auto &firstBlock = *blocks->front().getAsObject();
      auto *queries = firstBlock.getArray("queries");
      require(queries && queries->size() == (mode == "guard" ? 1u : 4u),
              "logical source occurrence coverage changed");
      require(firstBlock.get("packet_capacity")->getAsUINT64() ==
                  (mode == "guard" ? 3u : 4u) &&
                  !firstBlock.get("request_groups"),
              "dynamic packet bound or record schema differs");
      firstBlock["packet_capacity"] = 1;
      std::string changedRecord;
      raw_string_ostream(changedRecord) << encoded;
      refused(checkOracleRealization(*prepared, *copy, changedRecord, policy));
      bool mutated = false;
      copy->walk([&](protocol_ir::LocalCallOp call) {
        if (!mutated && call.getSite().contains("opening_group") &&
            call->getNumResults() == 2 && !call.getInputs().empty()) {
          call->getResult(0).replaceAllUsesWith(call.getInputs()[0]);
          mutated = true;
        }
      });
      require(mutated && succeeded(verify(*copy)),
              "physical request substitution must preserve formation");
      refused(checkOracleRealization(*prepared, *copy, record, policy));
      if (mode == "paired") {
        for (unsigned field : {1u, 2u}) {
          auto packetCopy =
              parseSourceString<ModuleOp>(print(*candidate.module), &context);
          bool changed = false;
          packetCopy->walk([&](exec::VariantOp pack) {
            if (changed || !pack.getSite().ends_with("_key") ||
                pack.getPayload().size() != 3)
              return;
            pack->setOperand(1 + field, pack.getPayload()[field - 1]);
            changed = true;
          });
          require(changed && succeeded(verify(*packetCopy)),
                  "physical key mutation must preserve formation");
          refused(checkOracleRealization(*prepared, *packetCopy, record, policy));
        }
      }
      auto invalid = parseSourceString<ModuleOp>(print(*prepared), &context);
      invalid->walk([&](data::IndexOp index) {
        if (index.getValue() == 0)
          index.setValue(8);
      });
      require(succeeded(verify(*invalid)),
              "domain mutation must preserve formation");
      refused(
          checkOracleRealization(*invalid, *candidate.module, record, policy));
      auto individual = policy;
      individual.authentication = OracleAuthentication::PerQuery;
      refused(checkOracleRealization(*prepared, *candidate.module, record,
                                     individual));
      RunOptions options;
      options.oracleRealization = policy;
      auto run =
          take(compileRun(text, "oracle-blocks.mlir", options, registry));
      auto edge = run.compilation.oracleRealizationSnapshot();
      require(bool(edge), "batch compilation lost checked edge");
      checked(checkOracleRealization(*edge->original, *edge->candidate,
                                     edge->record, policy));
      if (argc >= 2) {
        std::ofstream out(std::filesystem::path(argv[1]) /
                          ("batch-" + mode.str() + ".bundle"));
        out << run.bundle;
        require(bool(out), "could not retain batch bundle");
      }
    });
  require(selectedCase, "no selected root/query test case");
  return cases.result();
}
