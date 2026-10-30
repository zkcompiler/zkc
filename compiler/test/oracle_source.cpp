#include "../lib/Compiler/ComponentContracts.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/OracleObligations.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/JSON.h"
#include <fstream>
#include <set>
using namespace llvm;
using namespace zkc::test;
using namespace zkc::protocol;
namespace {
using A = json::Array;
using J = json::Value;
std::string source() {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">, 16 : ui64]>
#U = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">]>
!F = !algebra.field<"koala-bear">
!D = !algebra.field_vector<"koala-bear">
!H = !protocol.oracle<#K>
!U = !protocol.oracle<#U>
!S = !protocol.oracle_sequence<#U, 4>
module { "protocol.module"() ({
  func.func private @identity(%value:!F)->!F { return %value : !F }
  relation.declare @admissible {kind="external",key="test/virtual",revision="0",
    signature=(!D,ui64)->i1,purposes=["witness","parameter"]}
  "protocol.oracle"() ({
   ^bb0(%source:!H,%parameter:ui64,%position:ui64):
    %first = "protocol.oracle_query"(%source,%position) {site="first"} : (!H,ui64)->!F
    %second = "protocol.oracle_query"(%source,%position) {site="second"} : (!H,ui64)->!F
    %value = func.call @identity(%first) : (!F)->!F
    "protocol.oracle_yield"(%value) : (!F)->()
  }) {sym_name="select",function_type=(!H,ui64,ui64)->!F,kind=#K,shape_arguments={},shape_bounds={},
      admissibility=@admissible} : ()->()
  "protocol.func"() ({
   ^bb0(%data:!D,%anchor:!H,%rows:ui64,%position:ui64):
    %input = "protocol.oracle_input"(%data,%anchor) {shape_bounds={},holder="P",receivers=["V"]} : (!D,!H)->!H
    %sent = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="sent"} : (!D,ui64)->!H
    %virtual = "protocol.oracle_virtual"(%input,%rows) {callee=@select,holder="P",receivers=["V"]} : (!H,ui64)->!H
    %contents = "protocol.oracle_contents"(%virtual) {owner="P"} : (!H)->!D
    %answer = "protocol.oracle_query"(%virtual,%position) {owner="V",site="read"} : (!H,ui64)->!F
    %unsized = "protocol.oracle_forget_shape"(%sent) : (!H)->!U
    %empty = "protocol.oracle_sequence_empty"() : ()->!S
    %sequence = "protocol.oracle_sequence_append"(%empty,%unsized) {roles=["P","V"],site="append"} : (!S,!U)->!S
    %selected = "protocol.oracle_sequence_at"(%sequence,%position) {roles=["P","V"],site="select"} : (!S,ui64)->!U
    %count = "protocol.oracle_sequence_length"(%sequence) : (!S)->ui64
    %shape = "protocol.oracle_shape"(%selected) {dimension="rows"} : (!U)->ui64
    %held, %returned = "protocol.oracle_components"(%selected) {holder="P",receivers=["V"]} : (!U)->(!D,!U)
    %ok = arith.constant true
    "protocol.return"(%held,%returned,%ok) : (!D,!U,i1)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!D,!H,ui64,ui64)->(!D,!U,i1),
      roles=["P","V"],input_roles=[["P"],["V"],["P","V"],["P","V"]],
      output_roles=[["P"],["V"],["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string replaceText(std::string text, StringRef before, StringRef after) {
  auto position = text.find(before.str());
  require(position != std::string::npos, "missing mutation target");
  text.replace(position, before.size(), after.str());
  return text;
}
const J &at(const J &value, ArrayRef<unsigned> path) {
  auto *result = &value;
  for (auto index : path) {
    auto array = result->getAsArray();
    require(array && index < array->size(), "invalid structured row");
    result = &(*array)[index];
  }
  return *result;
}
J kind(bool sized = true) {
  A arguments{
      A{"type", A{"apply", "field", A{A{"domain", "Field", "koala-bear"}}}}};
  if (sized)
    arguments.push_back(A{"nat", "16"});
  return A{"table", std::move(arguments)};
}
} // namespace
int main(int argc, char **argv) {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  mlir::ScopedDiagnosticHandler silence(
      &context, [](mlir::Diagnostic &) { return mlir::success(); });
  auto capture = [&](StringRef text) {
    return exportStructuredSource(text, "main", context);
  };
  if (argc >= 2 && argc <= 4) {
    auto exported = take(capture(source()));
    std::ofstream out(argv[1]);
    out << exported.bytes;
    out.close();
    require(bool(out), "failed to write independent-reader fixture");
    if (argc >= 3) {
      std::ofstream report(argv[2]);
      report << take(exportOracleObligations(source(), "main", context));
      report.close();
      require(bool(report), "failed to write oracle obligation fixture");
    }
    if (argc == 4) {
      std::ofstream original(argv[3]);
      original << source();
      original.close();
      require(bool(original), "failed to write oracle original fixture");
    }
    return 0;
  }
  Cases cases;
  cases.run(
      "generated oracle obligations address the exact original rows", [&] {
        auto snapshot = take(json::parse(take(capture(source())).bytes));
        auto bytes = take(exportOracleObligations(source(), "main", context));
        auto report = take(json::parse(bytes));
        A conditions{A{"query_domain", A{7, 1, 7, 1, 0}},
                     A{"query_domain", A{7, 1, 7, 1, 1}},
                     A{"input_pair", A{7, 2, 9, 1, 0}},
                     A{"send_shape", A{7, 2, 9, 1, 1}},
                     A{"virtual_admissibility", A{7, 2, 9, 1, 2}},
                     A{"query_domain", A{7, 2, 9, 1, 4}}};
        A footprints{
            A{1, 1, A{A{A{7, 1, 7, 1, 0}, 0, 2}, A{A{7, 1, 7, 1, 1}, 0, 3}}}};
        require(report ==
                    J(A{"zkc.oracle-obligations/0", at(snapshot, {2}), "main",
                        std::move(conditions), std::move(footprints)}),
                "oracle proposal changed actual rows or positions");
        if (auto e = checkOracleObligations(source(), "main", bytes, context))
          require(false, toString(std::move(e)));
        for (unsigned mutation = 0; mutation < 7; ++mutation) {
          auto changed = report;
          auto &root = *changed.getAsArray();
          auto &rows = *root[3].getAsArray();
          if (mutation == 0)
            root[1] = "wrong-source";
          if (mutation == 1)
            root[2] = "wrong-entry";
          if (mutation == 2)
            rows.erase(rows.begin());
          if (mutation == 3)
            rows.push_back(rows.front());
          if (mutation == 4)
            std::swap(rows[0], rows[1]);
          if (mutation == 5)
            root[4] = A{A{1, 1, A{A{A{7, 1, 7, 1, 0}, 0, 2}}}};
          if (mutation == 6)
            root.push_back(nullptr);
          std::string text;
          raw_string_ostream stream(text);
          stream << changed;
          auto e = checkOracleObligations(source(), "main", text, context);
          require(bool(e), "modified obligation proposal admitted");
          require(namesIdentifier(toString(std::move(e)),
                                  "oracle-obligations-mismatch"),
                  "unexpected obligation proposal refusal");
        }
      });
  cases.run("oracle proposals refuse malformed and oversized input", [&] {
    auto reject = [&](StringRef proposal, StringRef code) {
      auto error = checkOracleObligations(source(), "main", proposal, context);
      require(bool(error), "malformed oracle proposal admitted");
      require(namesIdentifier(toString(std::move(error)), code),
              "unexpected malformed proposal refusal");
    };
    for (StringRef proposal : {"[", "[-1]", "[1.0]", "[1e0]"})
      reject(proposal, "oracle-obligations-shape");
    for (const auto &proposal : {std::string(1024 * 1024 + 1, ' '),
                                 std::string(17, '[') + std::string(17, ']')})
      reject(proposal, "oracle-obligations-limit");
  });
  cases.run("query templates retain their nested iteration address", [&] {
    auto text =
        replaceText(source(),
                    "%answer = \"protocol.oracle_query\"(%virtual,%position) "
                    "{owner=\"V\",site=\"read\"} : (!H,ui64)->!F",
                    R"mlir(
    "protocol.repeat"(%rows,%virtual,%position) ({
      ^bb0(%i:ui64,%word:!H,%at:ui64):
       %answer = "protocol.oracle_query"(%word,%at) {owner="V",site="read"} : (!H,ui64)->!F
       "protocol.yield"() : ()->()
    }) {site="iteration",carried=0:i64,maximum=16:i64,roles=["P","V"],carried_roles=[]} : (ui64,!H,ui64)->()
    )mlir");
    auto report =
        take(json::parse(take(exportOracleObligations(text, "main", context))));
    require(at(report, {3, 5}) ==
                J(A{"query_domain", A{7, 2, 9, 1, 4, 3, 0, 2, 1, 0}}),
            "query was flattened out of its iteration");
  });
  cases.run(
      "anchor contracts retain data associations without role reads", [&] {
        auto text =
            replaceText(source(), "sym_name=\"main\",", R"mlir(sym_name="main",
      contracts=[
        ["input","initial",[@admissible,[["anchor","input",1:i64],["input",2:i64,"P"]]],unit,unit],
        ["output","result",[@admissible,[["anchor","output",1:i64],["input",2:i64,"P"]]],unit,unit]],)mlir");
        auto snapshot = take(json::parse(take(capture(text)).bytes));
        require(at(snapshot, {8, 0, 1, 0, 2, 1, 0}) ==
                        J(A{"anchor", "input", 1}) &&
                    at(snapshot, {8, 0, 1, 1, 2, 1, 0}) ==
                        J(A{"anchor", "output", 1}),
                "anchor selector became a role-local data selector");
        refuses(zkc::language::deriveComponentContracts(snapshot),
                "component-seam-oracle");
        for (StringRef replacement :
             {"[\"anchor\",\"input\",0:i64]", "[\"anchor\",\"input\",4:i64]",
              "[\"anchor\",\"input\",-1:i64]", "[\"anchor\",\"input\",1:i32]",
              "[\"anchor\",\"other\",1:i64]",
              "[\"anchor\",\"input\",1:i64,\"V\"]"})
          refuses(capture(replaceText(text, "[\"anchor\",\"input\",1:i64]",
                                      replacement)),
                  "structured-source-original");
        refuses(capture(replaceText(text, "signature=(!D,ui64)->i1",
                                    "signature=(!F,ui64)->i1")),
                "structured-source-original");
      });
  cases.run(
      "original oracle bodies preserve identities roles and repeated queries",
      [&] {
        auto exported = take(capture(source()));
        auto snapshot = take(json::parse(exported.bytes));
        require(snapshot.getAsArray()->size() == 11,
                "second source envelope introduced");
        auto &declaration = *at(snapshot, {7, 1}).getAsArray();
        require(declaration.size() == 8 && declaration[0] == J("oracle") &&
                    declaration[1] == J("select") && declaration[3] == kind() &&
                    declaration[4] == J("admissible") &&
                    declaration[5] == J(A{}) && declaration[6] == J(A{}),
                "virtual declaration changed");
        require(at(snapshot, {7, 1, 7, 1}).getAsArray()->size() == 3,
                "unused query disappeared");
        require(at(snapshot, {7, 1, 7, 1, 0, 0}) ==
                        J(A{"oracle_query", nullptr, kind()}) &&
                    at(snapshot, {7, 1, 7, 1, 0, 1}) == J(A{0, 2}) &&
                    at(snapshot, {7, 1, 7, 1, 1, 1}) == J(A{1, 3}) &&
                    at(snapshot, {7, 1, 7, 1, 0, 4}) == J("first") &&
                    at(snapshot, {7, 1, 7, 1, 1, 4}) == J("second"),
                "query order or coordinates changed");
        require(at(snapshot, {7, 2, 4, 1}) ==
                    J(A{"oracle", "table", (*kind().getAsArray())[1]}),
                "interface anchor erased");
        auto &ops = *at(snapshot, {7, 2, 9, 1}).getAsArray();
        require(ops.size() == 13, "oracle operation lost");
        require(at(ops[0], {0}) ==
                    J(A{"oracle_input", "P", A{"V"}, kind(), A{}}),
                "input binding changed");
        require(at(ops[1], {0}) ==
                    J(A{"oracle_send", "P", A{"V"}, kind(), A{"rows"}, A{}}),
                "send changed");
        require(at(ops[2], {0}) ==
                    J(A{"oracle_virtual", "select", "P", A{"V"}, kind()}),
                "virtual constructor changed");
        require(at(ops[4], {0}) == J(A{"oracle_query", "V", kind()}),
                "query owner changed");
        require(at(ops[5], {0}) ==
                    J(A{"oracle_forget_shape", kind(), kind(false)}),
                "refinement erased");
        require(at(ops[6], {2, 0}) == J(A{"oracle_sequence", "table",
                                          (*kind(false).getAsArray())[1], "4"}),
                "bounded sequence erased");
        require(at(ops[7], {0}) == J(A{"oracle_sequence_append", kind(false),
                                       "4", A{"P", "V"}}),
                "append stop or roles lost");
        require(at(ops[8], {0}) ==
                    J(A{"oracle_sequence_at", kind(false), "4", A{"P", "V"}}),
                "selection stop or roles lost");
        require(at(ops[11], {0}) ==
                    J(A{"oracle_components", "P", A{"V"}, kind(false)}),
                "paired view lost");
        // Every exact exported row has a unique coordinate and the original
        // token.
        std::set<std::vector<unsigned>> rows;
        auto written = source();
        for (const auto &row : exported.associations) {
          at(snapshot, row.row);
          require(rows.insert(row.row).second && row.original.has_value(),
                  "missing row provenance");
          const auto &range = *row.original;
          require(range.begin < range.end && range.end <= written.size(),
                  "invalid source association");
          auto text = StringRef(written).slice(range.begin, range.end);
          if (text.starts_with("\"") && text.ends_with("\""))
            text = text.drop_front().drop_back();
          StringRef operation = row.operation;
          require(text == operation || text == operation.rsplit('.').second,
                  "source association names a different operation");
        }
        require(rows.size() == 24, "source row coverage changed");
        require(rows.count({7, 1, 7, 1, 0}) && rows.count({7, 1, 7, 2}),
                "virtual body associations absent");
      });
  cases.run(
      "oracle data is not silently admitted as a pure component seam", [&] {
        auto snapshot = take(json::parse(take(capture(source())).bytes));
        auto empty = take(zkc::language::deriveComponentContracts(snapshot));
        require(empty.getArray("seams")->empty() &&
                    empty.getArray("proposals")->empty(),
                "clause-free source acquired component evidence");
        // A retained linear declaration activates component dependency
        // derivation. Its ordinary contract path must refuse oracle operations
        // explicitly.
        auto &declarations = *(*snapshot.getAsArray())[10].getAsArray();
        declarations[0].getAsArray()->push_back(
            A{A{"nominal", "record", "tests::Pending", A{}}, "linear", true,
              A{}});
        if (auto error = zkc::language::checkComponentDeclarations(
                (*snapshot.getAsArray())[10]))
          require(false, toString(std::move(error)));
        auto seams = zkc::language::deriveComponentContracts(snapshot);
        require(!seams, "oracle route received ordinary pure seam authority");
        require(toString(seams.takeError()).find("component-seam-oracle") !=
                    std::string::npos,
                "unexpected seam refusal");
      });
  cases.run(
      "all retained oracle attributes and actual declarations are checked",
      [&] {
        for (auto text :
             {replaceText(source(), "admissibility=@admissible",
                          "admissibility=@missing"),
              replaceText(source(), "callee=@select", "callee=@identity"),
              replaceText(source(), "{owner=\"V\",site=\"read\"}",
                          "{owner=\"P\",site=\"read\",unchecked=1:ui64}"),
              replaceText(source(), "{site=\"second\"}", "{site=\"first\"}")}) {
          auto result = capture(text);
          require(!result, "malformed oracle export accepted");
          consumeError(result.takeError());
        }
      });
  cases.run("unsigned kind and capacity fields preserve their full width", [&] {
    auto text =
        replaceText(source(), "16 : ui64", "18446744073709551615 : ui64");
    text = replaceText(text, "#U, 4>", "#U, 18446744073709551615>");
    auto snapshot = take(json::parse(take(capture(text)).bytes));
    require(at(snapshot, {7, 1, 3, 1, 1, 1}) == J("18446744073709551615"),
            "kind natural narrowed");
    require(at(snapshot, {7, 2, 9, 1, 6, 2, 0, 3}) == J("18446744073709551615"),
            "capacity narrowed");
  });
  cases.run(
      "unsized shapes and associated collection sorts stay explicit", [&] {
        auto text = replaceText(source(), ", 16 : ui64", "");
        text = replaceText(text, "shape_arguments={}",
                           "shape_arguments={rows=1:ui64}");
        for (unsigned i = 0; i < 3; ++i)
          text = replaceText(text, "shape_bounds={}",
                             "shape_bounds={rows=64:ui64}");
        // Forgetting rows requires an actual sized refinement, so use the same
        // unsized handle directly in this case.
        text = replaceText(
            text,
            "    %unsized = \"protocol.oracle_forget_shape\"(%sent) "
            ": (!H)->!U\n",
            "");
        text = replaceText(text, "(%empty,%unsized)", "(%empty,%sent)");
        auto snapshot = take(json::parse(take(capture(text)).bytes));
        require(at(snapshot, {7, 1, 5}) == J(A{A{"rows", "1"}}) &&
                    at(snapshot, {7, 1, 6}) == J(A{A{"rows", "64"}}),
                "dynamic shape signature lost");
        require(at(snapshot, {7, 2, 9, 1, 0, 0, 4}) == J(A{A{"rows", "64"}}) &&
                    at(snapshot, {7, 2, 9, 1, 1, 0, 5}) ==
                        J(A{A{"rows", "64"}}),
                "dynamic maximum lost");
        for (bool index : {true, false}) {
          auto typed = source();
          const std::string field = "!algebra.field<\"koala-bear\">";
          const std::string target =
              index ? "ui64" : "!algebra.group<\"bls12-381.g1\">";
          size_t position;
          while ((position = typed.find(field)) != std::string::npos)
            typed.replace(position, field.size(), target);
          typed =
              replaceText(typed, "!algebra.field_vector<\"koala-bear\">",
                          index ? "!algebra.indices"
                                : "!algebra.group_vector<\"bls12-381.g1\">");
          auto result = take(json::parse(take(capture(typed)).bytes));
          require(at(result, {7, 2, 4, 0}) ==
                      (index ? J(A{"apply", "indices", A{}})
                             : J(A{"apply", "groups",
                                   A{A{"domain", "Group", "bls12-381.g1"}}})),
                  "associated Data collection changed");
        }
      });
  return cases.result();
}
