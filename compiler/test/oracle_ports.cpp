#include "../lib/Dialect/Protocol/IR/OracleAnalysis.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Mathematical.h"
using namespace mlir;
using namespace zkc::test;
using namespace zkc::protocol_ir;
namespace {
std::string source() {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">, 16 : ui64]>
!F = !algebra.field<"koala-bear">
!D = !algebra.field_vector<"koala-bear">
!H = !protocol.oracle<#K>
module {
 "protocol.module"() ({
  "protocol.func"() ({
   ^bb0(%data:!D,%anchor:!H,%rows:ui64,%position:ui64):
    %word = "protocol.oracle_input"(%data,%anchor) {holder="A",receivers=["B"]} : (!D,!H)->!H
    %contents = "protocol.oracle_contents"(%word) {owner="A"} : (!H)->!D
    %value = "protocol.oracle_query"(%word,%position) {owner="B",site="read"} : (!H,ui64)->!F
    %parts:2 = "protocol.oracle_components"(%word) {holder="A",receivers=["B"]} : (!H)->(!D,!H)
    "protocol.return"(%parts#0,%parts#1,%value) : (!D,!H,!F)->()
  }) {sym_name="reader",function_type=(!D,!H,ui64,ui64)->(!D,!H,!F),
      roles=["A","B"],input_roles=[["A"],["B"],["A","B"],["B"]],
      output_roles=[["A"],["B"],["B"]]} : ()->()
  "protocol.func"() ({
   ^bb0(%data:!D,%rows:ui64,%position:ui64):
    %word = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="word"} : (!D,ui64)->!H
    %parts:2 = "protocol.oracle_components"(%word) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
    %result:3 = "protocol.apply"(%parts#0,%parts#1,%rows,%position) {callee=@reader,roles=["P","V"],site="call"} : (!D,!H,ui64,ui64)->(!D,!H,!F)
    %returned = "protocol.oracle_input"(%result#0,%result#1) {holder="P",receivers=["V"]} : (!D,!H)->!H
    %contents = "protocol.oracle_contents"(%returned) {owner="P"} : (!H)->!D
    %value = "protocol.oracle_query"(%returned,%position) {owner="V",site="again"} : (!H,ui64)->!F
    "protocol.return"(%value) : (!F)->()
  }) {sym_name="example",function_type=(!D,ui64,ui64)->!F,
      roles=["P","V"],input_roles=[["P"],["P","V"],["V"]],
      output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->()
})mlir";
}
std::string replace(std::string text, llvm::StringRef before,
                    llvm::StringRef after) {
  auto pos = text.find(before.str());
  require(pos != std::string::npos, "missing port mutation target");
  text.replace(pos, before.size(), after.str());
  return text;
}
OwningOpRef<ModuleOp> parse(llvm::StringRef text, MLIRContext &context) {
  auto module =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module), "port fixture did not parse");
  return module;
}
std::string dynamic() {
  auto text = replace(source(), ", 16 : ui64", "");
  size_t start = 0;
  for (llvm::StringRef pattern : {"{holder=", "{sender="}) {
    start = 0;
    while ((start = text.find(pattern.str(), start)) != std::string::npos) {
      // Only binding/sending operations own a shape maximum; component views do
      // not.
      auto line =
          text.substr(text.rfind('\n', start), start - text.rfind('\n', start));
      if (line.find("oracle_input") != std::string::npos ||
          line.find("oracle_send") != std::string::npos) {
        text.insert(start + 1, "maximum_rows=32:ui64,");
        start += 22;
      }
      start += pattern.size();
    }
  }
  return text;
}
} // namespace
int main() {
  DialectRegistry registry;
  zkc::registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  auto accepted = [&](llvm::StringRef text, bool prepare = false) {
    std::string message;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      message += diagnostic.str();
      return success();
    });
    auto module = parse(text, context);
    require(succeeded(verify(*module)),
            "valid oracle ports refused: " + message);
    if (prepare) {
      auto candidate = zkc::mathematical::prepareProtocol(*module);
      require(bool(candidate), "port preparation failed: " + message);
    }
  };
  auto refused = [&](llvm::StringRef text) {
    auto module = parse(text, context);
    require(failed(verify(*module)), "invalid oracle ports admitted");
  };
  cases.run(
      "entry and returned ports retain a paired role family through calls",
      [&] {
        accepted(source(), true);
        accepted(dynamic(), true);
      });
  cases.run(
      "raw handle entries require unique bindings and exact role leaves", [&] {
        refused(replace(source(),
                        "\"protocol.oracle_contents\"(%word) {owner=\"A\"}",
                        "\"protocol.oracle_contents\"(%anchor) {owner=\"A\"}"));
        refused(replace(source(), "input_roles=[[\"A\"],[\"B\"]",
                        "input_roles=[[\"A\",\"B\"],[\"B\"]"));
        refused(replace(source(), "input_roles=[[\"A\"],[\"B\"]",
                        "input_roles=[[\"A\"],[\"A\",\"B\"]"));
        refused(replace(source(), "{owner=\"A\"}", "{owner=\"B\"}"));
        refused(replace(source(), "{holder=\"A\",receivers=[\"B\"]}",
                        "{holder=\"B\",receivers=[\"A\"]}"));
        refused(replace(source(), "    %contents =", R"mlir(
    %extra = "protocol.oracle_input"(%data,%anchor) {holder="A",receivers=["B"]} : (!D,!H)->!H
    %contents =)mlir"));
      });
  cases.run(
      "root bindings precede protocol effects and remain when unused", [&] {
        refused(
            replace(source(), "    %word = \"protocol.oracle_input\"", R"mlir(
    %early = "protocol.oracle_send"(%data,%rows) {sender="A",receivers=["B"],site="early"} : (!D,ui64)->!H
    %word = "protocol.oracle_input")mlir"));
        auto original = parse(source(), context);
        auto candidate = zkc::mathematical::prepareProtocol(*original);
        require(bool(candidate), "root preparation failed");
        unsigned bindings = 0;
        candidate->walk([&](OracleInputOp) { ++bindings; });
        require(bindings == 3, "preparation dropped an input or rebound check");
      });
  cases.run("calls and result tuples cannot mix equal-typed components", [&] {
    refused(replace(source(), "\"protocol.apply\"(%parts#0,%parts#1",
                    "\"protocol.apply\"(%data,%parts#1"));
    refused(replace(source(), "\"protocol.return\"(%parts#0,%parts#1,%value)",
                    "\"protocol.return\"(%contents,%parts#1,%value)"));
    refused(replace(source(), "\"protocol.return\"(%parts#0,%parts#1,%value)",
                    "\"protocol.return\"(%parts#0,%word,%value)"));
    refused(replace(source(), "\"protocol.oracle_input\"(%result#0,%result#1",
                    "\"protocol.oracle_input\"(%parts#0,%result#1"));
    auto two = replace(source(), "    %result:3 =", R"mlir(
    %other = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="other"} : (!D,ui64)->!H
    %otherParts:2 = "protocol.oracle_components"(%other) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
    %result:3 =)mlir");
    accepted(two);
    refused(replace(two, "\"protocol.apply\"(%parts#0,%parts#1",
                    "\"protocol.apply\"(%parts#0,%otherParts#1"));
  });
  cases.run("shape reads preserve initial input and send dependencies", [&] {
    auto text = replace(dynamic(), "    %result:3 =", R"mlir(
    %actualRows = "protocol.oracle_rows"(%word) : (!H)->ui64
    %next = "protocol.oracle_send"(%data,%actualRows) {sender="P",receivers=["V"],site="next",maximum_rows=32:ui64} : (!D,ui64)->!H
    %result:3 =)mlir");
    accepted(text, true);
    auto returnedShape = replace(
        dynamic(), "    %contents = \"protocol.oracle_contents\"(%returned)",
        R"mlir(
    %actualRows = "protocol.oracle_rows"(%returned) : (!H)->ui64
    %next = "protocol.oracle_send"(%data,%actualRows) {sender="P",receivers=["V"],site="next",maximum_rows=32:ui64} : (!D,ui64)->!H
    %contents = "protocol.oracle_contents"(%returned))mlir");
    accepted(returnedShape, true);
    auto malformed = parse(source(), context);
    malformed->walk([&](OracleInputOp input) {
      input.setMaximumRowsAttr(IntegerAttr::get(
          IntegerType::get(&context, 64, IntegerType::Unsigned), 32));
    });
    require(failed(verify(*malformed)),
            "sized input accepted a second row maximum");
    auto unsized = dynamic();
    refused(replace(unsized, "maximum_rows=32:ui64,", ""));
  });
  cases.run(
      "unsized selection preserves answer-dependent shape information", [&] {
        auto text = replace(
            dynamic(), "!H = !protocol.oracle<#K>",
            "!H = !protocol.oracle<#K>\n!S = !protocol.oracle_sequence<#K, 2>");
        size_t at = 0;
        const std::string field = "!algebra.field<\"koala-bear\">";
        while ((at = text.find(field)) != std::string::npos)
          text.replace(at, field.size(), "ui64");
        text = replace(text, "!algebra.field_vector<\"koala-bear\">",
                       "!algebra.indices");
        text = replace(text, "    %result:3 =", R"mlir(
    %selector = "protocol.oracle_query"(%word,%position) {owner="V",site="selector"} : (!H,ui64)->!F
    %empty = "protocol.oracle_sequence_empty"() : ()->!S
    %sequence = "protocol.oracle_sequence_append"(%empty,%word) {roles=["V"],site="append"} : (!S,!H)->!S
    %selected = "protocol.oracle_sequence_at"(%sequence,%selector) {roles=["V"],site="select"} : (!S,ui64)->!H
    %selectedRows = "protocol.oracle_rows"(%selected) : (!H)->ui64
    %result:3 =)mlir");
        auto module = parse(text, context);
        require(succeeded(verify(*module)),
                "dynamic selection fixture refused");
        OracleQueryOp query;
        OracleRowsOp rows;
        module->walk([&](OracleQueryOp op) {
          if (op.getSite() == "selector")
            query = op;
        });
        module->walk([&](OracleRowsOp op) { rows = op; });
        SymbolTableCollection symbols;
        auto program = rows->getParentOfType<MathematicalOp>();
        unsigned remaining = 1000;
        require(query && rows &&
                    failed(zkc::mathematical::verifyInitialOracleShape(
                        rows.getRows(), program, rows, symbols, remaining)),
                "answer-selected dimensions became initial configuration");
        auto selection = rows.getHandle().getDefiningOp<OracleSequenceAtOp>();
        selection.getPositionMutable().set(query.getPosition());
        remaining = 1000;
        require(succeeded(zkc::mathematical::verifyInitialOracleShape(
                    rows.getRows(), program, rows, symbols, remaining)),
                "initially selected dimensions were refused");
        remaining = 0;
        require(failed(zkc::mathematical::verifyInitialOracleShape(
                    rows.getRows(), program, rows, symbols, remaining)),
                "exhausted shape analysis admitted another traversal");
      });
  cases.run(
      "shape substitution distinguishes two calls to the same declaration",
      [&] {
        auto text = source();
        const std::string field = "!algebra.field<\"koala-bear\">";
        size_t at;
        while ((at = text.find(field)) != std::string::npos)
          text.replace(at, field.size(), "ui64");
        text = replace(text, "!algebra.field_vector<\"koala-bear\">",
                       "!algebra.indices");
        text = replace(text, "  \"protocol.func\"()", R"mlir(
    func.func private @choose(%a:ui64,%b:ui64)->ui64 { return %a : ui64 }
    "protocol.func"())mlir");
        text = replace(text, "\"protocol.return\"(%parts#0,%parts#1,%value)",
                       "\"protocol.return\"(%parts#0,%parts#1,%position)");
        text = replace(text, "    \"protocol.return\"(%value)", R"mlir(
    %later:3 = "protocol.apply"(%parts#0,%parts#1,%rows,%value) {callee=@reader,roles=["P","V"],site="later"} : (!D,!H,ui64,ui64)->(!D,!H,!F)
    %shape = func.call @choose(%later#2,%result#2) : (ui64,ui64)->ui64
    "protocol.return"(%value))mlir");
        auto module = parse(text, context);
        require(succeeded(verify(*module)),
                "repeated-call shape fixture refused");
        func::CallOp shape;
        ApplyOp later;
        module->walk([&](func::CallOp op) { shape = op; });
        module->walk([&](ApplyOp op) {
          if (op.getSite() == "later")
            later = op;
        });
        require(shape && later, "missing repeated call controls");
        auto program = shape->getParentOfType<MathematicalOp>();
        SymbolTableCollection symbols;
        unsigned remaining = 1000;
        require(failed(zkc::mathematical::verifyInitialOracleShape(
                    shape.getResult(0), program, shape, symbols, remaining)),
                "an earlier application hid a later query-dependent actual "
                "argument");
        later.setOperand(3, program.getBody().front().getArgument(2));
        remaining = 1000;
        require(succeeded(zkc::mathematical::verifyInitialOracleShape(
                    shape.getResult(0), program, shape, symbols, remaining)),
                "initial actual arguments failed shape substitution");
      });
  cases.run(
      "preparation checks actual paired operands after role substitution", [&] {
        auto text = replace(source(), "    %result:3 =", R"mlir(
    %other = "protocol.oracle_send"(%data,%rows) {sender="P",receivers=["V"],site="other"} : (!D,ui64)->!H
    %otherParts:2 = "protocol.oracle_components"(%other) {holder="P",receivers=["V"]} : (!H)->(!D,!H)
    %result:3 =)mlir");
        auto original = parse(text, context);
        auto candidate = zkc::mathematical::prepareProtocol(*original, false);
        require(bool(candidate), "candidate preparation failed");
        OracleComponentsOp other;
        OracleInputOp selected;
        candidate->walk([&](OracleComponentsOp view) {
          auto send = view.getHandle().getDefiningOp<OracleSendOp>();
          if (send && send.getSite() == "other")
            other = view;
        });
        candidate->walk([&](OracleInputOp input) {
          if (!selected &&
              input->getParentOfType<MathematicalOp>().getSymName() ==
                  "example")
            selected = input;
        });
        require(other && selected, "missing prepared port components");
        selected.getDataMutable().set(other.getData());
        selected.getAnchorMutable().set(other.getAnchor());
        require(succeeded(verify(*candidate)),
                "pair-preserving mutation lost formation");
        require(
            failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), &candidate->getBody()->front())),
            "different equal-data anchor passed preparation correspondence");
      });
  return cases.result();
}
