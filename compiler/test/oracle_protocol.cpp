#include "../lib/Transforms/ProtocolApplications.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Transforms/Passes.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Passes.h"
using namespace mlir;
using namespace zkc::test;
using namespace zkc::protocol_ir;
namespace {
std::string source(llvm::StringRef body) {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">, 16 : ui64]>
#U = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">]>
!F = !algebra.field<"koala-bear">
!V = !algebra.field_vector<"koala-bear">
!H = !protocol.oracle<#K>
!U = !protocol.oracle<#U>
!S = !protocol.oracle_sequence<#K, 4>
module {
 "protocol.module"() ({
  "protocol.func"() ({
   ^bb0(%data: !V, %rows: ui64, %position: ui64, %trips: ui64):
)mlir" + body.str() +
         R"mlir(
   %ok = arith.constant true
   "protocol.return"(%ok) : (i1) -> ()
  }) {sym_name = "example", function_type = (!V, ui64, ui64, ui64) -> i1,
      roles = ["P", "V"], input_roles = [["P"], ["P", "V"], ["V"], ["P", "V"]],
      output_roles = [["V"]]} : () -> ()
 }) {profile = #protocol.profile<protocol>} : () -> ()
})mlir";
}
const char *send = R"mlir(
 %h = "protocol.oracle_send"(%data, %rows) {shape_names=["rows"],shape_bounds={},sender="P", receivers=["V"], site="layer"} : (!V, ui64) -> !H
 %answer = "protocol.oracle_query"(%h, %position) {owner="V", site="read"} : (!H, ui64) -> !F
)mlir";
std::string replace(std::string text, llvm::StringRef before,
                    llvm::StringRef after) {
  auto pos = text.find(before.str());
  require(pos != std::string::npos, "missing mutation target");
  text.replace(pos, before.size(), after.str());
  return text;
}
OwningOpRef<ModuleOp> parse(llvm::StringRef text, MLIRContext &context) {
  std::string message;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
    llvm::raw_string_ostream out(message);
    diagnostic.print(out);
    return success();
  });
  auto module =
      parseSourceString<ModuleOp>(text, ParserConfig(&context, false));
  require(bool(module), "oracle fixture did not parse: " + message);
  return module;
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
  auto accepted = [&](llvm::StringRef text) {
    auto module = parse(text, context);
    require(succeeded(zkc::admitStage(*module)),
            "valid oracle protocol refused");
  };
  auto refused = [&](llvm::StringRef text) {
    auto module = parse(text, context);
    require(failed(zkc::admitStage(*module)),
            "invalid oracle protocol admitted");
  };
  cases.run("sized sends and queries have checked role availability", [&] {
    accepted(source(send));
    refused(replace(source(send), "sender=\"P\", receivers=[\"V\"]",
                    "sender=\"V\", receivers=[\"P\"]"));
    refused(
        replace(source(send), "receivers=[\"V\"]", "receivers=[\"V\",\"V\"]"));
    refused(replace(source(send), "receivers=[\"V\"]", "receivers=[\"P\"]"));
    refused(replace(source(send), "receivers=[\"V\"]", "receivers=[]"));
    refused(replace(source(send), "owner=\"V\"", "owner=\"P\""));
    refused(replace(source(send), "site=\"read\"", "site=\"layer\""));
    refused(
        replace(source(send), "[[\"P\"], [\"P\", \"V\"]", "[[\"P\"], [\"P\"]"));
  });
  cases.run("dynamic shapes have one explicit unsigned maximum", [&] {
    auto dynamic = replace(source(send), "16 : ui64", "0 : ui64");
    accepted(dynamic);
    dynamic =
        replace(source(send), "[!algebra.field<\"koala-bear\">, 16 : ui64]",
                "[!algebra.field<\"koala-bear\">]");
    refused(dynamic);
    dynamic =
        replace(dynamic, "shape_bounds={}", "shape_bounds={rows=32 : ui64}");
    accepted(dynamic);
    accepted(replace(dynamic, "32 : ui64", "18446744073709551615 : ui64"));
    auto malformed = parse(dynamic, context);
    malformed->walk([&](OracleSendOp oracle) {
      oracle.setShapeBoundsAttr(DictionaryAttr::get(
          &context, {NamedAttribute(StringAttr::get(&context, "rows"),
                                    IntegerAttr::get(
                                        IntegerType::get(&context, 64), 32))}));
    });
    require(failed(zkc::admitStage(*malformed)),
            "signedness of row maximum was ignored");
    refused(replace(source(send), "shape_bounds={}",
                    "shape_bounds={rows=32 : ui64}"));
  });
  cases.run("shape dimensions and dynamic bounds have exact kind names", [&] {
    auto value = source(send);
    refused(replace(value, "shape_names=[\"rows\"]", "shape_names=[]"));
    refused(replace(value, "shape_names=[\"rows\"]", "shape_names=[\"vars\"]"));
    refused(replace(value, "shape_names=[\"rows\"]",
                    "shape_names=[\"rows\",\"rows\"]"));
    refused(replace(value, "shape_bounds={}", "shape_bounds={vars=16:ui64}"));
    auto dynamic = replace(value, ", 16 : ui64", "");
    dynamic =
        replace(dynamic, "shape_bounds={}", "shape_bounds={rows=32:ui64}");
    accepted(dynamic);
    refused(replace(dynamic, "shape_bounds={rows=32:ui64}",
                    "shape_bounds={vars=32:ui64}"));
    refused(replace(dynamic, "shape_bounds={rows=32:ui64}",
                    "shape_bounds={rows=32:ui64,vars=2:ui64}"));
  });
  cases.run("query types and handle message restrictions stay closed", [&] {
    auto module = parse(source(send), context);
    module->walk([&](OracleQueryOp query) {
      query.getAnswer().setType(IntegerType::get(&context, 1));
    });
    require(failed(zkc::admitStage(*module)),
            "query with a wrong answer type admitted");
    module = parse(source(send), context);
    module->walk([&](OracleSendOp oracle) {
      oracle.getDataMutable().set(oracle.getShape().front());
    });
    require(failed(zkc::admitStage(*module)),
            "send with a wrong data type admitted");
  });
  cases.run("forgetting size preserves availability and kind", [&] {
    auto body = std::string(send) + R"mlir(
 %u = "protocol.oracle_forget_shape"(%h) : (!H) -> !U
 %again = "protocol.oracle_query"(%u, %position) {owner="V", site="again"} : (!U, ui64) -> !F
)mlir";
    accepted(source(body));
    auto malformed = parse(source(body), context);
    malformed->walk([&](OracleForgetShapeOp forget) {
      forget.getOutput().setType(forget.getInput().getType());
    });
    require(failed(zkc::admitStage(*malformed)),
            "forgetting rows preserved the exact size");
    auto restricted = replace(body, " %again =", R"mlir(
 %private = "protocol.restrict_roles"(%u) {roles=["P"]} : (!U) -> !U
 %again =)mlir");
    refused(source(
        replace(restricted, "(%u, %position)", "(%private, %position)")));
    refused(source(std::string(send) + R"mlir(
 %escaped = "protocol.exchange"(%h) {sender="P", receiver="V", site="escape"} : (!H) -> !H
)mlir"));
  });
  cases.run("message-derived shape is refused even after shared delivery", [&] {
    auto body = R"mlir(
 %received = "protocol.exchange"(%rows) {sender="P", receiver="V", site="shape"} : (ui64) -> ui64
)mlir" + replace(send, "(%data, %rows)", "(%data, %received)");
    refused(source(body));
  });
  cases.run("shape recurrences inspect future backedges", [&] {
    auto loop = R"mlir(
 %last = "protocol.repeat"(%trips, %rows, %data, %position) ({
  ^bb0(%i:ui64, %n:ui64, %table:!V, %q:ui64):
   %h = "protocol.oracle_send"(%table, %n) {shape_names=["rows"],shape_bounds={},sender="P", receivers=["V"], site="layer"} : (!V,ui64) -> !H
   %answer = "protocol.oracle_query"(%h, %q) {owner="V", site="read"} : (!H,ui64) -> !F
   "protocol.yield"(%n) : (ui64) -> ()
 }) {site="round", carried=1:i64, maximum=3:i64, roles=["P","V"], carried_roles=[["P","V"]]} : (ui64,ui64,!V,ui64) -> ui64
)mlir";
    accepted(source(loop));
    auto adaptive = R"mlir(
 %adaptive = "protocol.exchange"(%trips) {sender="P", receiver="V", site="adaptive"} : (ui64) -> ui64
)mlir" + replace(loop, "(%trips, %rows, %data, %position)",
                 "(%adaptive, %rows, %data, %position)");
    refused(source(adaptive));
    refused(source(replace(loop, "\"protocol.yield\"(%n)", R"mlir(
 %received = "protocol.exchange"(%n) {sender="P", receiver="V", site="late"} : (ui64) -> ui64
 "protocol.yield"(%received))mlir")));
    refused(source(replace(loop, "roles=[\"P\",\"V\"], carried_roles",
                           "roles=[\"P\"], carried_roles")));
  });
  cases.run("CSE preserves separate anchors and repeated unused query events",
            [&] {
              auto body = std::string(send) + R"mlir(
 %unused = "protocol.oracle_send"(%data, %rows) {shape_names=["rows"],shape_bounds={},sender="P", receivers=["V"], site="another_layer"} : (!V,ui64) -> !H
 %repeated = "protocol.oracle_query"(%h, %position) {owner="V", site="repeated"} : (!H,ui64) -> !F
)mlir";
              auto module = parse(source(body), context);
              require(succeeded(zkc::admitStage(*module)), "CSE input refused");
              PassManager passes(&context);
              passes.addPass(createCSEPass());
              require(succeeded(passes.run(*module)), "CSE pass failed");
              unsigned sends = 0, queries = 0;
              module->walk([&](OracleSendOp) { ++sends; });
              module->walk([&](OracleQueryOp) { ++queries; });
              require(sends == 2 && queries == 2,
                      "CSE erased an anchor allocation or query event");
            });
  cases.run("application expansion remaps overlapping oracle rosters", [&] {
    auto module = parse(source(std::string(send) + R"mlir(
 %contents = "protocol.oracle_contents"(%h) {owner="P"} : (!H) -> !V
 %received = "protocol.exchange"(%contents) {sender="P",receiver="V",site="copy"} : (!V) -> !V
 %empty = "protocol.oracle_sequence_empty"() : () -> !S
 %next = "protocol.oracle_sequence_append"(%empty,%h) {roles=["P","V"],site="append"} : (!S,!H) -> !S
 %selected = "protocol.oracle_sequence_at"(%next,%rows) {roles=["P","V"],site="select"} : (!S,ui64) -> !H
)mlir"),
                        context);
    auto unit = cast<ProtocolModuleOp>(module->getBody()->front());
    auto leaf = *unit.getBody().front().getOps<MathematicalOp>().begin();
    auto caller = cast<MathematicalOp>(leaf->clone());
    unit.getBody().front().push_back(caller);
    caller.setSymName("caller");
    auto &block = caller.getBody().front();
    block.clear();
    OpBuilder builder(&context);
    builder.setInsertionPointToEnd(&block);
    // Swapping P and V exercises substitution even though both old names
    // remain valid members of the caller roster.
    caller.setInputRolesAttr(builder.getArrayAttr(
        {builder.getStrArrayAttr({"V"}), builder.getStrArrayAttr({"P", "V"}),
         builder.getStrArrayAttr({"P"}), builder.getStrArrayAttr({"P", "V"})}));
    caller.setOutputRolesAttr(
        builder.getArrayAttr({builder.getStrArrayAttr({"P"})}));
    auto apply = ApplyOp::create(
        builder, caller.getLoc(), caller.getFunctionType().getResults(),
        block.getArguments(), FlatSymbolRefAttr::get(&context, "example"),
        builder.getStrArrayAttr({"V", "P"}), builder.getStringAttr("invoke"));
    MathematicalReturnOp::create(builder, caller.getLoc(), apply.getOutputs());
    require(succeeded(zkc::admitStage(*module)),
            "oracle application did not admit");
    OwningOpRef<ModuleOp> original(cast<ModuleOp>(module->clone()));
    require(succeeded(zkc::mathematical::expandApplications(unit)),
            "oracle application did not expand");
    require(succeeded(zkc::admitStage(*module)),
            "oracle role substitution lost formation");
    unsigned sends = 0, queries = 0;
    caller.walk([&](OracleSendOp event) {
      ++sends;
      require(event.getSender() == "V" &&
                  event.getReceivers() == builder.getStrArrayAttr({"P"}),
              "send roles did not follow the application");
      require(event.getSite() != "layer", "send occurrence was not expanded");
    });
    caller.walk([&](OracleQueryOp event) {
      ++queries;
      require(event.getOwner() == "P",
              "query owner did not follow the application");
      require(event.getSite() != "read", "query occurrence was not expanded");
    });
    require(sends == 1 && queries == 1, "application lost oracle events");
    require(succeeded(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), unit)),
            "independent preparation check refused role substitution");
    caller.walk([&](OracleQueryOp event) { event.setOwner("V"); });
    require(failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), unit)),
            "independent preparation check ignored a changed query role");
  });
  cases.run("checked preparation preserves events and simplifies handle views",
            [&] {
              auto body = std::string(send) + R"mlir(
 %u = "protocol.oracle_forget_shape"(%h) : (!H) -> !U
 %duplicate = "protocol.oracle_forget_shape"(%h) : (!H) -> !U
 %again = "protocol.oracle_query"(%duplicate, %position) {owner="V", site="again"} : (!U,ui64) -> !F
)mlir";
              auto module = parse(source(body), context);
              auto prepared = zkc::mathematical::prepareProtocol(*module);
              require(bool(prepared), "checked oracle preparation failed");
              unsigned sends = 0, queries = 0;
              prepared->walk([&](OracleSendOp) { ++sends; });
              prepared->walk([&](OracleQueryOp) { ++queries; });
              require(sends == 1 && queries == 2,
                      "preparation erased ordered events");
            });
  cases.run("projection refuses unrealized oracle events", [&] {
    auto module = parse(source(send), context);
    PassManager passes(&context);
    passes.addPass(zkc::protocol::createProjectProtocolPass());
    require(failed(passes.run(*module)),
            "unrealized oracle reached projection");
    auto unit = cast<ProtocolModuleOp>(module->getBody()->front());
    require(unit.getProfile() == Profile::Protocol,
            "failed projection published a participant candidate");
  });
  cases.run(
      "contents require the actual holder and retained availability", [&] {
        auto body = std::string(send) + R"mlir(
 %contents = "protocol.oracle_contents"(%h) {owner="P"} : (!H) -> !V
)mlir";
        accepted(source(body));
        refused(source(replace(body, "{owner=\"P\"}", "{owner=\"V\"}")));
        refused(source(replace(body, "{owner=\"P\"}", "{owner=\"unknown\"}")));
        auto hidden = replace(body, " %contents =", R"mlir(
 %hidden = "protocol.restrict_roles"(%h) {roles=["V"]} : (!H) -> !H
 %contents =)mlir");
        refused(source(replace(hidden, R"(oracle_contents"(%h))",
                               R"(oracle_contents"(%hidden))")));
        auto malformed = parse(source(body), context);
        malformed->walk([&](OracleContentsOp contents) {
          contents.getData().setType(IntegerType::get(&context, 1));
        });
        require(failed(zkc::admitStage(*malformed)),
                "contents with the wrong data type admitted");
      });
  cases.run(
      "sequence formation preserves kinds roles and bounds failures", [&] {
        auto body = std::string(send) + R"mlir(
 %empty = "protocol.oracle_sequence_empty"() : () -> !S
 %first = "protocol.oracle_sequence_append"(%empty,%h) {roles=["P","V"],site="append"} : (!S,!H) -> !S
 %length = "protocol.oracle_sequence_length"(%first) : (!S) -> ui64
 %selected = "protocol.oracle_sequence_at"(%first,%rows) {roles=["P","V"],site="select"} : (!S,ui64) -> !H
 %contents = "protocol.oracle_contents"(%selected) {owner="P"} : (!H) -> !V
 %value = "protocol.oracle_query"(%selected,%position) {owner="V",site="selected_read"} : (!H,ui64) -> !F
)mlir";
        accepted(source(body));
        refused(source(replace(body, R"(roles=["P","V"],site="append")",
                               R"(roles=["P"],site="append")")));
        refused(source(replace(body, R"(roles=["P","V"],site="append")",
                               R"(roles=[],site="append")")));
        refused(source(replace(body, R"(roles=["P","V"],site="select")",
                               R"(roles=["P","P"],site="select")")));
        refused(source(replace(body, "(%first,%rows)", "(%first,%position)")));
        auto malformed = parse(source(body), context);
        malformed->walk([&](OracleSequenceAppendOp append) {
          append.getOutput().setType(OracleSequenceType::get(
              &context, append.getPrefix().getType().getKind(), 5));
        });
        require(failed(zkc::admitStage(*malformed)),
                "append changed the sequence bound");
        malformed = parse(source(body), context);
        malformed->walk([&](OracleSequenceAtOp at) {
          auto kind = at.getHandle().getType().getKind();
          auto unsized = OracleKindAttr::get(
              &context, kind.getIdentity(),
              ArrayAttr::get(&context, {kind.getArguments()[0]}));
          at.getHandle().setType(OracleHandleType::get(&context, unsized));
        });
        require(failed(zkc::admitStage(*malformed)),
                "selection changed the handle kind");
        // Zero capacity is meaningful. Append/selection remain stopping
        // operations even when their results are unused; CSE cannot erase these
        // checks.
        auto zero = parse(replace(source(body), "<#K, 4>", "<#K, 0>"), context);
        require(succeeded(zkc::admitStage(*zero)),
                "zero-capacity sequence lost formation");
        auto prepared = zkc::mathematical::prepareProtocol(*zero);
        require(bool(prepared), "sequence preparation failed");
        unsigned appends = 0, selections = 0;
        prepared->walk([&](OracleSequenceAppendOp) { ++appends; });
        prepared->walk([&](OracleSequenceAtOp) { ++selections; });
        require(appends == 1 && selections == 1,
                "preparation erased sequence bounds failures");
      });
  cases.run("append-only loop selection retains its dynamic anchor", [&] {
    auto body = std::string(send) + R"mlir(
 %empty = "protocol.oracle_sequence_empty"() : () -> !S
 %final = "protocol.repeat"(%trips,%empty,%h) ({
  ^bb0(%i:ui64,%layers:!S,%initial:!H):
   %next = "protocol.oracle_sequence_append"(%layers,%initial) {roles=["P","V"],site="append"} : (!S,!H) -> !S
   %selected = "protocol.oracle_sequence_at"(%next,%i) {roles=["P","V"],site="select"} : (!S,ui64) -> !H
   %contents = "protocol.oracle_contents"(%selected) {owner="P"} : (!H) -> !V
   "protocol.yield"(%next) : (!S) -> ()
 }) {site="layers",carried=1:i64,maximum=4:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!S,!H) -> !S
 %last = "protocol.oracle_sequence_at"(%final,%position) {roles=["V"],site="last"} : (!S,ui64) -> !H
 %value = "protocol.oracle_query"(%last,%position) {owner="V",site="last_read"} : (!H,ui64) -> !F
)mlir";
    accepted(source(body));
    auto module = parse(source(body), context);
    require(bool(zkc::mathematical::prepareProtocol(*module)),
            "loop-carried oracle sequence failed checked preparation");
    refused(source(replace(body, R"(owner="P"} : (!H) -> !V)",
                           R"(owner="V"} : (!H) -> !V)")));
  });
  cases.run("holder checks include later loop backedges", [&] {
    auto body = std::string(send) + R"mlir(
 %received = "protocol.exchange"(%data) {sender="P",receiver="V",site="copy"} : (!V) -> !V
 %last = "protocol.repeat"(%trips,%h,%received,%rows) ({
  ^bb0(%i:ui64,%current:!H,%d:!V,%n:ui64):
   %contents = "protocol.oracle_contents"(%current) {owner="P"} : (!H) -> !V
   %next = "protocol.oracle_send"(%d,%n) {shape_names=["rows"],shape_bounds={},sender="V",receivers=["P"],site="later"} : (!V,ui64) -> !H
   "protocol.yield"(%next) : (!H) -> ()
 }) {site="switch",carried=1:i64,maximum=2:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!V,ui64) -> !H
)mlir";
    refused(source(body));
    // If the carried value never changes holder, the unused later anchor does
    // not contaminate it. This also checks the zero-trip incoming edge.
    accepted(source(replace(body, R"(protocol.yield"(%next))",
                            R"(protocol.yield"(%current))")));
    auto malformed = parse(source(body), context);
    malformed->walk([&](OracleSendOp event) {
      if (event.getSite() == "later")
        event->removeAttr("sender");
    });
    require(failed(zkc::admitStage(*malformed)),
            "malformed backedge producer admitted");
  });
  cases.run(
      "preparation compares actual dynamic anchors and sequence positions",
      [&] {
        auto body = std::string(send) + R"mlir(
 %other = "protocol.oracle_send"(%data,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="other"} : (!V,ui64) -> !H
 %empty = "protocol.oracle_sequence_empty"() : () -> !S
 %first = "protocol.oracle_sequence_append"(%empty,%h) {roles=["P","V"],site="append"} : (!S,!H) -> !S
 %selected = "protocol.oracle_sequence_at"(%first,%rows) {roles=["P","V"],site="select"} : (!S,ui64) -> !H
)mlir";
        auto original = parse(source(body), context);
        auto candidate = zkc::mathematical::prepareProtocol(*original);
        require(bool(candidate),
                "anchor comparison control failed preparation");
        Value other;
        candidate->walk([&](OracleSendOp event) {
          if (event.getSite() == "other")
            other = event.getHandle();
        });
        candidate->walk([&](OracleSequenceAppendOp append) {
          append.getElementMutable().set(other);
        });
        require(succeeded(zkc::admitStage(*candidate)),
                "anchor mutation lost formation");
        require(
            failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), &candidate->getBody()->front())),
            "same-kind same-data anchor substitution passed correspondence");
        candidate = zkc::mathematical::prepareProtocol(*original);
        candidate->walk([&](OracleSequenceAtOp at) {
          at.getPositionMutable().set(at->getParentOfType<MathematicalOp>()
                                          .getBody()
                                          .front()
                                          .getArgument(3));
        });
        require(succeeded(zkc::admitStage(*candidate)),
                "position mutation lost formation");
        require(
            failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), &candidate->getBody()->front())),
            "dynamic position substitution passed correspondence");
      });
  return cases.result();
}
