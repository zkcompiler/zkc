#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Mathematical.h"
using namespace mlir;
using namespace zkc::test;
using namespace zkc::protocol_ir;
namespace {
std::string source() {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear">, 16 : ui64]>
!F = !algebra.field<"koala-bear">
!D = !data.field_vector<"koala-bear">
!H = !protocol.oracle<#K>
module {
 "protocol.module"() ({
  relation.declare @admissible {kind="external",key="test/virtual",revision="0",
    signature=(!D,!D,ui64)->i1,purposes=["witness","witness","parameter"]}
  "protocol.oracle"() ({
   ^bb0(%first:!H,%second:!H,%parameter:ui64,%position:ui64):
    %left = "protocol.oracle_query"(%first,%position) {site="left"} : (!H,ui64)->!F
    %right = "protocol.oracle_query"(%second,%position) {site="right"} : (!H,ui64)->!F
    "protocol.oracle_yield"(%left) : (!F)->()
  }) {sym_name="select",function_type=(!H,!H,ui64,ui64)->!F,kind=#K,shape_arguments={},shape_bounds={},
      admissibility=@admissible} : ()->()
  "protocol.func"() ({
   ^bb0(%a:!D,%b:!D,%rows:ui64,%position:ui64,%parameter:ui64):
    %first = "protocol.oracle_send"(%a,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="first"} : (!D,ui64)->!H
    %second = "protocol.oracle_send"(%b,%rows) {shape_names=["rows"],shape_bounds={},sender="P",receivers=["V"],site="second"} : (!D,ui64)->!H
    %virtual = "protocol.oracle_virtual"(%first,%second,%parameter) {callee=@select,holder="P",receivers=["V"]} : (!H,!H,ui64)->!H
    %contents = "protocol.oracle_contents"(%virtual) {owner="P"} : (!H)->!D
    %value = "protocol.oracle_query"(%virtual,%position) {owner="V",site="read"} : (!H,ui64)->!F
    %ok = arith.constant true
    "protocol.return"(%ok) : (i1)->()
  }) {sym_name="example",function_type=(!D,!D,ui64,ui64,ui64)->i1,
      roles=["P","V"],input_roles=[["P"],["P"],["P","V"],["V"],["P","V"]],
      output_roles=[["V"]]} : ()->()
 }) {profile=#protocol.profile<protocol>} : ()->()
})mlir";
}
std::string replace(std::string text, llvm::StringRef before,
                    llvm::StringRef after) {
  auto position = text.find(before.str());
  require(position != std::string::npos, "missing mutation target");
  text.replace(position, before.size(), after.str());
  return text;
}
std::string indices() {
  auto text = source();
  for (llvm::StringRef from : {"!algebra.field<\"koala-bear\">"}) {
    size_t position;
    while ((position = text.find(from.str())) != std::string::npos)
      text.replace(position, from.size(), "ui64");
  }
  return replace(text, "!data.field_vector<\"koala-bear\">", "!data.indices");
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
  require(bool(module), "virtual fixture did not parse: " + message);
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
    std::string message;
    ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diagnostic) {
      llvm::raw_string_ostream out(message);
      diagnostic.print(out);
      return success();
    });
    require(succeeded(zkc::admitStage(*module)),
            "valid virtual oracle refused: " + message);
  };
  auto refused = [&](llvm::StringRef text) {
    auto module = parse(text, context);
    require(succeeded(verify(*module)),
            "semantic virtual oracle mutation lost structural validity");
    require(failed(zkc::admitStage(*module)),
            "invalid virtual oracle admitted");
  };
  auto structurallyRefused = [&](llvm::StringRef text) {
    auto module = parse(text, context);
    require(failed(verify(*module)),
            "invalid virtual oracle structure admitted");
  };
  cases.run(
      "virtual anchors may retain earlier iterations without cyclic values",
      [&] {
        auto text = replace(
            source(),
            "%virtual = \"protocol.oracle_virtual\"(%first,%second,%parameter) "
            "{callee=@select,holder=\"P\",receivers=[\"V\"]} : "
            "(!H,!H,ui64)->!H",
            R"mlir(
    %trips = "data.index"() {value=3 : ui64} : ()->ui64
    %virtual = "protocol.repeat"(%trips,%first,%second,%parameter) ({
      ^bb0(%iteration:ui64,%previous:!H,%other:!H,%argument:ui64):
       %next = "protocol.oracle_virtual"(%previous,%other,%argument) {callee=@select,holder="P",receivers=["V"]} : (!H,!H,ui64)->!H
       "protocol.yield"(%next) : (!H)->()
    }) {site="chain",carried=1:i64,maximum=3:i64,roles=["P","V"],carried_roles=[["P","V"]]} : (ui64,!H,!H,ui64)->!H
)mlir");
        accepted(text);
        auto module = parse(text, context);
        auto prepared = zkc::mathematical::prepareProtocol(*module, false);
        require(bool(prepared),
                "virtual recurrence was lost during preparation");
        unsigned definitions = 0, constructions = 0;
        prepared->walk([&](OracleDefinitionOp) { ++definitions; });
        prepared->walk([&](OracleVirtualOp) { ++constructions; });
        require(definitions == 1 && constructions == 1,
                "preparation unrolled dynamic anchors into static guesses");
      });
  cases.run(
      "virtual sources parameters holder and predicate stay explicit", [&] {
        accepted(source());
        accepted(indices());
        refused(replace(source(), "holder=\"P\",receivers=[\"V\"]",
                        "holder=\"V\",receivers=[\"P\"]"));
        refused(replace(source(), "holder=\"P\",receivers=[\"V\"]",
                        "holder=\"P\",receivers=[\"P\"]"));
        refused(
            replace(source(), "[\"V\"],[\"P\",\"V\"]]", "[\"V\"],[\"V\"]]"));
        structurallyRefused(replace(source(), "admissibility=@admissible",
                                    "admissibility=@missing"));
        structurallyRefused(
            replace(source(), "callee=@select", "callee=@admissible"));
        structurallyRefused(replace(source(), "signature=(!D,!D,ui64)->i1",
                                    "signature=(!D,!D,!F)->i1"));
        structurallyRefused(replace(source(), "{site=\"left\"}",
                                    "{site=\"left\",owner=\"V\"}"));
        refused(replace(source(), "site=\"right\"", "site=\"left\""));
        structurallyRefused(replace(source(), "{owner=\"V\",site=\"read\"}",
                                    "{site=\"read\"}"));
      });
  cases.run(
      "query maps cannot depend on answers including through helpers", [&] {
        refused(replace(indices(), "(%second,%position)", "(%second,%left)"));
        auto indirect = replace(indices(), " %right =", R"mlir(
    %mapped = func.call @map(%left,%position) : (ui64,ui64)->ui64
    %right =)mlir");
        indirect =
            replace(indirect, "(%second,%position)", "(%second,%mapped)");
        auto withHelper = [&](llvm::StringRef returned) {
          return replace(indirect, "  relation.declare", R"mlir(
  func.func private @map(%answer:ui64,%query:ui64)->ui64 {
    return )mlir" + returned.str() + R"mlir( : ui64
  }
  relation.declare)mlir");
        };
        refused(withHelper("%answer"));
        accepted(withHelper("%query"));
        auto module = parse(indices(), context);
        auto unit = cast<ProtocolModuleOp>(module->getBody()->front());
        auto definition =
            *unit.getBody().front().getOps<OracleDefinitionOp>().begin();
        auto unused = cast<OracleDefinitionOp>(definition->clone());
        unused.setSymName("unused");
        unit.getBody().front().push_back(unused);
        auto queries = unused.getBody().front().getOps<OracleQueryOp>();
        auto first = *queries.begin();
        for (auto query : queries)
          if (query != first)
            query.getPositionMutable().set(first.getAnswer());
        require(failed(zkc::admitStage(*module)),
                "unused invalid query declaration was ignored");
      });
  cases.run("query bodies admit total mathematics and refuse effects", [&] {
    auto math =
        replace(source(), "    \"protocol.oracle_yield\"(%left)", R"mlir(
    %sum = "algebra.field_add"(%left,%right) : (!F,!F)->!F
    "protocol.oracle_yield"(%sum))mlir");
    accepted(math);
    auto effect =
        replace(source(), "    \"protocol.oracle_yield\"(%left)", R"mlir(
    %ok = arith.constant true
    "protocol.guard"(%ok) {owner="V",site="stop"} : (i1)->()
    "protocol.oracle_yield"(%left))mlir");
    // Protocol guards require a program parent even before stage admission.
    structurallyRefused(effect);
    refused(replace(source(), "kind=#K,", "kind=#K,unproved=true,"));
  });
  cases.run(
      "dynamic virtual shapes identify an initially bound parameter", [&] {
        auto dynamic = replace(source(), ", 16 : ui64", "");
        dynamic = replace(dynamic, "shape_arguments={}",
                          "shape_arguments={rows=2:ui64}");
        for (unsigned i = 0; i < 3; ++i)
          dynamic = replace(dynamic, "shape_bounds={}",
                            "shape_bounds={rows=32:ui64}");
        accepted(dynamic);
        structurallyRefused(replace(dynamic, "shape_arguments={rows=2:ui64}",
                                    "shape_arguments={rows=0:ui64}"));
        structurallyRefused(replace(dynamic, "shape_arguments={rows=2:ui64}",
                                    "shape_arguments={rows=3:ui64}"));
        structurallyRefused(
            replace(dynamic, "shape_bounds={rows=32:ui64},", ""));
        structurallyRefused(replace(source(), "shape_arguments={}",
                                    "shape_arguments={rows=2:ui64}"));
      });
  cases.run(
      "preparation keeps actual query definitions and fresh virtual anchors",
      [&] {
        auto text = replace(source(), "    %contents =", R"mlir(
    %another = "protocol.oracle_virtual"(%first,%second,%parameter) {callee=@select,holder="P",receivers=["V"]} : (!H,!H,ui64)->!H
    %contents =)mlir");
        auto original = parse(text, context);
        auto prepared = zkc::mathematical::prepareProtocol(*original);
        require(bool(prepared), "virtual preparation failed");
        unsigned anchors = 0, queries = 0;
        prepared->walk([&](OracleVirtualOp) { ++anchors; });
        prepared->walk([&](OracleQueryOp) { ++queries; });
        require(anchors == 2 && queries == 3,
                "preparation erased a fresh anchor or query");
        prepared->walk([&](OracleDefinitionOp definition) {
          auto &body = definition.getBody().front();
          auto yield = cast<OracleYieldOp>(body.back());
          for (auto query : body.getOps<OracleQueryOp>())
            if (query.getSite() == "right")
              yield.getAnswerMutable().set(query.getAnswer());
        });
        require(succeeded(verify(*prepared)), "body mutation lost formation");
        require(
            failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                &original->getBody()->front(), &prepared->getBody()->front())),
            "same-name virtual body substitution passed correspondence");
      });
  cases.run(
      "virtual correspondence binds helper and predicate definitions", [&] {
        auto text = replace(source(), "  relation.declare", R"mlir(
    func.func private @choose(%a:!F,%b:!F)->!F { return %a : !F }
    relation.declare)mlir");
        text = replace(text, "    \"protocol.oracle_yield\"(%left)", R"mlir(
    %chosen = func.call @choose(%left,%right) : (!F,!F)->!F
    "protocol.oracle_yield"(%chosen))mlir");
        auto original = parse(text, context);
        for (bool helper : {false, true}) {
          auto prepared = zkc::mathematical::prepareProtocol(*original);
          require(bool(prepared), "virtual closure preparation failed");
          auto unit = cast<ProtocolModuleOp>(prepared->getBody()->front());
          if (helper) {
            auto function =
                cast<func::FuncOp>(SymbolTable::lookupSymbolIn(unit, "choose"));
            function.front().back().setOperand(0, function.getArgument(1));
          } else {
            auto *predicate = SymbolTable::lookupSymbolIn(unit, "admissible");
            predicate->setAttr("key",
                               StringAttr::get(&context, "test/different"));
          }
          require(succeeded(verify(*prepared)),
                  "closure mutation lost formation");
          require(
              failed(zkc::mathematical::verifyProtocolPreparationPreserved(
                  &original->getBody()->front(), unit)),
              "same-name virtual closure substitution passed correspondence");
        }
      });
  cases.run(
      "virtual helper observations check actual degree bounds before DCE", [&] {
        auto text = replace(source(), "module {", R"mlir(
!A = !data.field_array<"koala-bear", 2>
!Polynomial = !poly.polynomial<"koala-bear", 1>
module {)mlir");
        size_t position;
        while ((position = text.find("%parameter:ui64")) != std::string::npos)
          text.replace(position, std::string("%parameter:ui64").size(),
                       "%parameter:!A");
        for (auto [before, after] :
             {std::pair{"signature=(!D,!D,ui64)", "signature=(!D,!D,!A)"},
              {"function_type=(!H,!H,ui64,ui64)",
               "function_type=(!H,!H,!A,ui64)"},
              {"function_type=(!D,!D,ui64,ui64,ui64)",
               "function_type=(!D,!D,ui64,ui64,!A)"},
              {": (!H,!H,ui64)->!H", ": (!H,!H,!A)->!H"}})
          text = replace(text, before, after);
        text = replace(text, "  relation.declare", R"mlir(
  func.func private @observe(%p:!Polynomial)->!A {
    %coefficients = "poly.coefficients"(%p) : (!Polynomial)->!A
    return %coefficients : !A
  }
  relation.declare)mlir");
        text = replace(text, "    \"protocol.oracle_yield\"(%left)", R"mlir(
    %p = "poly.from_coefficients"(%parameter) : (!A)->!Polynomial
    %square = "poly.multiply"(%p,%p) : (!Polynomial,!Polynomial)->!Polynomial
    %unused = func.call @observe(%p) : (!Polynomial)->!A
    "protocol.oracle_yield"(%left))mlir");
        accepted(text);
        refused(replace(text, "@observe(%p)", "@observe(%square)"));
      });
  return cases.result();
}
