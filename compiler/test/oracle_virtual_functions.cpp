#include "../lib/Transforms/OracleVirtualFunctions.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Registry.h"
#include <filesystem>
#include <fstream>
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::protocol;
using namespace zkc::protocol_ir;
using namespace zkc::test;
namespace {
std::string source() {
  return R"mlir(
#K = #protocol.oracle_kind<"table", [i1, 16 : ui64]>
!H = !protocol.oracle<#K>
!D = !data.sequence<i1>
module { "protocol.module"() ({
 relation.declare @admissible {kind="external",key="test/functions",revision="0",
   signature=(!D,!D,ui64,i1)->i1,purposes=["witness","witness","parameter","parameter"]}
 func.func private @map(%unused:i1,%position:ui64)->ui64 {
   return %position : ui64
 }
 func.func private @choose(%left:i1,%right:i1,%choose:i1)->i1 {
   %answer = arith.select %choose, %left, %right : i1
   return %answer : i1
 }
 "protocol.oracle"() ({
  ^bb0(%a:!H,%b:!H,%parameter:ui64,%choose:i1,%position:ui64):
   %left = "protocol.oracle_query"(%a,%position) {site="left"} : (!H,ui64)->i1
   %mapped = func.call @map(%left,%parameter) : (i1,ui64)->ui64
   %right = "protocol.oracle_query"(%b,%mapped) {site="right"} : (!H,ui64)->i1
   %answer = func.call @choose(%left,%right,%choose) : (i1,i1,i1)->i1
   "protocol.oracle_yield"(%answer) : (i1)->()
 }) {sym_name="select",function_type=(!H,!H,ui64,i1,ui64)->i1,kind=#K,
     shape_arguments={},shape_bounds={},admissibility=@admissible} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";
}
std::string mutateText(std::string text, StringRef from, StringRef to) {
  auto at = text.find(from.str());
  require(at != std::string::npos, "fixture replacement missing");
  text.replace(at, from.size(), to.str());
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
  require(succeeded(verify(*result)), "formation: " + diagnostics);
  return result;
}
ProtocolModuleOp unit(ModuleOp module) {
  return cast<ProtocolModuleOp>(module.getBody()->front());
}
OracleDefinitionOp definition(ModuleOp module) {
  return *unit(module).getBody().front().getOps<OracleDefinitionOp>().begin();
}
OwningOpRef<ModuleOp> fresh(MLIRContext &context) {
  return parse(context, R"mlir(
module { "protocol.module"() ({
 func.func private @placeholder()->i1 { %ok = arith.constant true
 return %ok : i1 }
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
}
std::string print(Operation *op) {
  std::string text;
  raw_string_ostream stream(text);
  op->print(stream);
  return text;
}
void checked(ModuleOp candidate, OracleDefinitionOp original,
             const OracleVirtualFunctions &functions) {
  if (auto error = checkOracleVirtualFunctions(candidate, original, functions))
    throw std::runtime_error(toString(std::move(error)));
}
void refused(ModuleOp candidate, OracleDefinitionOp original,
             const OracleVirtualFunctions &functions) {
  require(succeeded(verify(candidate)), "mutation failed ordinary formation");
  auto error = checkOracleVirtualFunctions(candidate, original, functions);
  require(bool(error), "changed function record was admitted");
  require(namesIdentifier(toString(std::move(error)),
                          "oracle-virtual-function-body"),
          "wrong function refusal");
}
std::string client(ModuleOp candidate, const OracleVirtualFunctions &functions,
                   const DialectRegistry &registry) {
  OpBuilder builder(candidate.getContext());
  auto loc = candidate.getLoc();
  auto answer = functions.answer;
  auto signature = answer.getFunctionType();
  SmallVector<Type> outputs;
  for (auto query : functions.queries)
    outputs.push_back(query.position.getResultTypes()[0]);
  outputs.push_back(signature.getResult(0));
  auto role = builder.getArrayAttr({builder.getStringAttr("V")});
  OperationState state(loc, "protocol.func");
  state.addAttribute("sym_name", builder.getStringAttr("main"));
  state.addAttribute("function_type", TypeAttr::get(builder.getFunctionType(
                                          signature.getInputs(), outputs)));
  state.addAttribute("roles", role);
  state.addAttribute("input_roles", builder.getArrayAttr(SmallVector<Attribute>(
                                        signature.getNumInputs(), role)));
  state.addAttribute(
      "output_roles",
      builder.getArrayAttr(SmallVector<Attribute>(outputs.size(), role)));
  auto *body = new Block();
  body->addArguments(signature.getInputs(),
                     SmallVector<Location>(signature.getNumInputs(), loc));
  state.addRegion()->push_back(body);
  builder.setInsertionPointToEnd(&unit(candidate).getBody().front());
  builder.create(state);
  builder.setInsertionPointToEnd(body);
  SmallVector<Value> results;
  for (const auto &query : functions.queries)
    results.push_back(func::CallOp::create(builder, loc, query.position,
                                           body->getArguments().take_front(3))
                          .getResult(0));
  results.push_back(
      func::CallOp::create(builder, loc, functions.answer, body->getArguments())
          .getResult(0));
  MathematicalReturnOp::create(builder, loc, results);
  require(succeeded(verify(candidate)), "ordinary function client refused");
  return take(compileRun(print(candidate), "oracle-virtual-functions.mlir", {},
                         registry))
      .bundle;
}
} // namespace
int main(int argc, char **argv) {
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  ScopedDiagnosticHandler silence(&context,
                                  [](Diagnostic &) { return success(); });
  Cases cases;
  cases.run("actual helper returns split positions and ordered answers", [&] {
    auto original = parse(context, source());
    auto before = print(*original);
    auto candidate = fresh(context);
    OracleVirtualFunctionWork work;
    auto functions = take(
        emitOracleVirtualFunctions(*candidate, definition(*original), work));
    checked(*candidate, definition(*original), functions);
    require(print(*original) == before, "source was mutated");
    require(functions.queries.size() == 2 &&
                functions.answer.getNumArguments() == 5,
            "query inventory or answer interface lost");
    require(functions.queries[0].source == 0 &&
                functions.queries[1].source == 1,
            "sources changed");
    require(work.operations < 100000 && work.slots < 1000000,
            "work was not charged");
    for (auto &query : functions.queries)
      require(query.position.front().getOperations().size() == 1,
              "position retained an ignored answer argument");
    auto bundle = client(*candidate, functions, registry);
    require(!bundle.empty(), "ordinary virtual functions did not compile");
    if (argc == 2) {
      std::filesystem::create_directories(argv[1]);
      std::ofstream output(std::filesystem::path(argv[1]) /
                           "virtual-functions.bundle");
      output << bundle;
      require(bool(output), "could not write ordinary function client");
    }
  });
  cases.run(
      "duplicate queries and unused answers remain distinct occurrences", [&] {
        auto text = mutateText(source(), "(%b,%mapped)", "(%a,%position)");
        text = mutateText(text, "oracle_yield\"(%answer)",
                          "oracle_yield\"(%left)");
        auto original = parse(context, text);
        auto candidate = fresh(context);
        OracleVirtualFunctionWork work;
        auto functions = take(emitOracleVirtualFunctions(
            *candidate, definition(*original), work));
        checked(*candidate, definition(*original), functions);
        require(functions.queries.size() == 2 &&
                    functions.queries[1].source == 0 &&
                    functions.queries[0].site != functions.queries[1].site &&
                    functions.answer.getNumArguments() == 5,
                "dead or duplicate query was eliminated");
        functions.queries.pop_back();
        refused(*candidate, definition(*original), functions);
      });
  cases.run("a virtual function can ignore all sources and make no queries",
            [&] {
              auto text = source();
              auto start = text.find("   %left =");
              auto end = text.find("   \"protocol.oracle_yield\"");
              text.erase(start, end - start);
              text = mutateText(text, "oracle_yield\"(%answer)",
                                "oracle_yield\"(%choose)");
              auto original = parse(context, text);
              auto candidate = fresh(context);
              OracleVirtualFunctionWork work;
              auto functions = take(emitOracleVirtualFunctions(
                  *candidate, definition(*original), work));
              checked(*candidate, definition(*original), functions);
              require(functions.queries.empty() &&
                          functions.answer.getNumArguments() == 3,
                      "invented a query or placeholder answer");
            });
  for (unsigned mutation = 0; mutation < 8; ++mutation)
    cases.run(
        "well-formed virtual function substitution " + Twine(mutation), [&] {
          auto original = parse(context, source());
          auto candidate = fresh(context);
          OracleVirtualFunctionWork work;
          auto functions = take(emitOracleVirtualFunctions(
              *candidate, definition(*original), work));
          switch (mutation) {
          case 0:
            std::swap(functions.queries[0], functions.queries[1]);
            break;
          case 1:
            functions.queries[1].source = 0;
            break;
          case 2:
            functions.queries[1].site = "different";
            break;
          case 3:
            functions.queries.pop_back();
            break;
          case 4:
            functions.queries[1].kind = OracleKindAttr::get(
                &context, "table",
                ArrayAttr::get(&context,
                               {TypeAttr::get(IntegerType::get(
                                   &context, 64, IntegerType::Unsigned))}));
            break;
          case 5:
            functions.queries[0].position.front().back().setOperand(
                0, functions.queries[0].position.getArgument(0));
            break;
          case 6:
            functions.answer.front().back().setOperand(
                0, functions.answer.getArgument(1));
            break;
          case 7: {
            functions.answer.walk([&](Operation *op) {
              if (op->getName().getStringRef() == "arith.select") {
                auto first = op->getOperand(1);
                op->setOperand(1, op->getOperand(2));
                op->setOperand(2, first);
              }
            });
            break;
          }
          }
          refused(*candidate, definition(*original), functions);
        });
  cases.run("candidate calls are checked through their actual helper bodies",
            [&] {
              auto original = parse(context, source());
              auto candidate = fresh(context);
              OracleVirtualFunctionWork work;
              auto functions = take(emitOracleVirtualFunctions(
                  *candidate, definition(*original), work));
              OpBuilder builder(&context);
              auto position = functions.queries[1].position;
              auto helper = cast<func::FuncOp>(position->clone());
              helper.setSymName("replacement");
              unit(*candidate).getBody().front().push_back(helper);
              builder.setInsertionPoint(&position.front().back());
              auto call = func::CallOp::create(builder, position.getLoc(),
                                               helper, position.getArguments());
              position.front().back().setOperand(0, call.getResult(0));
              checked(*candidate, definition(*original), functions);
              helper.front().back().setOperand(0, helper.getArgument(2));
              refused(*candidate, definition(*original), functions);
            });
  for (bool slots : {false, true})
    cases.run(slots ? "bounded slot work" : "bounded operation work", [&] {
      auto original = parse(context, source());
      auto before = print(*original);
      auto candidate = fresh(context);
      OracleVirtualFunctionWork work;
      if (slots)
        work.slots = 0;
      else
        work.operations = 0;
      refuses(
          emitOracleVirtualFunctions(*candidate, definition(*original), work),
          "oracle-virtual-function-limit");
      require(before == print(*original), "refusal mutated the source");
    });
  return cases.result();
}
