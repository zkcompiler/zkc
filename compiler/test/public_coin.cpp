#include "mlir/Parser/Parser.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Registry.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace zkc;
namespace {
constexpr StringLiteral fixture = R"(module { "protocol.module"() ({
"protocol.func"() ({^bb0(%s:!protocol.service_ref<"random.bls12-381.fr/1">):
%q="protocol.query"(%s) {owner="V",method="draw",site="draw"} : (!protocol.service_ref<"random.bls12-381.fr/1">)->!algebra.field<"bls12-381.fr">
%d=protocol.exchange %q {sender="V",receiver="P",site="coin"} : !algebra.field<"bls12-381.fr">
%yes=arith.constant true
"protocol.return"(%yes) : (i1)->()})
{sym_name="main",function_type=(!protocol.service_ref<"random.bls12-381.fr/1">)->i1,roles=["P","V"],input_roles=[["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
constexpr StringLiteral requirement =
    R"({"format":"zkc.public-coin-requirement/1","entry":"main","prover":"P","verifier":"V","service":0,"decision":0,"bound_inputs":[],"draws":[{"query_site":"draw","delivery_site":"coin"}]})";
void require(bool ok, StringRef message) {
  if (!ok) {
    errs() << message << '\n';
    std::exit(1);
  }
}
std::string print(mlir::ModuleOp module) {
  std::string text;
  raw_string_ostream stream(text);
  module.print(stream);
  return text;
}
json::Value analyze() {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(fixture, &context);
  require(bool(module), "fixture parse");
  auto before = print(*module);
  std::string independent = requirement.str();
  auto report = analyzePublicCoin(*module, independent);
  require(bool(report), "analysis");
  require(print(*module) == before, "analysis changed source");
  std::string text;
  raw_string_ostream(text) << *report;
  auto checked = checkPublicCoin(*module, independent, text);
  require(!checked, "report check");
  auto bad = checkPublicCoin(*module, independent, "{}");
  require(bool(bad), "bad report accepted");
  consumeError(std::move(bad));
  require(print(*module) == before, "failed check changed source");
  // The caller serializes only after source, prepared copy, requirement and
  // context have died. Dynamic site strings must be owned, not StringRefs.
  return std::move(*report);
}
} // namespace
int main() {
  auto report = analyze();
  std::string printed;
  raw_string_ostream(printed) << report;
  auto decoded = json::parse(printed);
  require(bool(decoded) && *decoded == report, "report ownership");
  auto *draw = (*report.getAsObject()->getArray("draws"))[0].getAsObject();
  require(draw->getString("site") == "draw" &&
              draw->getObject("delivery")->getString("site") == "coin",
          "owned sites");
  mlir::DialectRegistry registry;
  RunOptions options;
  options.publicCoinRequirement = requirement.str();
  auto result = compileRun(fixture, "public-coin.mlir", options, registry);
  require(bool(result) && result->publicCoin && !result->correspondence,
          "checked invocation");
  auto compiled = json::parse(*result->publicCoin);
  require(bool(compiled) && *compiled->getAsObject()->get("view") == report,
          "same unsimplified view");
  options.entry = "absent";
  auto refused = compileRun(fixture, "public-coin.mlir", options, registry);
  require(!refused, "entry mismatch accepted");
  consumeError(refused.takeError());
  outs() << "public-coin source immutability, report ownership and checked API "
            "passed\n";
}
