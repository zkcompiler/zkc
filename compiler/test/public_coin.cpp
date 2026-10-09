#include "../lib/Transforms/PreparedProtocol.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Compiler/PublicCoin.h"
#include "zkc/Compiler/Run.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/Passes.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace zkc;
namespace {
constexpr StringLiteral fixture = R"(module { "protocol.module"() ({
"protocol.func"() ({^bb0(%s:!protocol.service_ref<"random.bls12-381.fr/0">):
%q="protocol.query"(%s) {owner="V",method="draw",site="draw"} : (!protocol.service_ref<"random.bls12-381.fr/0">)->!algebra.field<"bls12-381.fr">
%d=protocol.exchange %q {sender="V",receiver="P",site="coin"} : !algebra.field<"bls12-381.fr">
%yes=arith.constant true
"protocol.return"(%yes) : (i1)->()})
{sym_name="main",function_type=(!protocol.service_ref<"random.bls12-381.fr/0">)->i1,roles=["P","V"],input_roles=[["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })";
constexpr StringLiteral requirement =
    R"({"format":"zkc.public-coin-requirement/0","entry":"main","prover":"P","verifier":"V","service":0,"decision":0,"bound_inputs":[],"draws":[{"query_site":"draw","delivery_site":"coin"}]})";
constexpr StringLiteral helperPrograms = R"mlir(module { "protocol.module"() ({
  func.func private @conjoin(%x: i1, %y: i1) -> i1 {
    %both = arith.andi %x, %y : i1
    return %both : i1
  }
  func.func private @checked(%x: i1) -> i1 {
    %yes = arith.constant true
    %result = func.call @conjoin(%x, %yes) : (i1, i1) -> i1
    return %result : i1
  }
  "protocol.func"() ({
  ^entry(%x: i1):
    %first = func.call @checked(%x) : (i1) -> i1
    %second = func.call @checked(%x) : (i1) -> i1
    %sent = protocol.exchange %first {sender="P", receiver="V", site="message"} : i1
    %accepted = func.call @conjoin(%sent, %sent) : (i1, i1) -> i1
    "protocol.return"(%second, %accepted) : (i1, i1) -> ()
  }) {sym_name="main", function_type=(i1)->(i1, i1), roles=["P","V"], input_roles=[["P"]], output_roles=[["P"],["V"]]} : ()->()
  "protocol.func"() ({
    %yes = arith.constant true
    %accepted = func.call @checked(%yes) : (i1) -> i1
    "protocol.return"(%accepted) : (i1)->()
  }) {sym_name="other", function_type=()->i1, roles=["V"], input_roles=[], output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
constexpr StringLiteral polynomialPrograms = R"mlir(
!field = !algebra.field<"bls12-381.fr">
!polynomial = !poly.polynomial<"bls12-381.fr", 1>
module { "protocol.module"() ({
  func.func private @square(%values: tensor<2x!field>) -> !polynomial {
    %linear = "poly.mle"(%values) : (tensor<2x!field>)->!polynomial
    %square = "poly.multiply"(%linear, %linear) : (!polynomial, !polynomial)->!polynomial
    return %square : !polynomial
  }
  "protocol.func"() ({
    %yes = arith.constant true
    %both = arith.andi %yes, %yes : i1
    "protocol.return"(%both) : (i1)->()
  }) {sym_name="main", function_type=()->i1, roles=["V"], input_roles=[], output_roles=[["V"]]} : ()->()
  "protocol.func"() ({
  ^entry(%values: tensor<2x!field>):
    %square = func.call @square(%values) : (tensor<2x!field>)->!polynomial
    %unused = "poly.coefficients"(%square) : (!polynomial)->tensor<3x!field>
    "protocol.return"(%values) : (tensor<2x!field>)->()
  }) {sym_name="observation", function_type=(tensor<2x!field>)->tensor<2x!field>, roles=["P"], input_roles=[["P"]], output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
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

unsigned programOperationCount(mlir::ModuleOp module, StringRef name) {
  unsigned count = 0;
  module.walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() == name &&
        (op->getParentOfType<protocol_ir::MathematicalOp>() ||
         op->getParentOfType<protocol_ir::ParticipantOp>()))
      ++count;
  });
  return count;
}

void compareProjection(mlir::MLIRContext &context, StringRef source,
                       unsigned programs, unsigned calls, bool simplify) {
  auto original = mlir::parseSourceString<mlir::ModuleOp>(source, &context);
  test::require(bool(original), "source parse");
  auto unit =
      mlir::cast<protocol_ir::ProtocolModuleOp>(original->getBody()->front());
  test::require(
      llvm::range_size(
          unit.getBody().front().getOps<protocol_ir::MathematicalOp>()) ==
              programs &&
          programOperationCount(*original, "func.call") == calls,
      "source program/helper coverage");
  auto sourceText = print(*original);
  auto handle = mathematical::PreparedProtocol::prepare(*original);
  test::require(bool(handle), "preparation failed");
  test::require(print(*original) == sourceText, "preparation changed source");
  auto snapshot = handle->snapshot();
  test::require(bool(snapshot), "missing prepared snapshot");
  auto frozen = print(*snapshot);
  test::require(programOperationCount(*snapshot, "func.call") == 0,
                "preparation left helper calls in programs");
  test::require(programOperationCount(*snapshot, "arith.andi") > 0,
                "snapshot was simplified");
  // Changing either caller-owned module cannot alter the prepared authority,
  // even though MLIR operation views mutate.
  original->getBody()->clear();
  auto independent = handle->snapshot();
  test::require(bool(independent), "missing independent snapshot");
  independent->getBody()->clear();
  auto projected = std::move(*handle).project(simplify);
  test::require(bool(projected), "projection failed");
  test::require(print(*snapshot) == frozen, "projection changed snapshot");
  test::require((programOperationCount(*projected, "arith.andi") > 0) !=
                    simplify,
                "wrong projection simplification timing");
  test::require(!handle->snapshot() && !std::move(*handle).project(simplify),
                "consumed authority was reused");
  auto standalone = mlir::parseSourceString<mlir::ModuleOp>(source, &context);
  test::require(bool(standalone), "standalone source parse");
  mlir::PassManager pipeline(&context);
  pipeline.addPass(protocol::createProjectProtocolPass(simplify));
  test::require(succeeded(pipeline.run(*standalone)),
                "standalone projection failed");
  test::require(print(*standalone) == print(*projected),
                "standalone/prepared projection disagreement");
  // Compare explicit preparation and projection with the prepared handle.
  // Equality here is bounded fixture evidence, not general pass equivalence.
  auto staged = mlir::parseSourceString<mlir::ModuleOp>(source, &context);
  test::require(bool(staged), "staged source parse");
  pipeline.clear();
  pipeline.addPass(protocol::createPrepareProtocolPass(false));
  test::require(succeeded(pipeline.run(*staged)), "staged preparation failed");
  test::require(print(*staged) == frozen, "staged preparation disagreement");
  pipeline.clear();
  pipeline.addPass(protocol::createProjectProtocolPass(simplify));
  test::require(succeeded(pipeline.run(*staged)), "staged projection failed");
  test::require(print(*staged) == print(*projected),
                "staged/prepared projection disagreement");
}

int preparationCases() {
  zkc::test::Cases cases;
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // The conjunction is used by the verifier result, but folds to true. It
  // distinguishes the unsimplified analysis subject from the projected code.
  std::string source = fixture.str();
  auto returned = source.find("\"protocol.return\"(%yes)");
  source.replace(returned, StringRef("\"protocol.return\"(%yes)").size(),
                 "%both=arith.andi %yes,%yes : i1\n"
                 "\"protocol.return\"(%both)");
  struct Fixture {
    StringRef name, source;
    unsigned programs, calls;
  };
  for (const auto &input :
       {Fixture{"public coin", source, 1, 0},
        Fixture{"shared nested helpers", helperPrograms, 2, 4},
        Fixture{"polynomial helper observation", polynomialPrograms, 2, 1}})
    for (bool simplify : {false, true})
      cases.run(Twine(input.name) + (simplify ? " simplify" : " no simplify"),
                [&] {
                  compareProjection(context, input.source, input.programs,
                                    input.calls, simplify);
                });

  cases.run("unused observation in a later program fails preparation", [&] {
    std::string invalid = polynomialPrograms.str();
    auto extent = invalid.find("tensor<3x!field>");
    test::require(extent != std::string::npos, "observation fixture extent");
    invalid.replace(extent, StringRef("tensor<3x!field>").size(),
                    "tensor<2x!field>");
    auto original = mlir::parseSourceString<mlir::ModuleOp>(invalid, &context);
    test::require(bool(original) && succeeded(mlir::verify(*original)),
                  "invalid observation must reach helper expansion");
    auto before = print(*original);
    bool degreeRefusal = false;
    mlir::ScopedDiagnosticHandler expected(&context, [&](mlir::Diagnostic &d) {
      for (const auto &refusal : diagnostics::refusals(d))
        degreeRefusal |= refusal.code == "polynomial-formation";
      return mlir::success();
    });
    // The later unused observation only exposes its degree after @square is
    // expanded. No handle may be produced, even though main can be folded.
    auto handle = mathematical::PreparedProtocol::prepare(*original);
    test::require(!handle && degreeRefusal,
                  "preparation missed the later unused observation");
    test::require(print(*original) == before,
                  "failed preparation changed source");
    mlir::PassManager preparation(&context);
    preparation.addPass(protocol::createPrepareProtocolPass(false));
    degreeRefusal = false;
    test::require(failed(preparation.run(*original)) && degreeRefusal,
                  "explicit preparation missed the observation");
    test::require(print(*original) == before,
                  "failed staged preparation changed source");
    // Fix the native refusal for both options without imposing equality of
    // arbitrary invalid-input diagnostics with standalone projection.
    for (bool simplify : {false, true}) {
      RunOptions options;
      options.simplify = simplify;
      test::refuses(
          compileRun(invalid, "unused-observation.mlir", options, registry),
          "polynomial-formation");
    }
  });

  for (bool simplify : {false, true})
    cases.run(simplify ? "unused invalid helper before simplification"
                       : "unused invalid helper without simplification",
              [&] {
                std::string invalid = helperPrograms.str();
                auto end = invalid.find("}) {profile=");
                test::require(end != std::string::npos,
                              "helper insertion point");
                invalid.insert(end, "func.func private @unused(%x: i32) -> i32 "
                                    "{ return %x : i32 }\n");
                RunOptions options;
                options.simplify = simplify;
                test::refuses(compileRun(invalid, "unused-helper.mlir", options,
                                         registry),
                              "mathematical-formation");
              });
  return cases.result();
}
} // namespace
int main() {
  if (preparationCases())
    return 1;
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
