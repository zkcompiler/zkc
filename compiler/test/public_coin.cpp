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
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <set>
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
    R"({"format":"zkc.public-coin-requirement/0","subject":"authored","deployment_entries":["main"],"entry":"main","prover":"P","verifier":"V","service":0,"decision":0,"bound_inputs":[],"draws":[{"query_site":"draw","delivery_site":"coin"}]})";
constexpr StringLiteral policyFixture = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!S = !protocol.service_ref<"random.bls12-381.fr/0">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="field.add",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "runtime.binding"() {sym_name="sum",contract="vector.sum",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()
 "data.domain"() ({^entry(%xs:!V):
   %items = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%items) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
func.func private @step(%scope:!runtime.scope,%a0:!F,%a1:!F,%a2:!V)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["step",[]]} {
%next_attempt = "exec.apply"(%scope,%a0,%a1) {binding=@add,parameters=[],site="add"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%next_attempt)[^next,^failed] : (!exec.outcome<(!F)>)->()
^next(%next:!F):

%done = "exec.returned"(%next) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
func.return %failure : !exec.outcome<(!F)>
}
func.func private @product(%a:!F,%b:!F)->!F {
   %p = "algebra.field_multiply"(%a,%b) : (!F,!F)->!F
   return %p : !F
 }
 "data.domain"() ({^entry(%a:!V,%b:!V):
   %a_items = "data.domain_elements"(%a) : (!V)->!data.domain<!F>
   %b_items = "data.domain_elements"(%b) : (!V)->!data.domain<!F>
   %pairs = "data.domain_zip"(%a_items,%b_items) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
   "data.domain_yield"(%pairs) : (!data.domain<!F,!F>)->()
 }) {sym_name="pairs",sym_visibility="private",function_type=(!V,!V)->!data.domain<!F,!F>} : ()->()
func.func private @mapped_row(%scope:!runtime.scope,%a0:!F,%a1:!F,%a2:!V,%a3:!V)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["mapped_row",[]]} {
%product_attempt = "exec.compute"(%scope,%a0,%a1) {callee=@product,site="product"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%product_attempt)[^product,^failed] : (!exec.outcome<(!F)>)->()
^product(%value:!F):

%done = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
func.return %failure : !exec.outcome<(!F)>
}
func.func @work(%scope:!runtime.scope,%a0:!V,%a1:!V,%a2:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
%fold_attempt = "exec.fold"(%scope,%a0,%a2) {domain=@items,step=@step,site="fold"} : (!runtime.scope,!V,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%fold_attempt)[^fold,^failed] : (!exec.outcome<(!F)>)->()
^fold(%fold:!F):
%map_attempt = "exec.collect"(%scope,%a0,%a1) {domain=@pairs,body=@mapped_row,site="map"} : (!runtime.scope,!V,!V)->!exec.outcome<(!V)>
"exec.dispatch"(%map_attempt)[^map,^failed] : (!exec.outcome<(!V)>)->()
^map(%mapped:!V):
%sum_attempt = "exec.apply"(%scope,%mapped) {binding=@sum,parameters=[],site="sum"} : (!runtime.scope,!V)->!exec.outcome<(!F)>
"exec.dispatch"(%sum_attempt)[^sum,^failed] : (!exec.outcome<(!F)>)->()
^sum(%sum:!F):
%result_attempt = "exec.apply"(%scope,%fold,%sum) {binding=@add,parameters=[],site="result"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
"exec.dispatch"(%result_attempt)[^result,^failed] : (!exec.outcome<(!F)>)->()
^result(%result:!F):

%done = "exec.returned"(%result) : (!F)->!exec.outcome<(!F)>
func.return %done : !exec.outcome<(!F)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
func.return %failure : !exec.outcome<(!F)>
}
 "protocol.func"() ({^entry(%service:!S,%a:!V,%b:!V,%seed:!F):
   %local = "protocol.local_call"(%a,%b,%seed) {callee=@work,role="P",site="work"} : (!V,!V,!F)->!F
   %q = "protocol.query"(%service) {owner="V",method="draw",site="draw"} : (!S)->!F
   %d = protocol.exchange %q {sender="V",receiver="P",site="coin"} : !F
   %yes = arith.constant true
   "protocol.return"(%yes) : (i1)->()
 }) {sym_name="main",function_type=(!S,!V,!V,!F)->i1,roles=["P","V"],input_roles=[["V"],["P"],["P"],["P"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() })mlir";
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
  func.func private @square(%values: !algebra.field_array<"bls12-381.fr", 2>) -> !polynomial {
    %linear = "poly.mle"(%values) : (!algebra.field_array<"bls12-381.fr", 2>)->!polynomial
    %square = "poly.multiply"(%linear, %linear) : (!polynomial, !polynomial)->!polynomial
    return %square : !polynomial
  }
  "protocol.func"() ({
    %yes = arith.constant true
    %both = arith.andi %yes, %yes : i1
    "protocol.return"(%both) : (i1)->()
  }) {sym_name="main", function_type=()->i1, roles=["V"], input_roles=[], output_roles=[["V"]]} : ()->()
  "protocol.func"() ({
  ^entry(%values: !algebra.field_array<"bls12-381.fr", 2>):
    %square = func.call @square(%values) : (!algebra.field_array<"bls12-381.fr", 2>)->!polynomial
    %unused = "poly.coefficients"(%square) : (!polynomial)->!algebra.field_array<"bls12-381.fr", 3>
    "protocol.return"(%values) : (!algebra.field_array<"bls12-381.fr", 2>)->()
  }) {sym_name="observation", function_type=(!algebra.field_array<"bls12-381.fr", 2>)->!algebra.field_array<"bls12-381.fr", 2>, roles=["P"], input_roles=[["P"]], output_roles=[["P"]]} : ()->()
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
json::Value analyze(StringRef source = fixture,
                    MathematicalSelectionPolicy policy = {}) {
  mlir::DialectRegistry registry;
  registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto module = mlir::parseSourceString<mlir::ModuleOp>(source, &context);
  require(bool(module), "fixture parse");
  auto before = print(*module);
  std::string independent = requirement.str();
  auto report = analyzePublicCoin(*module, independent, policy);
  require(bool(report), "analysis");
  require(print(*module) == before, "analysis changed source");
  std::string text;
  raw_string_ostream(text) << *report;
  auto checked = checkPublicCoin(*module, independent, text, policy);
  require(!checked, "report check");
  auto bad = checkPublicCoin(*module, independent, "{}", policy);
  require(bool(bad), "bad report accepted");
  consumeError(std::move(bad));
  auto prepared = mathematical::PreparedProtocol::prepare(*module, policy);
  require(bool(prepared), "independent preparation failed");
  require(succeeded(prepared->selectEntries({"main"})),
          "entry selection failed");
  auto snapshot = prepared->snapshot();
  auto printed = print(*snapshot);
  auto hash = toHex(SHA256::hash(arrayRefFromStringRef(printed)), true);
  require(report->getAsObject()->getString("prepared_ir_sha256") == hash,
          "public-coin fingerprint differs from selected preparation");
  for (auto different :
       {MathematicalSelectionPolicy{!policy.finiteBulk,
                                    policy.vectorReductionFusion,
                                    policy.collectFoldFusion},
        MathematicalSelectionPolicy{policy.finiteBulk,
                                    !policy.vectorReductionFusion,
                                    policy.collectFoldFusion},
        MathematicalSelectionPolicy{policy.finiteBulk,
                                    policy.vectorReductionFusion,
                                    !policy.collectFoldFusion}}) {
    auto mismatch = checkPublicCoin(*module, independent, text, different);
    require(bool(mismatch), "report accepted under a different policy");
    require(
        namesIdentifier(toString(std::move(mismatch)), "public-coin-report"),
        "policy mismatch has wrong refusal identifier");
  }
  for (StringRef key :
       {"finite_bulk", "fuse_vector_reductions", "fuse_collect_fold"}) {
    auto mutated = json::parse(text);
    require(bool(mutated), "report mutation parse");
    (*mutated->getAsObject())[key] = !*mutated->getAsObject()->getBoolean(key);
    std::string changed;
    raw_string_ostream(changed) << *mutated;
    auto mismatch = checkPublicCoin(*module, independent, changed, policy);
    require(bool(mismatch), "changed report policy accepted");
    require(
        namesIdentifier(toString(std::move(mismatch)), "public-coin-report"),
        "changed policy has wrong refusal identifier");
  }
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
    auto extent = invalid.find("!algebra.field_array<\"bls12-381.fr\", 3>");
    test::require(extent != std::string::npos, "observation fixture extent");
    invalid.replace(
        extent, StringRef("!algebra.field_array<\"bls12-381.fr\", 3>").size(),
        "!algebra.field_array<\"bls12-381.fr\", 2>");
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
  auto *draw = (*report.getAsObject()->getObject("graph")->getArray("draws"))[0]
                   .getAsObject();
  require(draw->getString("site") == "draw" &&
              draw->getObject("delivery")->getString("site") == "coin",
          "owned sites");
  auto *request = draw->getObject("request");
  require(request &&
              request->getString("contract") == "random.bls12-381.fr/0" &&
              request->getString("method") == "draw" &&
              request->getString("law") == "uniform-field",
          "request metadata did not outlive its source context");
  mlir::DialectRegistry registry;
  RunOptions options;
  options.publicCoinRequirement = requirement.str();
  std::set<std::string> preparedHashes[2], bundleHashes[2];
  for (bool fuse : {false, true})
    for (bool finite : {false, true})
      for (bool collect : {false, true}) {
        options.mathematicalSelection = {finite, fuse, collect};
        auto selected = analyze(policyFixture, options.mathematicalSelection);
        auto result =
            compileRun(policyFixture, "public-coin.mlir", options, registry);
        auto compiledResult = test::take(std::move(result));
        require(compiledResult.publicCoin && !compiledResult.correspondence,
                "checked invocation");
        auto compiled = json::parse(*compiledResult.publicCoin);
        require(bool(compiled) &&
                    *compiled->getAsObject()->get("view") == selected,
                "same unsimplified view");
        auto &view = *selected.getAsObject();
        require(view.getBoolean("finite_bulk") == finite &&
                    view.getBoolean("fuse_vector_reductions") == fuse &&
                    view.getBoolean("fuse_collect_fold") == collect,
                "public-coin view lost preparation choice");
        bundleHashes[collect].insert(
            compiled->getAsObject()->getString("bundle_sha256")->str());
        preparedHashes[collect].insert(
            view.getString("prepared_ir_sha256")->str());
        require(compiled->getAsObject()->getBoolean("fuse_vector_reductions") ==
                        fuse &&
                    compiled->getAsObject()->getBoolean("finite_bulk") ==
                        finite &&
                    compiled->getAsObject()->getBoolean("fuse_collect_fold") ==
                        collect,
                "compiled public-coin record lost preparation choice");
        auto *passes =
            compiled->getAsObject()->getArray("subject_to_bundle_stages");
        require(passes && !passes->empty() &&
                    passes->front().getAsString() == "checked-preparation",
                "compiled view omitted preparation before projection");
      }
  require(preparedHashes[0].size() == 1 &&
              preparedHashes[0] == preparedHashes[1],
          "scoped source preparation must retain the same unsimplified body");
  require(bundleHashes[0].size() == 4 && bundleHashes[1].size() == 4,
          "fixture must distinguish finite/vector selection in emitted "
          "bundles under each collect-fold choice: " +
              std::to_string(bundleHashes[0].size()) + ", " +
              std::to_string(bundleHashes[1].size()));
  for (bool simplify : {false, true})
    for (bool fix : {false, true}) {
      options.simplify = simplify;
      options.fixPolynomialFactors = fix;
      auto result =
          compileRun(fixture, "reported-stages.mlir", options, registry);
      require(bool(result) && result->publicCoin, "reported pipeline refused");
      auto compiled = json::parse(*result->publicCoin);
      require(bool(compiled), "compiled pipeline report is not JSON");
      json::Array expected{"checked-preparation", "checked-oracle-realization",
                           "zkc-project-protocol"};
      if (simplify)
        expected.push_back("zkc-simplify-participant");
      if (fix)
        expected.push_back("zkc-fix-polynomial-factors");
      expected.push_back("zkc-lower-closed-participant");
      expected.push_back("zkc-select-physical");
      auto *passes =
          compiled->getAsObject()->getArray("subject_to_bundle_stages");
      require(passes && *passes == expected,
              "compiled report differs from selected pipeline stages");
    }
  options.entry = "absent";
  auto refused = compileRun(fixture, "public-coin.mlir", options, registry);
  require(!refused, "entry mismatch accepted");
  consumeError(refused.takeError());
  outs() << "public-coin source immutability, report ownership and checked API "
            "passed\n";
}
