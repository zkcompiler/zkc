#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Compiler/Evm.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Transforms/EndpointClosure.h"
#include "zkc/Transforms/Stages.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral sourceText = R"mlir(
module {
 "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %a: !algebra.field<"bls12-381.fr">, %b: !algebra.field<"bls12-381.fr">, %c: !algebra.field<"bls12-381.fr">):
    %scaled = algebra.group_scale %g, %x : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
    %product = algebra.field_multiply %a, %b : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    %ok = algebra.field_equal %product, %c : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
    "protocol.return"(%scaled, %ok) : (!algebra.group<"bls12-381.g1">, i1) -> ()
  }) {sym_name="independent_numeric", function_type=(!algebra.group<"bls12-381.g1">,!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">,!algebra.field<"bls12-381.fr">)->(!algebra.group<"bls12-381.g1">,i1), roles=["P","V"], input_roles=[["P"],["P"],["V"],["V"],["V"]], output_roles=[["P"],["V"]]} : () -> ()
 }) {profile=#protocol.profile<protocol>} : () -> ()
})mlir";

// An index accumulator over field elements deliberately uses different state,
// item and capture types. The final vector is a two-lane invariant capture.
constexpr StringLiteral finiteSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="add",contract="index.add",arguments=[],implementation="",function_type=(!runtime.scope,ui64,ui64)->!exec.outcome<(ui64)>} : ()->()
 "data.domain"() ({ ^entry(%xs:!V,%ys:!V):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   %y = "data.domain_elements"(%ys) : (!V)->!data.domain<!F>
   %unused = "data.domain_zip"(%x,%y) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
   %unused_again = "data.domain_zip"(%y,%x) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
   "data.domain_yield"(%x) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V,!V)->!data.domain<!F>} : ()->()
 func.func private @step(%scope:!runtime.scope,%state:ui64,%item:!F,%xs:!V,%ys:!V,%increment:ui64,%held:!V) -> !exec.outcome<(ui64)> attributes {no_inline,runtime.origin=["step",[]]} {
   %next = "exec.apply"(%scope,%state,%increment) {binding=@add,parameters=[],site="add"} : (!runtime.scope,ui64,ui64)->!exec.outcome<(ui64)>
   "exec.dispatch"(%next)[^ok,^stop] : (!exec.outcome<(ui64)>)->()
 ^ok(%value:ui64):
   %result = "exec.returned"(%value) : (ui64)->!exec.outcome<(ui64)>
   func.return %result : !exec.outcome<(ui64)>
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(ui64)>
   func.return %failure : !exec.outcome<(ui64)>
 }
 func.func @work(%scope:!runtime.scope,%xs:!V,%ys:!V,%init:ui64,%increment:ui64,%held:!V) -> !exec.outcome<(ui64)> attributes {no_inline,runtime.origin=["work",[]]} {
   %r = "exec.fold"(%scope,%xs,%ys,%init,%increment,%held) {domain=@items,step=@step,site="fold"} : (!runtime.scope,!V,!V,ui64,ui64,!V)->!exec.outcome<(ui64)>
   "exec.dispatch"(%r)[^ok,^stop] : (!exec.outcome<(ui64)>)->()
 ^ok(%value:ui64):
   %result = "exec.returned"(%value) : (ui64)->!exec.outcome<(ui64)>
   func.return %result : !exec.outcome<(ui64)>
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(ui64)>
   func.return %failure : !exec.outcome<(ui64)>
 }
 "protocol.func"() ({ ^entry(%xs:!V,%ys:!V,%init:ui64,%increment:ui64,%held:!V):
   %r = "protocol.local_call"(%xs,%ys,%init,%increment,%held) {callee=@work,role="V",site="work"} : (!V,!V,ui64,ui64,!V)->ui64
   "protocol.return"(%r) : (ui64)->()
 }) {sym_name="main",function_type=(!V,!V,ui64,ui64,!V)->ui64,roles=["V"],input_roles=[["V"],["V"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

constexpr StringLiteral totalFiniteSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%x) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%state:!F,%item:!F,%xs:!V,%factor:!F) -> !F {
   %product = algebra.field_multiply %item,%factor : (!F,!F)->!F
   %next = algebra.field_add %state,%product : (!F,!F)->!F
   func.return %next : !F
 }
 "protocol.func"() ({ ^entry(%xs:!V,%init:!F,%factor:!F):
   %r = "algebra.finite_fold"(%xs,%init,%factor) {domain=@items,step=@step} : (!V,!F,!F)->!F
   "protocol.return"(%r) : (!F)->()
 }) {sym_name="main",function_type=(!V,!F,!F)->!F,roles=["V"],input_roles=[["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

// The transcript generation is affine carried state. Its callback must borrow
// the fold's scope, which owns the generation throughout the traversal.
constexpr StringLiteral capabilityFiniteSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
!T = !runtime.capability<transcript,"hash-chain.keccak256.bls12-381.fr64be/0">
!O = !exec.outcome<(!T)>
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="coordinates",contract="indices.empty",arguments=[],implementation="",function_type=(!runtime.scope)->!exec.outcome<(!algebra.indices)>} : ()->()
 "runtime.binding"() {sym_name="draw",contract="transcript.native.indexed.challenge",arguments=["hash-chain.keccak256.bls12-381.fr64be/0"],implementation="",function_type=(!runtime.scope,!T,!algebra.indices)->!exec.outcome<(!F,!T)>} : ()->()
 "data.domain"() ({ ^entry(%xs:!V):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%x) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @step(%scope:!runtime.scope,%state:!T,%item:!F,%xs:!V)->!O attributes {no_inline,runtime.origin=["step",[]]} {
   %coordinates = "exec.apply"(%scope) {binding=@coordinates,parameters=[],site="coordinates"} : (!runtime.scope)->!exec.outcome<(!algebra.indices)>
   "exec.dispatch"(%coordinates)[^invoke,^stop] : (!exec.outcome<(!algebra.indices)>)->()
 ^invoke(%indices:!algebra.indices):
   %draw = "exec.apply"(%scope,%state,%indices) {binding=@draw,parameters=[#runtime.origin<"main", #runtime.query_origin<"Round","draw",0,"random.bls12-381.fr/0","draw","V">>],site="draw"} : (!runtime.scope,!T,!algebra.indices)->!exec.outcome<(!F,!T)>
   "exec.dispatch"(%draw)[^done,^stop] : (!exec.outcome<(!F,!T)>)->()
 ^done(%unused:!F,%next:!T):
   %ok = "exec.returned"(%next) : (!T)->!O
   func.return %ok : !O
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!O
   func.return %failure : !O
 }
 func.func private @work(%scope:!runtime.scope,%xs:!V,%seed:!T)->!O attributes {no_inline,runtime.origin=["work",[]]} {
   %fold = "exec.fold"(%scope,%xs,%seed) {domain=@items,step=@step,site="fold"} : (!runtime.scope,!V,!T)->!O
   "exec.dispatch"(%fold)[^done,^stop] : (!O)->()
 ^done(%next:!T):
   %ok = "exec.returned"(%next) : (!T)->!O
   func.return %ok : !O
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!O
   func.return %failure : !O
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!T):
   %next = "protocol.local_call"(%xs,%seed) {callee=@work,role="V",site="work"} : (!V,!T)->!T
   %yes = arith.constant true
   "protocol.return"(%yes,%next) : (i1,!T)->()
 }) {sym_name="main",function_type=(!V,!T)->(i1,!T),roles=["V"],input_roles=[["V"],["V"]],output_roles=[["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

std::string replaceFixture(std::string text, StringRef before,
                           StringRef after) {
  auto at = text.find(before.str());
  require(at != std::string::npos, "missing fixture substitution");
  text.replace(at, before.size(), after.str());
  return text;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  registry.insert<evm::EvmDialect>();
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  std::string diagnostics;
  ScopedDiagnosticHandler capture(&context, [&](Diagnostic &diag) {
    raw_string_ostream out(diagnostics);
    diag.print(out);
    out << '\n';
    return success();
  });
  auto close = [&](StringRef text) {
    auto source = parseSourceString<ModuleOp>(text, &context);
    require(bool(source), "numeric source failed to parse");
    PassManager pm(&context);
    buildProjectionPipeline(pm, false);
    buildClosedExecutionPipeline(pm);
    require(succeeded(pm.run(*source)),
            "numeric source failed closed formation");
    return source;
  };
  auto closed = [&] { return close(sourceText); };
  cases.run("deployment ceilings reject zero and unsupported increases", [&] {
    EvmOptions options;
    options.limits.transcriptTransitions = 0;
    refuses(compileEvmProof(sourceText, "numeric.mlir", options, registry),
            "evm.limits");
    options.limits = EvmLimits();
    ++options.limits.publicElements;
    refuses(compileEvmProof(sourceText, "numeric.mlir", options, registry),
            "evm.limits");
  });
  cases.run("empty sources and unselected constructions refuse", [&] {
    refuses(compileEvmProof("", "empty.mlir", {}, registry),
            "evm.source-limit");
    refuses(compileEvmProof(sourceText, "numeric.mlir", {}, registry),
            "evm.construction");
  });
  cases.run(
      "unrelated numeric closure supports full field multiplication", [&] {
        auto source = closed();
        auto endpoint = take(closeEndpoint(*source, "V"));
        auto target = take(evm::lowerEndpoint(endpoint, {}));
        unsigned products = 0;
        target->walk(
            [&](evm::WordOp op) { products += op.opcode() == "mulmod"; });
        require(products == 1, "field multiplication was not operation based");
        require(succeeded(evm::checkTarget(*target)),
                "numeric target was illegal");
        bool native = false;
        target->walk([&](Operation *op) {
          native |= op->getName().getStringRef().starts_with("exec.") ||
                    op->getName().getStringRef().starts_with("runtime.");
        });
        require(!native, "native execution wrapper remained");
      });
  cases.run("unsupported reachable producer fails without blocking verifier",
            [&] {
              auto source = closed();
              auto endpoint = take(closeEndpoint(*source, "P"));
              refuses(evm::lowerEndpoint(endpoint, {}), "evm.lowering");
              require(StringRef(diagnostics).contains("evm.unsupported-type"),
                      "reachable type diagnostic was imprecise");
            });
  cases.run("target legality refuses residual potentially undefined division",
            [&] {
              auto source = closed();
              auto endpoint = take(closeEndpoint(*source, "V"));
              auto target = take(evm::lowerEndpoint(endpoint, {}));
              auto fn = *target->getOps<func::FuncOp>().begin();
              OpBuilder b(&context);
              b.setInsertionPointToStart(&fn.front());
              auto zero = arith::ConstantIntOp::create(b, fn.getLoc(), 0, 64);
              arith::DivUIOp::create(b, fn.getLoc(), zero, zero);
              require(failed(evm::checkTarget(*target)),
                      "illegal division passed full conversion");
            });
  cases.run("checked opcode rejects a malformed signature", [&] {
    OwningOpRef<ModuleOp> module(ModuleOp::create(UnknownLoc::get(&context)));
    OpBuilder b(&context);
    b.setInsertionPointToEnd(module->getBody());
    auto one = arith::ConstantIntOp::create(b, module->getLoc(), 1, 64);
    evm::CheckedOp::create(b, module->getLoc(), {b.getI64Type()},
                           "proof.receive", {one});
    require(failed(verify(*module)), "wrong proof receive signature verified");
  });
  cases.run(
      "scoped finite fold keeps scalar and slice captures invariant", [&] {
        auto source = close(finiteSource);
        source->walk([&](Operation *op) {
          if (!finite::isComputation(op))
            return;
          finite::Computation computation;
          require(succeeded(finite::describe(op, computation)),
                  "common finite description refused");
          require(computation.arguments == 2 && computation.states == 1 &&
                      computation.captures == 2,
                  "fixture lost distinct finite partitions");
        });
        auto target =
            take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
        unsigned loops = 0;
        target->walk([&](scf::ForOp loop) {
          ++loops;
          require(loop.getInitArgs().size() == 1 && loop.getNumResults() == 1,
                  "invariant captures became carried state");
          auto owner = loop->getParentOfType<func::FuncOp>();
          require(loop.getInitArgs()[0] == owner.getArgument(5),
                  "finite initial state was taken from a capture");
          auto calls = loop.getBody()->getOps<func::CallOp>();
          require(!calls.empty(), "missing finite callback");
          auto call = *calls.begin();
          require(call.getNumOperands() == 10 &&
                      call.getOperand(0) == owner.getArgument(0) &&
                      call.getOperand(1) == loop.getRegionIterArgs()[0] &&
                      call.getOperand(2).getType().isInteger(256) &&
                      call.getOperand(7) == owner.getArgument(6) &&
                      call.getOperand(8) == owner.getArgument(7) &&
                      call.getOperand(9) == owner.getArgument(8),
                  "callback state/item/domain/capture ABI was reordered");
        });
        require(loops == 1, "scoped finite regression did not reach its fold");
      });
  cases.run("discarded zip admission precedes even an empty traversal", [&] {
    auto source = close(finiteSource);
    auto target =
        take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
    unsigned checks = 0;
    target->walk([&](evm::CheckedOp check) {
      if (check.opcode() != "range.check")
        return;
      auto owner = check->getParentOfType<func::FuncOp>();
      require(!check->getParentOfType<scf::ForOp>(),
              "zero-trip traversal bypasses constructor admission");
      unsigned left = checks == 0 ? 2 : 4, right = checks == 0 ? 4 : 2;
      require(checks < 2 && check.getOperand(0) == owner.getArgument(left) &&
                  check.getOperand(1) == owner.getArgument(right),
              "discarded constructors lost admission order or operands");
      ++checks;
    });
    require(checks == 2, "discarded zip admission disappeared");
  });
  cases.run("scoped finite callbacks borrow authority over affine state", [&] {
    auto source = close(capabilityFiniteSource);
    auto target =
        take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
    unsigned loops = 0, challenges = 0;
    target->walk([&](scf::ForOp loop) {
      ++loops;
      auto owner = loop->getParentOfType<func::FuncOp>();
      require(loop.getInitArgs().size() == 1 &&
                  loop.getInitArgs()[0] == owner.getArgument(3),
              "transcript generation was not retained as carried state");
      auto calls = loop.getBody()->getOps<func::CallOp>();
      require(!calls.empty(), "missing affine callback");
      auto call = *calls.begin();
      require(call.getOperand(0) == owner.getArgument(0) &&
                  call.getOperand(1) == loop.getRegionIterArgs()[0],
              "finite callback lost borrowed scope or affine state");
    });
    target->walk([&](evm::CheckedOp check) {
      if (check.opcode() == "transcript.challenge")
        ++challenges;
    });
    require(loops == 1 && challenges == 1,
            "affine callback regression lost its checked challenge");
  });
  cases.run(
      "total finite fold preserves its field capture and zero-trip seed", [&] {
        auto source = close(totalFiniteSource);
        auto target =
            take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
        unsigned loops = 0;
        target->walk([&](scf::ForOp loop) {
          ++loops;
          require(loop.getInitArgs().size() == 1 &&
                      loop.getInitArgs()[0].getType().isInteger(256),
                  "total fold carried its field capture");
          auto calls = loop.getBody()->getOps<func::CallOp>();
          require(!calls.empty(), "missing total callback");
          auto call = *calls.begin();
          auto owner = loop->getParentOfType<func::FuncOp>();
          require(call.getNumOperands() == 5 &&
                      call.getOperand(0) == loop.getRegionIterArgs()[0] &&
                      call.getOperand(4) == owner.getArguments().back(),
                  "total callback capture depends on loop state");
        });
        require(loops == 1, "total finite regression lost its fold");
      });
  cases.run(
      "total collect passes captures without inventing carried state", [&] {
        auto text = replaceFixture(totalFiniteSource.str(),
                                   "%state:!F,%item:!F", "%item:!F");
        text = replaceFixture(
            std::move(text),
            "%next = algebra.field_add %state,%product : (!F,!F)->!F",
            "%next = algebra.field_add %product,%factor : (!F,!F)->!F");
        text = replaceFixture(std::move(text),
                              "\"algebra.finite_fold\"(%xs,%init,%factor) "
                              "{domain=@items,step=@step} : (!V,!F,!F)->!F",
                              "\"algebra.finite_collect\"(%xs,%factor) "
                              "{domain=@items,body=@step} : (!V,!F)->!V");
        text = replaceFixture(std::move(text),
                              "\"protocol.return\"(%r) : (!F)->()",
                              "\"protocol.return\"(%r) : (!V)->()");
        text = replaceFixture(std::move(text), "function_type=(!V,!F,!F)->!F",
                              "function_type=(!V,!F,!F)->!V");
        auto source = close(text);
        auto target =
            take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
        unsigned loops = 0;
        target->walk([&](scf::ForOp loop) {
          ++loops;
          require(loop.getInitArgs().empty(), "collect invented carried state");
          auto calls = loop.getBody()->getOps<func::CallOp>();
          require(!calls.empty(), "missing collect callback");
          auto call = *calls.begin();
          auto owner = loop->getParentOfType<func::FuncOp>();
          require(call.getNumOperands() == 4 &&
                      call.getOperand(3) == owner.getArguments().back(),
                  "collect reordered its invariant field capture");
        });
        require(loops == 1, "total collect regression lost its traversal");
      });
  cases.run("local calls enter scopes while finite callbacks borrow them", [&] {
    auto source = close(finiteSource);
    auto target =
        take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
    unsigned current = 0, borrowed = 0;
    target->walk([&](evm::CheckedOp check) {
      if (check.opcode() != "scope.enter")
        return;
      auto parent = check.getOperand(0).getDefiningOp<evm::CheckedOp>();
      if (parent && parent.opcode() == "scope.current")
        ++current;
      else {
        require(isa<BlockArgument>(check.getOperand(0)),
                "callback scope was neither borrowed nor acquired");
        ++borrowed;
      }
    });
    require(current == 1 && borrowed == 0,
            "finite callback entered a scope instead of borrowing its owner");
  });
  cases.run(
      "nested local calls in scoped helpers refuse common admission", [&] {
        auto text = replaceFixture(
            finiteSource.str(),
            "%r = \"exec.fold\"(%scope,%xs,%ys,%init,%increment,%held)",
            "%nested = \"protocol.local_call\"(%xs,%ys,%init,%increment,%held) "
            "{callee=@work,role=\"V\",site=\"nested\"} : "
            "(!V,!V,ui64,ui64,!V)->ui64\n"
            "   %r = \"exec.fold\"(%scope,%xs,%ys,%init,%increment,%held)");
        diagnostics.clear();
        auto malformed = parseSourceString<ModuleOp>(text, &context);
        bool rejected = !malformed || failed(verify(*malformed));
        require(rejected &&
                    StringRef(diagnostics).contains("protocol.local_call") &&
                    StringRef(diagnostics).contains("expects parent op"),
                "nested helper local call escaped common owner admission: " +
                    diagnostics);
      });
  auto boundaryYul = [&] {
    auto module = parseSourceString<ModuleOp>(R"mlir(
      module {
        func.func private @verify_endpoint(%generation:i64) -> (i1,i64) attributes {evm.entry} {
          %accepted = arith.constant true
          func.return %accepted,%generation : i1,i64
        }
      })mlir",
                                              &context);
    require(bool(module), "invalid boundary test target");
    NativeProofPolicy policy;
    policy.entry = "independent";
    policy.producer = "P";
    policy.validator = "V";
    policy.suite = "hash-chain.keccak256.bls12-381.fr64be/0";
    json::Value descriptor =
        json::Array{"zkc.native-proof/0", "independent", "binding-test",
                    json::Array{},        json::Array{}, json::Array{},
                    json::Array{},        json::Array{}, json::Array{}};
    return take(evm::exportYul(*module, "exact original bytes\n", descriptor,
                               policy, {}));
  };
  cases.run("minimum calldata is a decode refusal below the resource ceiling",
            [&] {
              auto yul = boundaryYul();
              require(StringRef(yul).contains(
                          "if lt(calldatasize(), 100) { evm_decode(7) }"),
                      "short ABI inputs retain the resource failure class");
              require(StringRef(yul).contains(
                          "if gt(calldatasize(), 262144) { evm_resource(10) }"),
                      "oversized calldata lost its resource refusal");
            });
  cases.run("static binding uses raw bytes and the exact original digest", [&] {
    auto yul = boundaryYul();
    StringRef text(yul);
    require(
        text.contains(
            "datacopy(root, dataoffset(\"bytes_0\"), datasize(\"bytes_0\"))") &&
            !text.contains("evm_static") && !text.contains("Compressed"),
        "static byte copying retained compression machinery");
    auto digest = toHex(
        SHA256::hash(arrayRefFromStringRef("exact original bytes\n")), true);
    require(text.contains(toHex(digest, true)) &&
                !text.contains(toHex("exact original bytes\n", true)),
            "binding source is not the exact original SHA256 identity");
    require(text.contains("verbatim_1i_0o(hex\"50\", boundState)"),
            "invocation observation lost its final POP sink");
  });
  return cases.result();
}
