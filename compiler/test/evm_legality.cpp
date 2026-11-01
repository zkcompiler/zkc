#include "../lib/Target/Evm/Arithmetic.h"
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
#include "zkc/Compiler/Language.h"
#include "zkc/Dialect/Data/IR/DataTypes.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Target/Evm/Wire.h"
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

constexpr StringLiteral orderedScalarSource = R"mlir(
!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "runtime.binding"() {sym_name="mul",contract="field.mul",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope,!F,!F)->!exec.outcome<(!F)>} : ()->()
 func.func private @work(%scope:!runtime.scope,%a:!F,%b:!F)->!exec.outcome<(!F)> attributes {no_inline,runtime.origin=["work",[]]} {
   %r = "exec.apply"(%scope,%a,%b) {binding=@mul,parameters=[],site="mul"} : (!runtime.scope,!F,!F)->!exec.outcome<(!F)>
   "exec.dispatch"(%r)[^ok,^stop] : (!exec.outcome<(!F)>)->()
 ^ok(%value:!F):
   %result = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
   func.return %result : !exec.outcome<(!F)>
 ^stop(%reason:!exec.stop):
   %failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(!F)>
   func.return %failure : !exec.outcome<(!F)>
 }
 "protocol.func"() ({ ^entry(%a:!F,%b:!F):
   %product = "protocol.local_call"(%a,%b) {callee=@work,role="V",site="work"} : (!F,!F)->!F
   %ok = algebra.field_equal %product,%a : (!F,!F)->i1
   "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!F,!F)->i1,roles=["V"],input_roles=[["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir";

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
            "numeric source failed closed formation: " + diagnostics);
    return source;
  };
  auto closed = [&] { return close(sourceText); };
  auto proofSource = [](StringRef helper, StringRef outputs, StringRef body) {
    return ("module scalar; domain Fr=field(\"bls12-381.fr\"); " + helper +
            " protocol Work roles(P,V)(a:Fr@V,b:Fr@V,c:Fr@V,"
            "challenges:Random<Fr>@V)->(" +
            outputs +
            "){let challenge=challenges.draw();"
            "let delivered=send V->P(challenge);" +
            body +
            "} proof Proof=Work{prover P;verifier V;public{a,b,c};"
            "accept accepted;construction fiat_shamir("
            "\"hash-chain.keccak256.bls12-381.fr64be/0\",challenges);}")
        .str();
  };
  auto originalSource = [&](StringRef text) {
    auto project = take(
        language::analyze(
            take(language::capture({{"scalar", text.str(), "scalar.zkc"}})))
            .checkedProject());
    return take(language::prepareOriginal(
        take(language::closeEntry(project, "scalar::Proof"))));
  };
  auto compileSource = [&](StringRef text) {
    return take(compileEvmEntry(originalSource(text)));
  };
  constexpr StringLiteral bytesSource = R"zkc(
module scalar;
type Bytes=builtin("bytes");
fn at(value:Bytes,position:index)->index=primitive("bytes.at");
protocol Work roles(P,V)(value:Bytes@V,position:index@V,expected:index@V)
  ->(selected:index@V,accepted:bool@V) {
  let selected=at(value,position);
  return(selected=selected,accepted=selected==expected);
}
proof Proof=Work {
  prover P; verifier V; public{value,position,expected};
  accept accepted; construction authored;
}
)zkc";
  cases.run("source byte indexing reaches the exact packed byte helper", [&] {
    auto result = compileSource(bytesSource);
    require(result.sourceBytes().contains("contract = \"bytes.at\""),
            "fixture did not use the native byte source contract");
    auto target = result.targetSnapshot();
    unsigned accesses = 0;
    target->walk([&](evm::CheckedOp op) {
      if (op.opcode() != "bytes.get")
        return;
      ++accesses;
      require(isa<data::BytesType>(
                  op->getAttrOfType<TypeAttr>("value_type").getValue()) &&
                  op->getNumOperands() == 3 && op->getNumResults() == 1 &&
                  op.getResult(0).getType().isInteger(64),
              "byte indexing lost its complete type or index result");
    });
    require(accesses == 1 &&
                StringRef(result.yul()).contains("byte(0, mload(cell))"),
            "native byte indexing did not reach packed-byte extraction");
  });
  for (bool parameters : {false, true})
    cases.run(
        parameters ? "byte indexing refuses invocation parameters"
                   : "byte indexing refuses an inexact binding type",
        [&] {
          auto original = originalSource(bytesSource);
          auto source = parseSourceString<ModuleOp>(original.bytes(), &context);
          require(bool(source), "byte source did not parse");
          Operation *binding = nullptr;
          source->walk([&](Operation *op) {
            auto contract = op->getAttrOfType<StringAttr>("contract");
            if (op->getName().getStringRef() == "runtime.binding" && contract &&
                contract.getValue() == "bytes.at")
              binding = op;
          });
          require(binding, "byte source binding disappeared");
          OpBuilder b(&context);
          if (parameters) {
            auto name = binding->getAttrOfType<StringAttr>("sym_name");
            unsigned changed = 0;
            source->walk([&](Operation *op) {
              auto ref = op->getAttrOfType<FlatSymbolRefAttr>("binding");
              if (ref && ref.getValue() == name.getValue()) {
                op->setAttr(
                    "parameters",
                    b.getArrayAttr({b.getIntegerAttr(
                        IntegerType::get(&context, 64, IntegerType::Unsigned),
                        1)}));
                ++changed;
              }
            });
            require(changed == 1, "byte invocation was not mutated");
          } else {
            auto signature = cast<FunctionType>(
                binding->getAttrOfType<TypeAttr>("function_type").getValue());
            SmallVector<Type> inputs(signature.getInputs());
            inputs[1] = b.getI1Type();
            binding->setAttr("function_type",
                             TypeAttr::get(b.getFunctionType(
                                 inputs, signature.getResults())));
          }
          diagnostics.clear();
          require(failed(verify(*source)),
                  "malformed byte contract passed common admission");
          require(StringRef(diagnostics)
                      .contains(parameters ? "interactive-kernel-parameters"
                                           : "binding-signature"),
                  "byte refusal lost its diagnostic: " + diagnostics);
        });
  cases.run("no-draw source retains common construction refusal", [&] {
    auto text = proofSource("", "accepted:bool@V", "return(accepted=a*b==c);");
    text = replaceFixture(
        std::move(text),
        "let challenge=challenges.draw();let delivered=send V->P(challenge);",
        "");
    refuses(compileEvmEntry(originalSource(text)), "native-proof-policy");
  });
  for (StringRef expression : {"a*b==c", "a+b==c", "a-b==c", "!(a==b)",
                               "a==b && b==c", "a==b || b==c", "a+1==c"}) {
    cases.run(
        ("pure and ordered scalar legalization: " + expression).str(), [&] {
          auto pure = compileSource(
              proofSource("", "accepted:bool@V",
                          ("return(accepted=" + expression + ");").str()));
          auto ordered = compileSource(proofSource(
              ("fn work(a:Fr,b:Fr,c:Fr)->bool{return " + expression + ";}")
                  .str(),
              "accepted:bool@V",
              "let result@V=work(a,b,c);return(accepted=result);"));
          require(succeeded(evm::checkTarget(*pure.targetSnapshot())) &&
                      succeeded(evm::checkTarget(*ordered.targetSnapshot())),
                  "scalar legalization did not produce legal targets");
        });
  }
  for (StringRef contract : {"field.neg", "field.inverse"})
    cases.run(("ordered unary scalar legalization: " + contract).str(), [&] {
      compileSource(
          proofSource(("fn work(a:Fr,b:Fr,c:Fr)->bool{return kernel<Fr>(\"" +
                       contract + "\",a)==c;}")
                          .str(),
                      "accepted:bool@V",
                      "let result@V=work(a,b,c);return(accepted=result);"));
    });
  cases.run(
      "selected acceptance follows projected and expanded output lanes", [&] {
        auto result = compileSource(proofSource(
            "", "hidden:Fr@P,extra:Fr@V,other:bool@V,accepted:bool@V",
            "return(hidden=delivered,extra=a+b,other=true,accepted=a*b==c);"));
        auto target = result.targetSnapshot();
        for (auto function : target->getOps<func::FuncOp>()) {
          if (!function->hasAttr("evm.entry"))
            continue;
          auto ports = function->getAttrOfType<ArrayAttr>("evm.output_ports");
          require(ports && ports.size() == 3 &&
                      cast<IntegerAttr>(ports[2]).getUInt() == 3 &&
                      function.getNumResults() == 4 &&
                      function.getResultTypes()[0].isInteger(256),
                  "acceptance mapping lost source output ownership or Fr lane");
        }
        require(result.policy().acceptance == 3,
                "test did not select the non-first original Boolean");
      });
  cases.run("ordered scalar binding retains its admitted callable", [&] {
    auto source = close(orderedScalarSource);
    take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
  });
  for (auto replacement :
       {std::pair<StringRef, StringRef>{"arguments=[\"bls12-381.fr\"]",
                                        "arguments=[]"},
        {"arguments=[\"bls12-381.fr\"]", "arguments=[\"koala-bear\"]"},
        {"parameters=[]", "parameters=[1:ui64]"},
        {"function_type=(!runtime.scope,!F,!F)",
         "function_type=(!runtime.scope,!F,i1)"}}) {
    cases.run("malformed scalar binding: " + replacement.second, [&] {
      diagnostics.clear();
      auto text = replaceFixture(orderedScalarSource.str(), replacement.first,
                                 replacement.second);
      auto malformed = parseSourceString<ModuleOp>(text, &context);
      require(!malformed || failed(verify(*malformed)),
              "malformed scalar contract escaped common admission");
      StringRef code = replacement.first == "parameters=[]"
                           ? "interactive-kernel-parameters"
                           : "binding-signature";
      require(StringRef(diagnostics).contains(code),
              "scalar contract refusal lost its diagnostic: " + diagnostics);
    });
  }
  cases.run("EVM refuses a valid pinned provider instead of replacing it", [&] {
    auto text = replaceFixture(orderedScalarSource.str(), "implementation=\"\"",
                               "implementation=\"arkworks/field.mul\"");
    auto source = close(text);
    diagnostics.clear();
    refuses(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}),
            "evm.lowering");
    require(StringRef(diagnostics).contains("pinned runtime implementation"),
            "provider constraint was silently discarded");
  });
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
  cases.run("deployment forks are typed and exact", [&] {
    require(take(parseEvmFork("cancun")) == EvmFork::Cancun &&
                take(parseEvmFork("prague")) == EvmFork::Prague,
            "fork parser did not retain the selected deployment");
    require(evmForkName(EvmFork::Cancun) == "cancun" &&
                evmForkName(EvmFork::Prague) == "prague",
            "fork spelling is not canonical");
    for (StringRef name : {"", "Cancun", "Prague", "shanghai"})
      refuses(parseEvmFork(name), "evm.fork");
    EvmOptions options;
    options.fork = static_cast<EvmFork>(255);
    refuses(compileEvmProof(sourceText, "numeric.mlir", options, registry),
            "evm.fork");
  });
  cases.run("empty sources and malformed proof selections refuse", [&] {
    refuses(compileEvmProof("", "empty.mlir", {}, registry),
            "evm.source-limit");
    refuses(compileEvmProof(sourceText, "numeric.mlir", {}, registry),
            "native-proof-policy");
  });
  cases.run(
      "unrelated numeric closure supports full field multiplication", [&] {
        auto source = closed();
        auto endpoint = take(closeEndpoint(*source, "V"));
        auto target = take(evm::lowerEndpoint(endpoint, {}));
        unsigned products = 0;
        target->walk(
            [&](evm::CheckedOp op) { products += op.opcode() == "field.mul"; });
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
      auto leftLength = check.getOperand(0).getDefiningOp<evm::CheckedOp>();
      auto rightLength = check.getOperand(1).getDefiningOp<evm::CheckedOp>();
      require(checks < 2 && leftLength && rightLength &&
                  leftLength.opcode() == "vector.length" &&
                  rightLength.opcode() == "vector.length" &&
                  leftLength.getOperand(1) == owner.getArgument(left) &&
                  rightLength.getOperand(1) == owner.getArgument(right),
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
  cases.run("filtered fold guards every lane of field and sequence state", [&] {
    auto source = close(R"mlir(
!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
 "data.domain"() ({ ^entry(%xs:!V):
   %x = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
   "data.domain_yield"(%x) : (!data.domain<!F>)->()
 }) {sym_name="items",sym_visibility="private",function_type=(!V)->!data.domain<!F>} : ()->()
 func.func private @keep(%item:!F,%xs:!V)->i1 {
   %no = arith.constant false
   func.return %no : i1
 }
 func.func private @step(%state:!F,%held:!V,%item:!F,%xs:!V)->(!F,!V) {
   %next = algebra.field_add %state,%item : (!F,!F)->!F
   func.return %next,%held : !F,!V
 }
 "protocol.func"() ({ ^entry(%xs:!V,%seed:!F,%held:!V):
   %r:2 = "algebra.finite_fold"(%xs,%seed,%held) {domain=@items,predicate=@keep,step=@step} : (!V,!F,!V)->(!F,!V)
   "protocol.return"(%r#0,%r#1) : (!F,!V)->()
 }) {sym_name="main",function_type=(!V,!F,!V)->(!F,!V),roles=["V"],input_roles=[["V"],["V"],["V"]],output_roles=[["V"],["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
    auto target =
        take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
    unsigned guarded = 0;
    target->walk([&](scf::ForOp loop) {
      auto branch = loop.getBody()->getOps<scf::IfOp>();
      require(!branch.empty(), "filtered fold lost its predicate branch");
      auto condition = *branch.begin();
      require(condition.getNumResults() == 3 &&
                  condition.getResult(0).getType().isInteger(256) &&
                  condition.getResult(1).getType().isInteger(64) &&
                  condition.getResult(2).getType().isInteger(64),
              "filtered fold branch lost expanded state lanes");
      auto predicate = condition.getCondition().getDefiningOp<func::CallOp>();
      require(predicate && predicate->getBlock() == loop.getBody(),
              "predicate was not evaluated before the step branch");
      auto steps = condition.getThenRegion().front().getOps<func::CallOp>();
      require(!steps.empty() && (*steps.begin()).getNumOperands() == 6,
              "step was not guarded with its complete state ABI");
      require(condition.getElseRegion().front().getOps<func::CallOp>().empty(),
              "false predicate still invokes the step");
      require(llvm::equal(condition.elseYield().getOperands(),
                          loop.getRegionIterArgs()),
              "false predicate did not preserve every carried lane");
      ++guarded;
    });
    require(guarded == 1, "filtered fold did not reach its guarded loop");
  });
  cases.run("scoped filtered fold guards its borrowed affine callback", [&] {
    auto text = replaceFixture(capabilityFiniteSource.str(),
                               " func.func private @step(", R"mlir(
 func.func private @keep(%scope:!runtime.scope,%item:!F,%xs:!V)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["keep",[]]} {
   %no = "exec.boolean"(%scope) {value=false,site="keep"} : (!runtime.scope)->!exec.outcome<(i1)>
   "exec.dispatch"(%no)[^done,^stop] : (!exec.outcome<(i1)>)->()
 ^done(%value:i1):
   %ok = "exec.returned"(%value) : (i1)->!exec.outcome<(i1)>
   func.return %ok : !exec.outcome<(i1)>
 ^stop(%reason:!exec.stop):
   %failed = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
   func.return %failed : !exec.outcome<(i1)>
 }
 func.func private @step()mlir");
    text = replaceFixture(std::move(text), "domain=@items,step=@step",
                          "domain=@items,predicate=@keep,step=@step");
    auto source = close(text);
    auto target =
        take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
    unsigned guarded = 0;
    target->walk([&](scf::ForOp loop) {
      auto branches = loop.getBody()->getOps<scf::IfOp>();
      require(!branches.empty(), "scoped filter lost its guarded step");
      auto branch = *branches.begin();
      auto calls = branch.getThenRegion().front().getOps<func::CallOp>();
      require(!calls.empty(), "filtered affine callback disappeared");
      auto callback = *calls.begin();
      auto owner = loop->getParentOfType<func::FuncOp>();
      require(callback.getOperand(0) == owner.getArgument(0) &&
                  callback.getOperand(1) == loop.getRegionIterArgs()[0],
              "filtered callback lost borrowed scope or generation");
      require(llvm::equal(branch.elseYield().getOperands(),
                          loop.getRegionIterArgs()),
              "skipped callback changed its affine generation");
      ++guarded;
    });
    require(guarded == 1, "scoped filtered fold lost its loop");
  });
  cases.run(
      "total collect keeps captures independent of its output cursor", [&] {
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
          require(loop.getInitArgs().size() == 1 &&
                      loop.getInitArgs()[0].getType().isInteger(64),
                  "collect lost its output position");
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
  for (bool sequence : {false, true})
    for (bool filtered : {false, true})
      cases.run(
          (Twine(sequence ? "sequence" : "vector") +
           (filtered ? " filtered" : " unfiltered") +
           " collect separates 1025 candidates from output capacity"),
          [&] {
            std::string text;
            raw_string_ostream out(text);
            StringRef container = sequence ? "Sequence" : "Vector";
            out << R"zkc(module scalar;
domain F=field("koala-bear.ext4-binomial3");
type Vector<E:Field> = builtin("vector",E);
type Sequence<T:Type+Copy+Drop> = builtin("sequence",T);
domain fn range(lower:index,upper:index)->domain<index> = domain("range");
fn less(left:index,right:index)->bool=primitive("index.less");
fn collect<I:Type+Copy+Drop,E:Field>(rows:domain<I>,)zkc";
            if (filtered)
              out << "keep:fn(item:I)->bool effects(stop) where "
                     "item_from(item,rows),";
            out << "body:fn(item:I)->E effects(stop) where "
                   "item_from(item,rows))->"
                << container << "<E> effects(stop)=finite(\"local.collect."
                << (sequence ? "sequence" : "vector")
                << (filtered ? "_where" : "") << "\");\n"
                << "fn length<E:Field>(values:" << container
                << "<E>)->index=primitive(\""
                << (sequence ? "sequence.length" : "vector.length") << "\");\n"
                << "fn work(seed:F,keep:index)->index { let "
                   "values=collect(range(0,1025),";
            if (filtered)
              out << "fn(i)=>less(i,keep),";
            out << R"zkc(fn(i)=>kernel<F>("field.inverse",seed));
  return length(values);
}
protocol Work roles(P,V)(seed:F@V,keep:index@V,expected:index@V)
  ->(accepted:bool@V) {
  let size=work(seed,keep);
  return(accepted=size==expected);
}
proof Proof=Work {
  prover P;verifier V;public{seed,keep,expected};
  accept accepted;construction authored;
}
)zkc";
            auto original = originalSource(text);
            auto policy = take(language::proofPolicy(original));
            auto source = close(original.bytes());
            EvmOptions options;
            options.limits.publicElements = 3;
            auto target = take(evm::lowerEndpoint(
                take(closeEndpoint(*source, policy.validator)), options));
            evm::NativeLayouts layouts(context);
            evm::detail::Arithmetic arithmetic(layouts, options.limits);
            evm::WireGenerator wire(layouts, options.limits);
            unsigned stores = 0, lengths = 0;
            scf::ForOp traversal;
            target->walk([&](evm::CheckedOp op) {
              if (op.opcode() != (sequence ? "sequence.set" : "vector.set"))
                return;
              ++stores;
              traversal = op->getParentOfType<scf::ForOp>();
              require(bool(traversal), "collect lost its traversal");
              auto allocation =
                  op.getOperand(0).getDefiningOp<evm::CheckedOp>();
              auto capacity = op.getOperand(1).getDefiningOp<arith::SelectOp>();
              require(allocation && capacity &&
                          allocation.getOperand(0) == capacity &&
                          capacity.getTrueValue() == traversal.getUpperBound(),
                      "collect allocation did not bound storage alone");
              auto ceiling =
                  capacity.getFalseValue().getDefiningOp<arith::ConstantOp>();
              require(ceiling &&
                          cast<IntegerAttr>(ceiling.getValue()).getInt() == 3,
                      "collect ignored the configured output ceiling");
              auto condition =
                  capacity.getCondition().getDefiningOp<arith::CmpIOp>();
              require(condition &&
                          condition.getPredicate() ==
                              arith::CmpIPredicate::ult &&
                          condition.getLhs() == traversal.getUpperBound() &&
                          condition.getRhs() == ceiling,
                      "collect capacity was not min(candidates, ceiling)");
              require(op.getOperand(2) == traversal.getRegionIterArgs()[0],
                      "collect stores by traversal rather than selection");
              auto callback = op.getOperand(3).getDefiningOp<func::CallOp>();
              require(callback && callback->getBlock() == op->getBlock() &&
                          callback->isBeforeInBlock(op),
                      "capacity check preempted the selected body");
              if (filtered) {
                auto branch = op->getParentOfType<scf::IfOp>();
                auto predicate =
                    branch ? branch.getCondition().getDefiningOp<func::CallOp>()
                           : func::CallOp();
                require(predicate &&
                            predicate->getBlock() == traversal.getBody() &&
                            predicate->isBeforeInBlock(branch) &&
                            llvm::equal(branch.elseYield().getOperands(),
                                        traversal.getRegionIterArgs()),
                        "predicate or skipped selection was reordered");
              }
              std::string helper = sequence ? take(wire.operation(op))
                                            : take(arithmetic.helper(op));
              std::string definitions =
                  sequence ? wire.definitions() : arithmetic.helpers();
              StringRef definition =
                  StringRef(definitions)
                      .substr(definitions.find("function " + helper + "("));
              auto resource = definition.find("evm_resource(2)");
              auto fault = definition.find("evm_fault(3)");
              require(resource != StringRef::npos && fault != StringRef::npos &&
                          resource < fault,
                      "output ceiling must precede fresh-buffer fault");
              require(definition.contains(sequence ? "lt(i, 3)" : "lt(i,3)"),
                      "selected write ignored the configured ceiling");
              Value capacityValue = op.getOperand(1);
              op->setOperand(1, traversal.getUpperBound());
              diagnostics.clear();
              require(failed(op.verify()) &&
                          StringRef(diagnostics).contains("evm.construction"),
                      "store accepted a count different from allocation");
              op->setOperand(1, capacityValue);
            });
            require(stores == 1, "collect must use one fresh-buffer store");
            target->walk([&](evm::CheckedOp op) {
              require(op.opcode() != "vector.append" &&
                          op.opcode() != "sequence.append",
                      "collect introduced repeated append allocation");
              if (op.opcode() ==
                  (sequence ? "sequence.length" : "vector.length")) {
                ++lengths;
                require(op.getOperand(1) == traversal.getResult(0),
                        "collect exposed capacity as its output length");
              }
            });
            require(lengths == 1, "collect result count was not consumed");
            require(succeeded(verify(*target)),
                    "collect target no longer verifies");
          });
  cases.run(
      "extension finite traversal uses coefficient stride and pointer scalars",
      [&] {
        std::string text = totalFiniteSource.str();
        for (size_t offset = 0; (offset = text.find("bls12-381.fr", offset)) !=
                                std::string::npos;) {
          text.replace(offset, StringRef("bls12-381.fr").size(),
                       "koala-bear.ext4-binomial3");
          offset += StringRef("koala-bear.ext4-binomial3").size();
        }
        auto source = close(text);
        auto target =
            take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
        unsigned reads = 0, products = 0;
        target->walk([&](evm::CheckedOp op) {
          if (op.opcode() == "vector.get") {
            ++reads;
            require(
                op->getNumResults() == 1 &&
                    op->getResult(0).getType().isInteger(64),
                "extension read did not return immutable coefficient pointer");
            auto type = op->getAttrOfType<TypeAttr>("value_type");
            require(type && cast<algebra::FieldVectorType>(type.getValue())
                                    .getDomain() == "koala-bear.ext4-binomial3",
                    "extension finite access lost exact nominal field");
          }
          if (op.opcode() == "field.mul")
            ++products;
        });
        require(reads == 1 && products == 1,
                "extension finite traversal lost field operation family");
      });
  cases.run(
      "finite products preserve eager ranges and boolean sequence elements",
      [&] {
        auto source = close(R"mlir(
!S = !data.sequence<i1>
module { "protocol.module"() ({
  "data.domain"() ({ ^entry(%xs:!S,%lower:ui64,%upper:ui64):
    %a = "data.domain_elements"(%xs) : (!S)->!data.domain<i1>
    %r = "data.domain_range"(%lower,%upper) : (ui64,ui64)->!data.domain<ui64>
    %product = "data.domain_product"(%a,%r) : (!data.domain<i1>,!data.domain<ui64>)->!data.domain<i1,ui64>
    %unused = "data.domain_range"(%upper,%lower) : (ui64,ui64)->!data.domain<ui64>
    "data.domain_yield"(%product) : (!data.domain<i1,ui64>)->()
  }) {sym_name="items",sym_visibility="private",function_type=(!S,ui64,ui64)->!data.domain<i1,ui64>} : ()->()
  func.func private @step(%state:i1,%item:i1,%index:ui64,%xs:!S,%lower:ui64,%upper:ui64)->i1 {
    %next = arith.xori %state,%item : i1
    func.return %next : i1
  }
  "protocol.func"() ({ ^entry(%xs:!S,%lower:ui64,%upper:ui64,%seed:i1):
    %r = "algebra.finite_fold"(%xs,%lower,%upper,%seed) {domain=@items,step=@step} : (!S,ui64,ui64,i1)->i1
    "protocol.return"(%r) : (i1)->()
  }) {sym_name="main",function_type=(!S,ui64,ui64,i1)->i1,roles=["V"],input_roles=[["V"],["V"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
)mlir");
        auto target =
            take(evm::lowerEndpoint(take(closeEndpoint(*source, "V")), {}));
        unsigned loops = 0, reads = 0, admission = 0, remainders = 0;
        target->walk([&](scf::ForOp loop) {
          ++loops;
          require(loop.getInitArgs().size() == 1 &&
                      loop.getInitArgs()[0].getType().isInteger(1),
                  "Boolean fold lost zero-trip seed");
        });
        target->walk([&](evm::CheckedOp op) {
          if (op.opcode() == "sequence.get") {
            ++reads;
            require(op->getResult(0).getType().isInteger(1),
                    "Boolean item widened");
          }
          if (op.opcode() == "range.admit") {
            ++admission;
            require(!op->getParentOfType<scf::ForOp>(),
                    "eager descriptor admission moved inside traversal");
          }
          if (op.opcode() == "index.mod")
            ++remainders;
        });
        require(loops == 1 && reads == 1 && admission >= 5 && remainders == 2,
                "product lost eager factors or last-factor-fastest indexing");
      });
  cases.run(
      "variant dispatch loads only the active payload after its tag branch",
      [&] {
        std::string text = R"zkc(
module choices;
type Sequence<T:Type+Copy+Drop> = builtin("sequence",T);
fn length<T:Type+Copy+Drop>(xs:Sequence<T>)->index = primitive("sequence.length");
enum Optional {None(),Some(Sequence<bool>)}
fn work(value:Optional)->bool {
  return match value {None()=>{false},Some(xs)=>{length(xs)==0}};
}
protocol Main roles(P,V)(value:Optional@V)->(ok:bool@V) {
  let ok @V =work(value); return(ok=ok);
}
proof Proof=Main{prover P;verifier V;public{value};accept ok;construction authored;}
)zkc";
        auto project = take(
            language::analyze(
                take(language::capture({{"choices", text, "choices.zkc"}})))
                .checkedProject());
        auto original = take(language::prepareOriginal(
            take(language::closeEntry(project, "choices::Proof"))));
        auto policy = take(language::proofPolicy(original));
        auto source = close(original.bytes());
        auto target = take(evm::lowerEndpoint(
            take(closeEndpoint(*source, policy.validator)), {}));
        unsigned payloads = 0, tags = 0;
        target->walk([&](evm::CheckedOp op) {
          if (op.opcode() == "variant.tag")
            ++tags;
          if (op.opcode() == "variant.get") {
            ++payloads;
            require(op->getParentOfType<scf::IfOp>() ||
                        op->getParentOfType<scf::IndexSwitchOp>(),
                    "inactive payload was loaded before dispatch");
            require(op->getNumResults() == 2,
                    "sequence payload lost complete lane tuple");
          }
        });
        require(tags == 1 && payloads == 1,
                "variant dispatch lost exact typed operations");
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
  constexpr StringLiteral boundaryText = R"mlir(
      module {
        func.func private @verify_endpoint(%generation:i64) -> (i1,i64) attributes {evm.entry,
          evm.logical_type=(!runtime.capability<transcript,"hash-chain.keccak256.bls12-381.fr64be/0">)->(i1,!runtime.capability<transcript,"hash-chain.keccak256.bls12-381.fr64be/0">),
          evm.output_ports=[0:i64]} {
          %accepted = arith.constant true
          func.return %accepted,%generation : i1,i64
        }
      })mlir";
  // Exporter tests use a formed original interface. Its private producer
  // inputs exercise output-type projection without supplying public rows.
  auto boundaryOriginal = [&](ModuleOp module) {
    func::FuncOp endpoint;
    for (auto function : module.getOps<func::FuncOp>())
      if (function->hasAttr("evm.entry"))
        endpoint = function;
    auto logical = cast<FunctionType>(
        endpoint->getAttrOfType<TypeAttr>("evm.logical_type").getValue());
    auto ports = endpoint->getAttrOfType<ArrayAttr>("evm.output_ports");
    unsigned count =
        ports.empty()
            ? 0
            : cast<IntegerAttr>(ports[ports.size() - 1]).getUInt() + 1;
    SmallVector<Type> results(count, IntegerType::get(&context, 1));
    for (auto [i, port] : enumerate(ports))
      results[cast<IntegerAttr>(port).getUInt()] = logical.getResult(i);
    SmallVector<Type> inputs;
    SmallVector<std::string> returned;
    for (Type type : results) {
      if (type.isInteger(1))
        returned.push_back("%ok");
      else {
        returned.push_back("%input" + std::to_string(inputs.size()));
        inputs.push_back(type);
      }
    }
    std::string source;
    raw_string_ostream out(source);
    out << "module { \"protocol.module\"() ({ \"protocol.func\"() ({ ^entry(";
    for (auto [i, type] : enumerate(inputs)) {
      if (i)
        out << ",";
      out << "%input" << i << ":" << type;
    }
    out << "): %ok = arith.constant true \"protocol.return\"(";
    interleaveComma(returned, out);
    out << ") : (";
    interleaveComma(results, out);
    out << ")->() }) {sym_name=\"independent\",function_type=(";
    interleaveComma(inputs, out);
    out << ")->(";
    interleaveComma(results, out);
    out << "),roles=[\"P\",\"V\"],input_roles=[";
    for (unsigned i = 0; i < inputs.size(); ++i) {
      if (i)
        out << ",";
      out << "[\"P\"]";
    }
    out << "],output_roles=[";
    for (unsigned i = 0; i < results.size(); ++i) {
      if (i)
        out << ",";
      out << "[\"P\"]";
    }
    out << "]} : ()->() }) {profile=#protocol.profile<protocol>} : ()->() }\n";
    return source;
  };
  auto boundary = [&](StringRef text, unsigned selected = 0,
                      bool managed = true) {
    auto module = parseSourceString<ModuleOp>(text, &context);
    require(bool(module), "invalid boundary test target");
    NativeProofPolicy policy;
    policy.acceptance = selected;
    policy.entry = "independent";
    policy.producer = "P";
    policy.validator = "V";
    if (managed)
      policy.suite = "hash-chain.keccak256.bls12-381.fr64be/0";
    json::Value descriptor = json::Array{"zkc.native-proof-descriptor/0",
                                         encodeNativeProofPolicy(policy),
                                         "binding-test",
                                         json::Array{},
                                         json::Array{},
                                         json::Array{},
                                         json::Array{},
                                         json::Array{},
                                         json::Array{}};
    return evm::exportYul(*module, boundaryOriginal(*module), descriptor,
                          policy, {});
  };
  cases.run("expanded copyable results precede selected acceptance", [&] {
    auto text = replaceFixture(boundaryText.str(), "-> (i1,i64)",
                               "-> (i64,i64,i1,i64)");
    text = replaceFixture(
        std::move(text), "->(i1,!runtime.capability",
        "->(!algebra.field_vector<\"bls12-381.fr\">,i1,!runtime.capability");
    text = replaceFixture(std::move(text), "evm.output_ports=[0:i64]",
                          "evm.output_ports=[0:i64,2:i64]");
    text = replaceFixture(
        std::move(text), "func.return %accepted,%generation : i1,i64",
        "func.return %generation,%generation,%accepted,%generation : "
        "i64,i64,i1,i64");
    take(boundary(text, 2));
  });
  cases.run("invocation checks logical lane expansion independently", [&] {
    auto text = replaceFixture(
        boundaryText.str(), "->(i1,!runtime.capability",
        "->(!algebra.field_vector<\"bls12-381.fr\">,i1,!runtime.capability");
    text = replaceFixture(std::move(text), "evm.output_ports=[0:i64]",
                          "evm.output_ports=[0:i64,1:i64]");
    refuses(boundary(text, 1), "evm.yul");
  });
  cases.run("invocation refuses unconsumed affine results", [&] {
    auto text =
        replaceFixture(boundaryText.str(), "-> (i1,i64)", "-> (i64,i1,i64)");
    text = replaceFixture(std::move(text), "->(i1,!runtime.capability",
                          "->(!runtime.scope,i1,!runtime.capability");
    text = replaceFixture(std::move(text), "evm.output_ports=[0:i64]",
                          "evm.output_ports=[0:i64,1:i64]");
    text = replaceFixture(
        std::move(text), "func.return %accepted,%generation : i1,i64",
        "func.return %generation,%accepted,%generation : i64,i1,i64");
    refuses(boundary(text, 1), "evm.yul");
  });
  cases.run("invocation refuses absent selected acceptance",
            [&] { refuses(boundary(boundaryText, 1), "evm.yul"); });
  cases.run("zero transcript signature needs no invented generation lane", [&] {
    take(boundary(R"mlir(module {
      func.func private @verify_endpoint() -> i1 attributes {
        evm.entry,evm.logical_type=()->i1,evm.output_ports=[0:i64]} {
        %ok = arith.constant true
        func.return %ok : i1
      }
    })mlir",
                  0, false));
  });
  cases.run("minimum calldata is a decode refusal below the resource ceiling",
            [&] {
              auto yul = take(boundary(boundaryText));
              require(StringRef(yul).contains(
                          "if lt(calldatasize(), 100) { evm_decode(7) }"),
                      "short ABI inputs retain the resource failure class");
              require(StringRef(yul).contains(
                          "if gt(calldatasize(), 262144) { evm_resource(10) }"),
                      "oversized calldata lost its resource refusal");
            });
  cases.run("static binding uses raw bytes and the exact original digest", [&] {
    auto yul = take(boundary(boundaryText));
    StringRef text(yul);
    require(
        text.contains(
            "datacopy(root, dataoffset(\"bytes_0\"), datasize(\"bytes_0\"))") &&
            !text.contains("evm_static") && !text.contains("Compressed"),
        "static byte copying retained compression machinery");
    auto source = parseSourceString<ModuleOp>(boundaryText, &context);
    auto originalBytes = boundaryOriginal(*source);
    auto digest =
        toHex(SHA256::hash(arrayRefFromStringRef(originalBytes)), true);
    require(text.contains(toHex(digest, true)) &&
                !text.contains(toHex(originalBytes, true)),
            "binding source is not the exact original SHA256 identity");
    require(text.contains("verbatim_1i_0o(hex\"50\", boundState)"),
            "invocation observation lost its final POP sink");
  });
  return cases.result();
}
