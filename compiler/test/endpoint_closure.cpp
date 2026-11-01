#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "support/NativeCases.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Transforms/EndpointClosure.h"
#include "zkc/Transforms/Stages.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral sourceText = R"mlir(
module {
 "protocol.module"() ({
   "protocol.func"() ({
   ^entry(%g: !algebra.group<"bls12-381.g1">, %x: !algebra.field<"bls12-381.fr">, %a: !algebra.field<"bls12-381.fr">, %b: !algebra.field<"bls12-381.fr">):
     %scaled = algebra.group_scale %g, %x : (!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">) -> !algebra.group<"bls12-381.g1">
     %ok = algebra.field_equal %a, %b : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
     "protocol.return"(%scaled, %ok) : (!algebra.group<"bls12-381.g1">, i1) -> ()
   }) {sym_name="main", function_type=(!algebra.group<"bls12-381.g1">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)->(!algebra.group<"bls12-381.g1">,i1), roles=["P","V"],
       input_roles=[["P"],["P"],["V"],["V"]], output_roles=[["P"],["V"]]} : () -> ()
 }) {profile=#protocol.profile<protocol>} : () -> ()
})mlir";
bool equivalent(Operation *a, Operation *b) {
  return OperationEquivalence::isEquivalentTo(
      a, b, OperationEquivalence::IgnoreLocations);
}
void accepted(Error e) {
  if (e)
    throw std::runtime_error(toString(std::move(e)));
}
void rejected(Error e, StringRef code) {
  require(bool(e), "expected refusal");
  auto message = toString(std::move(e));
  require(namesIdentifier(message, code), message);
}
unsigned groups(ModuleOp module) {
  unsigned count = 0;
  module.walk([&](Operation *op) {
    count += op->getName().getStringRef() == "algebra.group_scale";
  });
  return count;
}
func::FuncOp nestedEntry(ModuleOp module) {
  func::FuncOp result;
  module.walk([&](ModuleOp unit) {
    auto entry = mathematical::getComputationEntry(unit);
    if (entry && entry.getNumResults() == 1 &&
        entry.getResultTypes()[0].isInteger(1))
      result = entry;
  });
  require(bool(result), "missing boolean computation");
  return result;
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry, MLIRContext::Threading::DISABLED);
  context.loadAllAvailableDialects();
  registerCompilerPasses();
  registerCompilerPipelines();
  auto parse = [&] {
    auto module = parseSourceString<ModuleOp>(sourceText, &context);
    require(bool(module), "invalid source fixture");
    return module;
  };
  auto closed = [&] {
    auto module = parse();
    PassManager pm(&context);
    buildProjectionPipeline(pm, false);
    buildClosedExecutionPipeline(pm);
    require(succeeded(pm.run(*module)), "closed formation failed");
    return module;
  };
  cases.run("common construction and CPU registration are independent", [&] {
    require(!PassInfo::lookup("zkc-select-physical"),
            "common registered CPU selection");
    auto policy = parseNativeProofPolicy("{}");
    refuses(std::move(policy), "invalid-shape");
  });
  cases.run(
      "actual selected closure excludes producer mathematics and retains "
      "source metadata",
      [&] {
        auto module = closed();
        nestedEntry(*module).setSymVisibilityAttr(
            StringAttr::get(&context, "public"));
        auto before = OwningOpRef<ModuleOp>(cast<ModuleOp>(module->clone()));
        auto endpoint = take(closeEndpoint(*module, "V"));
        auto candidate = endpoint.candidateSnapshot();
        auto retained = endpoint.sourceSnapshot();
        require(equivalent(*module, *before) && equivalent(*retained, *before),
                "source changed");
        require(groups(*module) > 0 && groups(*candidate) == 0,
                "producer entered verifier inventory");
        unsigned metadata = 0, slicedMetadata = 0;
        retained->walk([&](protocol_ir::ProjectionOp) { ++metadata; });
        candidate->walk([&](protocol_ir::ProjectionOp) { ++slicedMetadata; });
        require(metadata == 1 && slicedMetadata == 0,
                "correspondence inventory boundary changed");
        accepted(checkEndpointClosure(*module, *candidate, "V"));
        auto producer = take(closeEndpoint(*module, "P"));
        require(groups(*producer.candidateSnapshot()) > 0,
                "reachable unsupported producer disappeared");
        refuses(closeEndpoint(*module, "missing"), "endpoint-role");
        refuses(closeEndpoint(*module, std::string(4097, 'V')),
                "endpoint-role");
        rejected(checkEndpointClosure(*module, {}, "V"), "endpoint-candidate");
        auto malformed = endpoint.candidateSnapshot();
        malformed->getBodyRegion().getBlocks().clear();
        rejected(checkEndpointClosure(*module, *malformed, "V"),
                 "endpoint-candidate");
        refuses(closeEndpoint(*malformed, "V"), "endpoint-source");
      });
  cases.run(
      "reachable unsupported verifier mathematics remains a target obligation",
      [&] {
        std::string verifierSource = sourceText.str();
        auto inputs = verifierSource.find("input_roles=[[\"P\"],[\"P\"]");
        require(inputs != std::string::npos, "fixture input roles absent");
        verifierSource.replace(inputs,
                               StringRef("input_roles=[[\"P\"],[\"P\"]").size(),
                               "input_roles=[[\"V\"],[\"V\"]");
        auto outputs = verifierSource.find("output_roles=[[\"P\"],[\"V\"]]");
        require(outputs != std::string::npos, "fixture output roles absent");
        verifierSource.replace(
            outputs, StringRef("output_roles=[[\"P\"],[\"V\"]]").size(),
            "output_roles=[[\"V\"],[\"V\"]]");
        auto module = parseSourceString<ModuleOp>(verifierSource, &context);
        require(bool(module), "verifier fixture did not form");
        PassManager pm(&context);
        buildProjectionPipeline(pm, false);
        buildClosedExecutionPipeline(pm);
        require(succeeded(pm.run(*module)),
                "verifier closure formation failed");
        auto endpoint = take(closeEndpoint(*module, "V"));
        require(groups(*endpoint.candidateSnapshot()) > 0,
                "reachable unsupported verifier helper was pruned");
      });
  cases.run(
      "nested references resolve exact leaves and prune unused siblings", [&] {
        auto module = closed();
        auto entry = nestedEntry(*module);
        auto unit = entry->getParentOfType<ModuleOp>();
        OpBuilder builder(&context);
        builder.setInsertionPointToEnd(unit.getBody());
        auto leaf = func::FuncOp::create(
            builder, entry.getLoc(), "leaf",
            builder.getFunctionType({builder.getI1Type()},
                                    {builder.getI1Type()}));
        leaf.setPrivate();
        builder.setInsertionPointToEnd(leaf.addEntryBlock());
        func::ReturnOp::create(builder, leaf.getLoc(), leaf.getArgument(0));
        auto dead = cast<func::FuncOp>(leaf->clone());
        dead.setSymName("dead");
        unit.getBody()->push_back(dead);
        auto returned = cast<func::ReturnOp>(entry.getBody().back().back());
        builder.setInsertionPoint(returned);
        auto call = func::CallOp::create(builder, returned.getLoc(), leaf,
                                         returned.getOperands());
        returned->setOperands(call.getResults());
        require(succeeded(admitStage(*module)),
                "nested source was not admitted");
        auto endpoint = take(closeEndpoint(*module, "V"));
        auto candidate = endpoint.candidateSnapshot();
        auto selected = nestedEntry(*candidate)->getParentOfType<ModuleOp>();
        require(SymbolTable::lookupSymbolIn(selected, "leaf") &&
                    !SymbolTable::lookupSymbolIn(selected, "dead"),
                "incorrect nested closure");
        accepted(checkEndpointClosure(*module, *candidate, "V"));
        auto changed =
            cast<func::FuncOp>(SymbolTable::lookupSymbolIn(selected, "leaf"));
        auto terminator = cast<func::ReturnOp>(changed.front().back());
        builder.setInsertionPoint(terminator);
        auto value =
            arith::ConstantIntOp::create(builder, changed.getLoc(), 0, 1);
        terminator->setOperands(value.getResult());
        rejected(checkEndpointClosure(*module, *candidate, "V"),
                 "endpoint-correspondence");
      });
  cases.run("stale candidates and metadata mutations refuse", [&] {
    auto module = closed();
    auto endpoint = take(closeEndpoint(*module, "V"));
    auto candidate = endpoint.candidateSnapshot();
    nestedEntry(*candidate)
        .setSymVisibilityAttr(StringAttr::get(&context, "public"));
    rejected(checkEndpointClosure(*module, *candidate, "V"),
             "endpoint-correspondence");
    candidate = endpoint.candidateSnapshot();
    (*candidate)->setAttr("test.changed", UnitAttr::get(&context));
    rejected(checkEndpointClosure(*module, *candidate, "V"),
             "endpoint-correspondence");
    candidate = endpoint.candidateSnapshot();
    nestedEntry(*module).setSymVisibilityAttr(
        StringAttr::get(&context, "public"));
    rejected(checkEndpointClosure(*module, *candidate, "V"),
             "endpoint-correspondence");
    require(equivalent(*endpoint.candidateSnapshot(), *candidate),
            "inspection mutated owner");
  });
  cases.run("direct and textual closed formation and endpoint selection agree",
            [&] {
              auto direct = parse(), textual = parse();
              PassManager a(&context), b(&context);
              buildProjectionPipeline(a, false);
              buildClosedExecutionPipeline(a);
              a.addPass(createSelectEndpointPass("V"));
              require(succeeded(parsePassPipeline(
                          "zkc-projection-pipeline{simplify=false},zkc-closed-"
                          "execution-pipeline,zkc-select-endpoint{role=V}",
                          b)),
                      "textual pipeline unavailable");
              require(succeeded(a.run(*direct)) && succeeded(b.run(*textual)),
                      "pipeline failed");
              require(equivalent(*direct, *textual),
                      "direct/textual subjects differ");
              refuses(closeEndpoint(*parse(), "V"), "endpoint-source");
            });
  return cases.result();
}
