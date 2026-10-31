#include "../lib/Transforms/PreparedProtocol.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Pass/PassRegistry.h"
#include "mlir/Transforms/Passes.h"
#include "support/NativeCases.h"
#include "support/ScopedFixture.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Stages.h"
#include "llvm/ADT/ScopeExit.h"
#include <mutex>

using namespace mlir;
using namespace zkc;
using namespace zkc::test;
namespace {
constexpr StringLiteral source = R"mlir(
module {
 "protocol.module"() ({
   func.func private @unused(%x: i1) -> i1 { return %x : i1 }
   "protocol.func"() ({ ^entry(%x: i1):
     "protocol.return"(%x) : (i1) -> ()
   }) {sym_name="main", function_type=(i1)->i1, roles=["P"],
       input_roles=[["P"]], output_roles=[["P"]]} : () -> ()
 }) {profile=#protocol.profile<protocol>} : () -> ()
})mlir";
std::string printed(Operation *op) {
  std::string value;
  llvm::raw_string_ostream stream(value);
  op->print(stream);
  return value;
}
protocol_ir::ProtocolModuleOp unit(ModuleOp module) {
  return *module.getOps<protocol_ir::ProtocolModuleOp>().begin();
}
void dormantCast(ModuleOp module) {
  auto function =
      *unit(module).getBody().front().getOps<func::FuncOp>().begin();
  OpBuilder builder(&function.getBody().front(),
                    function.getBody().front().begin());
  UnrealizedConversionCastOp::create(builder, function.getLoc(),
                                     TypeRange{builder.getI1Type()},
                                     ValueRange{function.getArgument(0)});
}
} // namespace
int main() {
  registerCompilerPasses();
  registerCompilerPipelines();
  registerTransformsPasses();
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  std::string messages;
  std::mutex messageMutex;
  ScopedDiagnosticHandler diagnostics(&context, [&](Diagnostic &diagnostic) {
    std::lock_guard<std::mutex> lock(messageMutex);
    llvm::raw_string_ostream out(messages);
    diagnostic.print(out);
    out << '\n';
    return success();
  });
  auto parse = [&] {
    auto module = parseSourceString<ModuleOp>(source, &context);
    require(bool(module), "stage fixture did not form");
    return module;
  };
  Cases cases;
  cases.run("structural preflight precedes recursive verification", [&] {
    auto root = ModuleOp::create(UnknownLoc::get(&context));
    SmallVector<ModuleOp> modules{root};
    auto cleanup = llvm::scope_exit([&] {
      for (auto module : llvm::reverse(modules))
        module.erase();
    });
    for (unsigned i = 0; i < 10000; ++i) {
      auto nested = ModuleOp::create(root.getLoc());
      modules.back().getBody()->push_back(nested);
      modules.push_back(nested);
    }
    messages.clear();
    require(failed(admitStage(root)), "unbounded native nesting admitted");
    require(namesIdentifier(messages, "stage-admission-limit"), messages);
  });
  cases.run("standalone computation units undergo complete admission", [&] {
    auto module = parseSourceString<ModuleOp>(R"mlir(
      module @unit attributes {exec.computation} {
        func.func @main(%x: i1) -> i1 { return %x : i1 }
        func.func private @unused(%x: i1) -> i1 {
          %unused = builtin.unrealized_conversion_cast %x : i1 to i1
          return %x : i1
        }
      })mlir",
                                              &context);
    require(bool(module), "standalone computation did not form");
    messages.clear();
    require(failed(admitStage(*module)), "standalone dormant cast admitted");
    require(namesIdentifier(messages, "mathematical-formation"), messages);
  });
  cases.run("admission is read only and does not stamp mutable IR", [&] {
    auto module = parse();
    auto original = printed(*module);
    require(succeeded(admitStage(*module)), messages);
    require(printed(*module) == original, "admission changed IR");
    require(succeeded(admitStage(unit(*module))), messages);
  });
  cases.run("structural verification does not admit dormant vocabulary", [&] {
    auto module = parse();
    dormantCast(*module);
    require(succeeded(verify(*module)), "cast broke structural verification");
    auto original = printed(*module);
    messages.clear();
    require(failed(admitStage(*module)), "unresolved dormant cast admitted");
    require(namesIdentifier(messages, "mathematical-formation"), messages);
    require(printed(*module) == original, "failed admission changed IR");
  });
  cases.run("admission runs before generic symbol elimination", [&] {
    auto module = parse();
    dormantCast(*module);
    PassManager passes(&context);
    passes.addPass(createAdmitStagePass());
    passes.addPass(createSymbolDCEPass());
    require(failed(passes.run(*module)), "generic pass erased invalid subject");
    require(!unit(*module).getBody().front().getOps<func::FuncOp>().empty(),
            "failed stage ran symbol elimination");
  });
  cases.run("fresh direct admission sees sibling body mutation", [&] {
    auto module = parse();
    require(succeeded(admitStage(*module)), messages);
    dormantCast(*module);
    require(failed(admitStage(*module)),
            "previous admission survived mutation");
  });
  cases.run("nested admission owns every sibling declaration", [&] {
    auto module = parse();
    PassManager passes(&context);
    passes.nest<protocol_ir::ProtocolModuleOp>().addPass(
        createAdmitStagePass());
    require(succeeded(passes.run(*module)), messages);
    dormantCast(*module);
    require(failed(passes.run(*module)), "nested admission missed mutation");
  });
  cases.run("a function is not an admission owner", [&] {
    auto module = parse();
    auto function =
        *unit(*module).getBody().front().getOps<func::FuncOp>().begin();
    messages.clear();
    require(failed(admitStage(function)),
            "function admitted a sibling closure");
    require(namesIdentifier(messages, "stage-admission-owner"), messages);
  });
  cases.run("prepared stages retain their original outside mutable IR", [&] {
    auto module = parse();
    auto before = printed(*module);
    MathematicalSelectionPolicy policy{false, true, true, false,
                                       NumericalExpressionMode::VectorOnly};
    auto prepared = mathematical::PreparedProtocol::prepare(*module, policy);
    require(bool(prepared), messages);
    dormantCast(*module);
    auto original = prepared->originalSnapshot();
    require(original && printed(*original) == before,
            "prepared original aliases caller mutations");
    auto candidate = std::move(*prepared).project(false);
    require(candidate && succeeded(admitStage(*candidate)), messages);
  });
  cases.run("nondefault selection matches named and production pipelines", [&] {
    auto direct = parse(), textual = parse();
    MathematicalSelectionPolicy policy{false, true, true, false,
                                       NumericalExpressionMode::VectorOnly};
    PassManager first(&context), second(&context);
    buildProjectionPipeline(first, false, policy);
    buildClosedExecutionPipeline(first, false, false, policy);
    PhysicalPipelineOptions physical;
    physical.mathematics = policy;
    physical.releaseStorage = true;
    buildPhysicalPipeline(first, physical);
    require(succeeded(parsePassPipeline(
                "zkc-participant-pipeline{simplify=false "
                "optimize-finite=false fuse-vector-reductions=true "
                "fuse-collect-fold=true calculation-batching=false "
                "numerical-expressions=vector-only release-storage=true}",
                second)),
            "named pipeline did not parse");
    require(succeeded(first.run(*direct)), messages);
    require(succeeded(second.run(*textual)), messages);
    require(OperationEquivalence::isEquivalentTo(
                *direct, *textual, OperationEquivalence::IgnoreLocations),
            "named and production routes differ");
  });
  cases.run("physical textual descriptor refuses before mutation", [&] {
    auto module = parse();
    PassManager prepare(&context);
    buildProjectionPipeline(prepare);
    buildExecutionPipeline(prepare);
    require(succeeded(prepare.run(*module)), messages);
    auto before = printed(*module);
    PassManager select(&context);
    messages.clear();
    llvm::raw_string_ostream errors(messages);
    require(failed(parsePassPipeline(
                "zkc-physical-pipeline{cpu-target=invalid}", select, errors)),
            "invalid target descriptor accepted");
    // LLVM's option parser writes its specific refusal to stderr. The
    // pipeline callback separately reports construction failure here.
    require(messages.find("failed to add") != std::string::npos, messages);
    require(printed(*module) == before, "invalid target mutated IR");
  });
  cases.run(
      "typed physical intent survives textual reproduction and pass clones",
      [&] {
        messages.clear();
        auto text = scopedFixture(
            R"mlir("runtime.binding"() {sym_name="add",contract="field.add",
          arguments=["bls12-381.fr"],implementation="",
          function_type=(!runtime.scope,!algebra.field<"bls12-381.fr">,
                         !algebra.field<"bls12-381.fr">)->
                         !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->())mlir",
            "%a:!algebra.field<\"bls12-381.fr\">,%b:!algebra.field<\"bls12-381."
            "fr\">",
            "%a,%b",
            "!algebra.field<\"bls12-381.fr\">,!algebra.field<\"bls12-381.fr\">",
            "!algebra.field<\"bls12-381.fr\">",
            scopedApply("add", "sum", "%a,%b",
                        "!algebra.field<\"bls12-381.fr\">,!algebra.field<"
                        "\"bls12-381.fr\">",
                        "%sum", "!algebra.field<\"bls12-381.fr\">") +
                scopedReturn("%sum", "!algebra.field<\"bls12-381.fr\">"),
            2);
        auto source = take(executableFixture(text, context));
        PhysicalPipelineOptions options;
        options.selections = {{"add", "arkworks/field.add"}};
        options.functionPorts = {
            {"Work", false, 0, "field:bls12-381.fr@arkworks.fr/0"}};
        options.cpuTarget = take(target::CpuTarget::parse(
            R"({"format":"zkc.cpu-target/0","providers":["arkworks","blst"]})"));
        options.mathematics.finiteBulk = false;
        options.mathematics.numericalExpressions =
            NumericalExpressionMode::VectorOnly;
        PassManager direct(&context, ModuleOp::getOperationName());
        PassManager reproduced(&context, ModuleOp::getOperationName());
        buildPhysicalPipeline(direct.nest<ModuleOp>(), options);
        std::string pipeline;
        llvm::raw_string_ostream out(pipeline);
        direct.printAsTextualPipeline(out);
        StringRef body(pipeline);
        require(body.consume_front("builtin.module(") && body.consume_back(")"),
                "unexpected pipeline root: " + pipeline);
        require(succeeded(parsePassPipeline(body, reproduced)), pipeline);
        OwningOpRef<ModuleOp> first(ModuleOp::create(source->getLoc()));
        for (unsigned i = 0; i < 4; ++i)
          first->getBody()->push_back(source->clone());
        OwningOpRef<ModuleOp> second(cast<ModuleOp>(first->clone()));
        require(succeeded(direct.run(*first)), messages);
        require(succeeded(reproduced.run(*second)), messages);
        require(OperationEquivalence::isEquivalentTo(
                    *first, *second, OperationEquivalence::IgnoreLocations),
                "pass serialization or threaded cloning lost selected intent");
        unsigned pins = 0;
        first->walk([&](runtime::BindingOp binding) {
          if (binding.getSymName() == "add") {
            ++pins;
            require(binding.getImplementation() == "arkworks/field.add",
                    "selected implementation was lost");
          }
        });
        require(pins == 4, "nested pipelines skipped their subjects");
      });
  cases.run("pipeline selections reject duplicate and unknown option shapes", [&] {
    refuses(target::parseImplementationSelections(R"([["x","a"],["x","b"]])"),
            "binding-selection-option");
    refuses(
        target::parseFunctionPortSelections(
            R"([{"function":"f","output":false,"port":0,"type":"bool@native.bool/0","extra":0}])"),
        "binding-selection-option");
    refuses(
        target::parseFunctionPortSelections(
            R"([{"function":"f","output":false,"port":4294967296,"type":"bool@native.bool/0"}])"),
        "binding-selection-option");
  });
  return cases.result();
}
