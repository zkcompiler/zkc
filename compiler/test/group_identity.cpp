#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "support/NativeCases.h"
#include "support/ProtocolDeployment.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Contracts/Mathematical.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Kernel.h"
#include "zkc/Transforms/Mathematical.h"
#include "zkc/Transforms/Passes.h"
using namespace mlir;
using namespace llvm;
using namespace zkc;
using namespace zkc::test;
namespace {
Expected<language::CheckedProject> check(StringRef body) {
  return language::analyze(
             take(language::capture({{"sample", ("module sample;" + body).str(),
                                      "identity.zkc"}})))
      .checkedProject();
}
void run(ModuleOp module, std::unique_ptr<Pass> pass) {
  PassManager manager(module.getContext());
  manager.addPass(std::move(pass));
  require(succeeded(manager.run(module)), "fixture pass failed");
}
} // namespace
int main() {
  Cases cases;
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  for (StringRef group : {"ristretto255.group", "bls12-381.g1", "bls12-381.g2",
                          "bls12-381.gt", "bn254.g1", "bn254.g2", "bn254.gt"}) {
    for (bool primitive : {false, true})
      cases.run("source identity and realization: " + group, [&] {
        auto source =
            "domain G=group(\"" + group.str() + R"(");
          math fn zero<T:Group>()->T where zkc::curve::ScalarAction(T))" +
            (primitive ? "=primitive(\"curve.identity\");"
                       : "{return intrinsic<T>(\"curve.identity\");}") +
            R"(
          protocol Run roles(P,V)()->(z:G@(P,V)){return(z=zero<G>());}
          run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
        )";
        auto original = take(
            language::prepareOriginal(take(zkc::test::closeProtocolDeployment(
                take(check(source)), "sample::Demo"))));
        require(original.bytes().contains("algebra.group_identity"),
                "source identity did not reach total Algebra");
        for (bool simplify : {false, true})
          take(language::compileEntry(original, {simplify, false}));
        auto parsed = parseSourceString<ModuleOp>(original.bytes(), &context);
        require(bool(parsed), "cannot read original");
        unsigned identities = 0;
        parsed->walk([&](algebra::GroupIdentityOp op) {
          ++identities;
          auto meaning = cast<MathematicalOpInterface>(op.getOperation());
          require(meaning.getMathematicalIdentity() ==
                          MathematicalIdentity::GroupIdentity &&
                      meaning.getOperandDependencies(0).empty() &&
                      op->getNumOperands() == 0,
                  "identity must have no operand dependencies");
          SmallVector<MemoryEffects::EffectInstance> effects;
          cast<MemoryEffectOpInterface>(op.getOperation()).getEffects(effects);
          require(effects.empty(), "mathematical identity has effects");
        });
        require(identities > 0, "missing identity");
      });
  }
  for (StringRef expression :
       {"intrinsic(\"curve.identity\")", "intrinsic<F>(\"curve.identity\")",
        "intrinsic<G>(\"curve.identity\", x)",
        "intrinsic<G>(\"curve.identity\";\"0\")",
        "intrinsic<G,G>(\"curve.identity\")"})
    cases.run("malformed nullary signature: " + expression, [&] {
      refuses(check("domain G=group(\"bn254.g1\");domain F=field(\"bn254.fr\");"
                    "math fn bad(x:G)->G{return " +
                    expression.str() + ";}"),
              "source.intrinsic");
    });
  cases.run("generic Group alone grants no ScalarAction", [&] {
    refuses(check(R"(math fn zero<G:Group>()->G where () {
      return intrinsic<G>("curve.identity");})"),
            "source.intrinsic");
  });
  cases.run("scalar action belongs to the exact group", [&] {
    refuses(check(R"(math fn zero<G:Group,H:Group>()->G
      where zkc::curve::ScalarAction(H) {
        return intrinsic<G>("curve.identity");})"),
            "source.intrinsic");
  });
  cases.run("ordinary functions use ordered realization", [&] {
    refuses(check(R"(domain G=group("bn254.g1");
      fn bad()->G{return intrinsic<G>("curve.identity");})"),
            "source.mode");
  });
  cases.run("independent declaration signature", [&] {
    const auto *intrinsic = mathematicalIntrinsic("curve.identity");
    require(intrinsic &&
                intrinsic->identity == MathematicalIdentity::GroupIdentity,
            "missing mathematical registry identity");
    bool found = false;
    for (const auto &op : protocol::executableOperationContracts()) {
      if (op.name != "curve.identity")
        continue;
      found = true;
      const auto &s = op.signature;
      require(s.scope.sorts == std::vector<std::string>{"Group", "Field"} &&
                  s.inputs.empty() && s.outputs.size() == 1 &&
                  s.outputs[0].constructor == "group" &&
                  s.outputs[0].arguments == std::vector<unsigned>{0} &&
                  s.requirements ==
                      std::vector<requirements::Predicate>{
                          requirements::Predicate::holds("ScalarAction", {0})},
              "nullary signature or requirements differ");
    }
    require(found, "missing native contract");
  });
  auto original =
      take(language::prepareOriginal(take(zkc::test::closeProtocolDeployment(
          take(check(R"(domain G=group("bn254.g1");
        math fn zero()->G{return intrinsic<G>("curve.identity");}
        protocol Run roles(P)()->(z:G@P){return(z=zero());}run Demo(inputs: Run::Inputs) { return Run::run(inputs); })")),
          "sample::Demo"))));
  auto projected = parseSourceString<ModuleOp>(original.bytes(), &context);
  require(bool(projected), "mutation source");
  run(*projected, protocol::createProjectProtocolPass(false));
  auto lowered = OwningOpRef<ModuleOp>(cast<ModuleOp>((*projected)->clone()));
  run(*lowered, protocol::createLowerMathPass());
  auto logical = OwningOpRef<ModuleOp>(cast<ModuleOp>((*lowered)->clone()));
  run(*lowered, kernel::createLowerKernelsPass());
  cases.run("independent recipe accepts exact identity", [&] {
    require(succeeded(mathematical::verifyProjectionPreserved(*projected,
                                                              *logical)) &&
                succeeded(kernel::verifyKernelLowering(*logical, *lowered)),
            "identity recipe refused");
  });
  for (bool generator : {false, true})
    cases.run(
        generator ? "generator cannot realize identity"
                  : "another group cannot realize identity",
        [&] {
          auto candidate =
              OwningOpRef<ModuleOp>(cast<ModuleOp>((*lowered)->clone()));
          local::OperationBindingOp binding;
          algebra::CurveIdentityOp operation;
          candidate->walk([&](local::OperationBindingOp op) {
            if (op.getContract() == "curve.identity")
              binding = op;
          });
          candidate->walk([&](algebra::CurveIdentityOp op) { operation = op; });
          require(binding && operation, "missing native identity recipe");
          if (generator) {
            binding->setAttr("contract",
                             StringAttr::get(&context, "curve.generator"));
            OpBuilder builder(operation);
            OperationState state(operation.getLoc(),
                                 "algebra.exec.group_generator");
            state.addTypes(operation->getResultTypes());
            state.addAttributes(operation->getAttrs());
            auto *replacement = builder.create(state);
            operation->replaceAllUsesWith(replacement);
            operation.erase();
          } else {
            binding->setAttr(
                "arguments",
                ArrayAttr::get(&context,
                               {StringAttr::get(&context, "bn254.g2")}));
          }
          bool diagnostic = false;
          ScopedDiagnosticHandler expected(&context, [&](Diagnostic &d) {
            diagnostic |= namesIdentifier(
                d.str(), generator ? "kernel-lowering-correspondence"
                                   : "binding-operation-signature");
            return success();
          });
          if (generator) {
            require(succeeded(verify(*candidate)),
                    "generator mutation must retain formation");
            require(failed(kernel::verifyKernelLowering(*logical, *candidate)),
                    "generator realized identity");
          } else {
            require(failed(verify(*candidate)),
                    "wrong nominal group escaped signature admission");
          }
          require(diagnostic, "wrong mutation diagnostic");
        });
  return cases.result();
}
