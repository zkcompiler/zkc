#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Support/Json.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
using namespace llvm;
using namespace mlir;
using namespace zkc;
void require(bool ok, StringRef detail) {
  if (!ok) {
    errs() << detail << '\n';
    std::exit(1);
  }
}
std::string print(ModuleOp module) {
  std::string text;
  raw_string_ostream stream(text);
  module.print(stream);
  return text;
}
int main(int argc, char **argv) {
  require(argc == 2, "fixture argument");
  DialectRegistry registry;
  registerDialects(registry);
  MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto source = parseSourceFile<ModuleOp>(argv[1], &context);
  require(bool(source), "source parse");
  auto original = print(*source);
  auto policy = parseNativeProofPolicy(
      R"(["zkc.native-proof-policy/5", "main", "Alice", "Bob", "0", "merlin3.bls12-381.fr64be/1", "4", ["0", "2"], [["draw_challenge", "challenge"]]])");
  if (!policy) {
    errs() << toString(policy.takeError());
    return 1;
  }
  for (const char *suite : {"merlin3.bls12-381.fr64be/1",
                            "spongefish0.7.4.keccak.bls12-381.fr64be/1"}) {
    policy->suite = suite;
    auto built = constructNativeProof(*source, *policy);
    if (!built) {
      errs() << toString(built.takeError());
      return 1;
    }
    if (auto e = checkNativeProof(*source, *built->module, *policy)) {
      errs() << toString(std::move(e));
      return 1;
    }
    require(print(*source) == original, "constructor mutated source");
    bool changed = false;
    built->module->walk([&](Operation *op) {
      if (!changed && op->getName().getStringRef() == "algebra.field_add") {
        op->setOperand(0, op->getOperand(1));
        changed = true;
      }
    });
    require(changed, "mutation reached actual SSA operand");
    auto refusal = checkNativeProof(*source, *built->module, *policy);
    require(bool(refusal), "changed arithmetic accepted");
    consumeError(std::move(refusal));
    built = constructNativeProof(*source, *policy);
    require(bool(built), "reconstruct");
    PassManager passes(&context);
    passes.addPass(protocol::createSimplifyParticipantPass());
    passes.addPass(protocol::createEliminatePolynomialsPass());
    passes.addPass(protocol::createLowerMathPass());
    passes.addPass(protocol::createSelectPhysicalPass());
    require(succeeded(passes.run(*built->module)), "shared physical lowering");
    auto exported = protocol::exportModule(*built->module);
    if (!exported) {
      errs() << toString(exported.takeError());
      return 1;
    }
    outs() << printJson(*exported) << '\n';
  }
  policy->publicInputs.pop_back();
  auto rejected = constructNativeProof(*source, *policy);
  require(!rejected, "missing public binding accepted");
  consumeError(rejected.takeError());
}
