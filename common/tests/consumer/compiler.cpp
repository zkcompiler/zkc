#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Language.h"
#include "zkc/Compiler/NativeProof.h"
#include "zkc/Compiler/Passes.h"
#include "zkc/Compiler/Pipelines.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Transforms/EndpointClosure.h"
#include "zkc/Transforms/Stages.h"
#include "llvm/Support/raw_ostream.h"
int main() {
  auto project = zkc::language::capture({{"m", R"(module m;
    protocol Echo roles(P)(x:bool@P)->(r:bool@P){return(r=x);}
    entry fn Demo(inputs:Echo::Inputs){return Echo::run(inputs);}
    protocol Send roles(P,V)(x:bool@P)->(accepted:bool@V){
      let received=send P->V(x);return(accepted=received);
    }
    proof Proof=Send{prover P;verifier V;public{};accept accepted;construction authored;}
    domain Q=field("koala-bear.ext4-binomial3");
    protocol Queries roles(P,V)(coins:Random<Q>@V)->(ok:bool@V){
      #[site(first)] let first=coins.indices(16,2);
      let first_received=send V->P(first);
      #[site(second)] let second=coins.indices(16,2);
      let second_received=send V->P(second);
      return true;
    }
    proof Gates=Queries{prover P;verifier V;public{};accept ok;
      construction fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",coins);
      gate second bits 0;
      gate first bits 3;
    })",
                                          "common.zkc"}});
  if (!project) {
    llvm::errs() << llvm::toString(project.takeError());
    return 1;
  }
  auto checked = zkc::language::analyze(*project).checkedProject();
  if (!checked) {
    llvm::errs() << llvm::toString(checked.takeError());
    return 2;
  }
  auto entry = zkc::language::closeEntry(*checked, "m::Demo");
  if (!entry) {
    llvm::errs() << llvm::toString(entry.takeError());
    return 3;
  }
  auto original = zkc::language::prepareOriginal(*entry);
  if (!original) {
    llvm::errs() << llvm::toString(original.takeError());
    return 4;
  }
  auto admitted = zkc::language::admitOriginal(*entry, original->bytes(),
                                               original->interfaceJson());
  if (!admitted) {
    llvm::errs() << llvm::toString(admitted.takeError());
    return 5;
  }
  auto policy = zkc::parseNativeProofPolicy("{}");
  if (policy)
    return 6;
  llvm::consumeError(policy.takeError());
  zkc::registerCompilerPasses();
  zkc::registerCompilerPipelines();
  if (original->bytes() != admitted->bytes() ||
      original->identity() != admitted->identity())
    return 7;
  auto runPolicy = zkc::language::proofPolicy(*original);
  if (runPolicy)
    return 8;
  llvm::consumeError(runPolicy.takeError());
  auto proofEntry = zkc::language::closeEntry(*checked, "m::Proof");
  if (!proofEntry) {
    llvm::errs() << llvm::toString(proofEntry.takeError());
    return 9;
  }
  auto proof = zkc::language::prepareOriginal(*proofEntry);
  if (!proof) {
    llvm::errs() << llvm::toString(proof.takeError());
    return 10;
  }
  auto selection = zkc::language::proofPolicy(*proof);
  if (!selection) {
    llvm::errs() << llvm::toString(selection.takeError());
    return 11;
  }
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  auto source =
      mlir::parseSourceString<mlir::ModuleOp>(proof->bytes(), &context);
  if (!source)
    return 12;
  auto built = zkc::constructNativeProof(*source, *selection);
  if (!built) {
    llvm::errs() << llvm::toString(built.takeError());
    return 13;
  }
  if (auto error = zkc::checkNativeProof(*source, *built->module, *selection)) {
    llvm::errs() << llvm::toString(std::move(error));
    return 14;
  }
  auto pair = zkc::exportConstructedPair(*source, *built->module,
                                         proof->bytes(), *selection);
  if (!pair) {
    llvm::errs() << llvm::toString(pair.takeError());
    return 15;
  }
  mlir::PassManager pipeline(&context);
  zkc::buildClosedExecutionPipeline(pipeline);
  if (mlir::failed(pipeline.run(*built->module)))
    return 16;
  auto endpoint = zkc::closeEndpoint(*built->module, selection->validator);
  if (!endpoint) {
    llvm::errs() << llvm::toString(endpoint.takeError());
    return 17;
  }
  auto candidate = endpoint->candidateSnapshot();
  if (auto error = zkc::checkEndpointClosure(*built->module, *candidate,
                                             selection->validator)) {
    llvm::errs() << llvm::toString(std::move(error));
    return 18;
  }
  auto gatedEntry = zkc::language::closeEntry(*checked, "m::Gates");
  if (!gatedEntry) {
    llvm::errs() << llvm::toString(gatedEntry.takeError());
    return 19;
  }
  auto gated = zkc::language::prepareOriginal(*gatedEntry);
  if (!gated) {
    llvm::errs() << llvm::toString(gated.takeError());
    return 20;
  }
  auto gates = zkc::language::proofPolicy(*gated);
  if (!gates) {
    llvm::errs() << llvm::toString(gates.takeError());
    return 21;
  }
  // Source policy is common compiler data, before either target is linked.
  // Explicit zero remains a selected request, in source occurrence order.
  if (!gates->draws.empty() || gates->gates.size() != 2 ||
      gates->gates[0] !=
          std::pair(zkc::language::nativeSiteName("first", 0), 3u) ||
      gates->gates[1] !=
          std::pair(zkc::language::nativeSiteName("second", 0), 0u))
    return 22;
  return 0;
}
