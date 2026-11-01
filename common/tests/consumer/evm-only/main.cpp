#include "zkc/Compiler/Evm.h"
#include "zkc/Target/Evm/Target.h"
#include "llvm/Support/raw_ostream.h"

int main() {
  auto project = zkc::language::capture({{"numeric", R"(
module numeric;
domain Fr = field("bls12-381.fr");
protocol Product roles(P,V)(a:Fr@V,b:Fr@V,c:Fr@V,
    challenges:Random<Fr>@V)->(accepted:bool@V){
  let challenge=challenges.draw();
  let delivered=send V->P(challenge);
  return(accepted=a*b==c);
}
proof Proof=Product{
  prover P;verifier V;public{a,b,c};accept accepted;
  construction fiat_shamir("hash-chain.keccak256.bls12-381.fr64be/0", challenges);
})",
                                          "numeric.zkc"}});
  if (!project) {
    llvm::errs() << llvm::toString(project.takeError());
    return 1;
  }
  auto checked = zkc::language::analyze(*project).checkedProject();
  if (!checked) {
    llvm::errs() << llvm::toString(checked.takeError());
    return 2;
  }
  auto entry = zkc::language::closeEntry(*checked, "numeric::Proof");
  if (!entry) {
    llvm::errs() << llvm::toString(entry.takeError());
    return 3;
  }
  auto original = zkc::language::prepareOriginal(*entry);
  if (!original) {
    llvm::errs() << llvm::toString(original.takeError());
    return 4;
  }
  auto compiled = zkc::compileEvmEntry(*original);
  if (!compiled) {
    llvm::errs() << llvm::toString(compiled.takeError());
    return 5;
  }
  auto target = compiled->targetSnapshot();
  return mlir::failed(zkc::evm::checkTarget(*target)) ||
         compiled->yul().empty();
}
