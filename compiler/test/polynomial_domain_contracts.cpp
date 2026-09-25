#include "zkc/Analysis/PolynomialDomains.h"
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Operations.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace zkc;
namespace {
void require(bool condition, llvm::StringRef message) {
  if (!condition) {
    llvm::errs() << message << '\n';
    std::exit(1);
  }
}
} // namespace
int main() {
  unsigned cosets = 0;
  for (const auto &kernel : protocol::kernels()) {
    if (auto facet = kernel.contracts.coset) {
      ++cosets;
      require(facet->shiftInput < kernel.inputs.size() &&
                  kernel.inputs[facet->shiftInput] == "field",
              "coset shift port");
      require(facet->sizeInput < kernel.inputs.size() &&
                  kernel.inputs[facet->sizeInput] ==
                      (facet->sizeIsLength ? "vector" : "index"),
              "coset size/length port");
      require(!facet->vectorOutput ||
                  (*facet->vectorOutput < kernel.outputs.size() &&
                   kernel.outputs[*facet->vectorOutput] == "vector"),
              "coset vector result port");
      require(!facet->foldedOutput ||
                  (facet->sizeIsLength && facet->vectorOutput),
              "fold must transform a vector domain");
    }
    if (auto facet = kernel.contracts.domainValue) {
      require(facet->output < kernel.outputs.size(), "exact result port");
      if (facet->rule != protocol::DomainValueRule::Constant)
        require(facet->input < kernel.inputs.size(), "exact input port");
      if (facet->rule == protocol::DomainValueRule::Divide ||
          facet->rule == protocol::DomainValueRule::Multiply)
        require(facet->otherInput < kernel.inputs.size(), "exact second port");
    }
  }
  require(cosets == 6, "expected installed coset coverage");
  require(!protocol::operationContracts("poly.future") &&
              !protocol::operationContracts("poly.fold")->coset &&
              !protocol::operationContracts("poly.univariate_evaluate")->coset,
          "unrelated polynomials do not acquire coset facts");
  require(!protocol::cosetConvention("bls12-381.fr") &&
              !protocol::cosetConvention("uninstalled"),
          "field alone does not install a root convention");
  auto *base = protocol::cosetConvention("koala-bear");
  auto *extension = protocol::cosetConvention("koala-bear.ext8-binomial3");
  require(base && extension && base->identity == extension->identity &&
              base->maxLogSize == 24 && base->rootField == "koala-bear",
          "explicit base-root embedding convention");
  auto *bn254 = protocol::cosetConvention("bn254.fr");
  require(bn254 && bn254->maxLogSize == 28 && bn254->rootField == "bn254.fr" &&
              bn254->identity != base->identity &&
              bn254->maximalRoot ==
                  "19103219067921713944291392827692070036145651957329286315305642004821462161904",
          "BN254 convention pins arkworks' generator-5 two-adic root");
  for (const auto &op : protocol::boundOperationContracts()) {
    if (op.name != "poly.even_odd_fold")
      continue;
    bool twoAdic = false, odd = false;
    for (const auto &r : op.signature.requirements) {
      twoAdic |= r.relation == "TwoAdicField";
      odd |= r.relation == "CharacteristicNotTwo";
    }
    require(twoAdic && odd, "fold declares both independent requirements");
  }
  // Missing convention stays unknown even when all exact expressions agree.
  // The API permits conservative future installations without granting facts.
  PolynomialDomains r;
  r.terms = {{"value", "field:future", "s", {}}, {"value", "index", "n", {}}};
  PolynomialDomain d;
  d.field = "future";
  d.shift = 0;
  d.size = 1;
  r.domains = {d, d};
  auto c = comparePolynomialDomains(r, 0, 1);
  require(c.result == DomainComparison::Result::Unknown &&
              c.reasons ==
                  std::vector<std::string>{"root-convention-unavailable"},
          "missing convention is unknown");
  return 0;
}
