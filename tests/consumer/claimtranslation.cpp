#include "mlir/IR/Builders.h"
#include "mlir/IR/Verifier.h"
#include "zkc/ClaimTranslation/Claims.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"

// Only Zkc::ClaimTranslation is linked: no frontend, transforms or compiler.
// The original source and independent caller contract remain mandatory.
int main() {
  auto json =
      zkc::parseJson(R"(["zkc.protocol/1",[["require","control.require",[],""]],
    [["function","Check",[["ok","bool"]],["bool"],
      [["op","guard","require",[],["ok"],[]],["return",["ok"]]],["Check",[]]]],
    [["protocol","Checked",["V"],[],[["ok","V","bool"]],[["V","bool"]],[],
      [["local","call","V","Check",["ok"],["accepted"]],["return",["accepted"]]]]],
    [["instance","run","Checked",[],[],[["V","Validator"]]]],[["entry","main","run"]]])");
  if (!json) {
    llvm::consumeError(json.takeError());
    return 1;
  }
  auto content = zkc::source::decode(*json);
  if (!content) {
    llvm::consumeError(content.takeError());
    return 2;
  }
  auto *source = std::get_if<zkc::source::Module>(&*content);
  if (!source)
    return 2;
  auto catalog = zkc::claims::inspect(*source, "main");
  if (!catalog) {
    llvm::consumeError(catalog.takeError());
    return 3;
  }
  zkc::claims::Contract contract;
  contract.sourceDigest =
      catalog->getAsObject()->getString("source_digest")->str();
  contract.entry = "main";
  contract.validator = "Validator";
  contract.kinds = {{"accepted", {"bool"}, "The input Boolean is true"}};
  contract.claims = {{"guard", "guard", {"v0"}},
                     {"result", "accepted", {"v0"}}};
  contract.required = {"result"};
  contract.terminals = {{"guard", "$/0/0"}};
  contract.laws = {{"check", "The Check body enforces its exact input"}};
  contract.rules = {{"accept",
                     "check",
                     "$/0",
                     "Check",
                     {"v0"},
                     {"v0"},
                     {"$/0/0"},
                     {"guard"},
                     "result"}};
  auto certificate = zkc::claims::derive(*source, contract);
  if (!certificate) {
    llvm::consumeError(certificate.takeError());
    return 4;
  }
  if (auto error = zkc::claims::check(*source, contract, *certificate)) {
    llvm::consumeError(std::move(error));
    return 5;
  }
  mlir::MLIRContext context;
  auto candidate =
      zkc::claims::import(*source, contract, *certificate, context);
  if (!candidate) {
    llvm::consumeError(candidate.takeError());
    return 6;
  }
  if (mlir::failed(mlir::verify(candidate->get())))
    return 7;
  const auto loaded = context.getLoadedDialects().size();
  if (auto error = zkc::claims::checkIR(*source, contract, candidate->get())) {
    llvm::consumeError(std::move(error));
    return 8;
  }
  if (context.getLoadedDialects().size() != loaded)
    return 9;

  // Structurally valid IR still needs independent source/contract checking.
  mlir::Builder builder(&context);
  candidate->get()->setAttr("claim.entry", builder.getStringAttr("other"));
  if (mlir::failed(mlir::verify(candidate->get())))
    return 10;
  auto mismatch = zkc::claims::checkIR(*source, contract, candidate->get());
  if (!mismatch)
    return 11;
  if (llvm::toString(std::move(mismatch)) != "claim-ir-mismatch")
    return 12;

  certificate->steps.clear();
  auto invalid = zkc::claims::import(*source, contract, *certificate, context);
  if (invalid)
    return 13;
  if (llvm::toString(invalid.takeError()) != "claim-unresolved")
    return 14;
  return 0;
}
