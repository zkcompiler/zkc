#include "zkc/Claims/Claims.h"
#include "zkc/Source/Codec.h"
#include "zkc/Support/Json.h"

// No MLIR context, frontend parser, transformation or driver is linked.
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
  certificate->steps.clear();
  auto rejected = zkc::claims::check(*source, contract, *certificate);
  if (!rejected)
    return 6;
  llvm::consumeError(std::move(rejected));
  return 0;
}
