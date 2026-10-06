#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Services.h"

int main() {
  using namespace zkc::protocol;
  if (randomServiceField("random.bn254.fr/1") != "bn254.fr" ||
      !randomServiceField("random.koala-bear/1").empty() ||
      nativeChallengeField(
          "merlin3.koala-bear.ext8-binomial3.rejection31le/1") !=
          "koala-bear.ext8-binomial3")
    return 2;
  const BindingApplication mixed{
      "transcript.native.indexed.observe.data",
      {"merlin3.koala-bear.ext8-binomial3.rejection31le/1", "group:bn254.g2"},
      "plonky3/transcript.native.indexed.observe.data"};
  auto observed = resolveBinding(mixed, true);
  if (!observed) {
    llvm::consumeError(observed.takeError());
    return 3;
  }

  const zkc::protocol::BindingApplication binding{
      "poly.fold", {"bls12-381.fr"}, "arkworks/poly.fold"};
  auto logical = zkc::protocol::resolveBinding(binding, false);
  auto physical = zkc::protocol::resolveBinding(binding, true);
  if (!logical || !physical) {
    if (!logical)
      llvm::consumeError(logical.takeError());
    if (!physical)
      llvm::consumeError(physical.takeError());
    return 1;
  }
  return logical->inputs.front().representation != "" ||
         physical->inputs.front().representation.empty();
}
