#include "zkc/Contracts/Bindings.h"

int main() {
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
