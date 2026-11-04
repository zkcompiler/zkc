#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/MathematicalFacts.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/TypePolicy.h"

int main() {
  using namespace zkc::protocol;
  VariantDescriptor descriptor{"Installed", {}};
  for (unsigned i = 0; i < 65; ++i)
    descriptor.alternatives.push_back({"arm" + std::to_string(i), {}});
  auto variant = variantType(std::move(descriptor));
  if (!variant) {
    llvm::consumeError(variant.takeError());
    return 5;
  }
  auto policy = typePolicy(*variant);
  if (!policy || !policy->copy || !policy->drop || !policy->message ||
      !variant->spelling().empty())
    return 6;
  uint64_t remaining = 1;
  zkc::facts::Work work(remaining);
  auto range = zkc::facts::transferWordRange(
      work, zkc::facts::WordOperation::BitAnd, {8, 16}, {7, 7});
  if (range.status != zkc::facts::Status::Proven || !range.value ||
      range.value->minimum != 0 || range.value->maximum != 7 || remaining)
    return 7;
  const auto *addition =
      mathematicalMeaning(zkc::MathematicalIdentity::FieldAdd);
  if (!addition || !addition->law.associative || !addition->law.commutative ||
      zkc::mathematicalIdentityName(addition->identity) != "FieldAdd")
    return 4;
  if (randomServiceField("random.bn254.fr/0") != "bn254.fr" ||
      !randomServiceField("random.koala-bear/0").empty() ||
      nativeChallengeField(
          "merlin3.koala-bear.ext8-binomial3.rejection31le/0") !=
          "koala-bear.ext8-binomial3")
    return 2;
  const BindingApplication mixed{
      "transcript.native.indexed.observe.data",
      {"merlin3.koala-bear.ext8-binomial3.rejection31le/0", "group:bn254.g2"},
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
