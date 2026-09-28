#include "zkc/Contracts/Services.h"
#include "zkc/Contracts/Declarations.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::protocol {
Expected<EntropyService>
resolveEntropyService(const BindingApplication &binding) {
  const auto *sample = samplingContract(binding.contract);
  const auto *parameters = parameterContract(binding.contract);
  if (!binding.implementation.empty() || !sample || !parameters ||
      parameters->validator != ParameterValidator::None ||
      sample->provider != RandomnessProvider::Entropy || sample->boundInput ||
      (sample->domain != SampleDomain::Field &&
       sample->domain != SampleDomain::NonzeroField) ||
      sample->stateInput != 0 || sample->valueOutput != 0 ||
      sample->stateOutput != 1)
    return error("entropy-service-contract");
  auto signature = resolveBinding(binding, false);
  if (!signature)
    return signature.takeError();
  if (signature->inputs.size() != 1 || signature->outputs.size() != 2 ||
      signature->inputs[0].kind != "rng" ||
      !(signature->inputs[0] == signature->outputs[1]))
    return error("entropy-service-signature");
  return EntropyService{binding, signature->inputs[0], signature->outputs[0],
                        *sample};
}
} // namespace zkc::protocol
