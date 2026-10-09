#include "NativeDeployment.h"
#include "ArtifactJson.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/LogicalTree.h"
#include "zkc/Translation/Protocol.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
using namespace llvm;
using namespace mlir;
namespace zkc::detail {
namespace {
namespace pir = protocol_ir;
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
bool owns(Attribute owners, StringAttr role) {
  return is_contained(cast<ArrayAttr>(owners), role);
}
Expected<json::Array> ports(pir::MathematicalOp source,
                            const program::Participants &program,
                            const NativeProofPolicy &policy) {
  const program::ParticipantEntry *entry = nullptr;
  for (const auto &candidate : program.entries)
    if (candidate.name == policy.entry)
      entry = &candidate;
  if (!entry || entry->participants.size() != source.getRoles().size() ||
      program.entries.size() != 1 ||
      program.participants.size() != source.getRoles().size())
    return error("native-deployment-correspondence");
  json::Array maps;
  auto type = source.getFunctionType();
  for (auto item : source.getRoles()) {
    auto role = cast<StringAttr>(item);
    const program::Participant *participant = nullptr;
    for (const auto &mapping : entry->participants)
      if (mapping.first == role.getValue())
        for (const auto &candidate : program.participants)
          if (candidate.name == mapping.second)
            participant = &candidate;
    if (!participant || participant->role != role.getValue() ||
        participant->instance != policy.entry)
      return error("native-deployment-correspondence");
    json::Array inputs, outputs, services;
    unsigned ingress = 0, service = 0;
    for (auto [i, owners] : enumerate(source.getInputRoles())) {
      if (!owns(owners, role))
        continue;
      if (auto reference =
              dyn_cast<pir::ServiceReferenceType>(type.getInput(i))) {
        if (policy.service != i) {
          if (service == participant->services.size())
            return error("native-deployment-correspondence");
          const auto &port = participant->services[service++];
          if (port.contract != reference.getContract() ||
              port.inputIndex != ingress)
            return error("native-deployment-correspondence");
          services.push_back(json::Array{std::to_string(i), port.name,
                                         port.contract,
                                         std::to_string(ingress)});
        }
      } else {
        auto logical = protocol::encodeBoundType(type.getInput(i), false);
        if (!logical)
          return logical.takeError();
        inputs.push_back(json::Array{std::to_string(i), logical->spelling()});
      }
      ++ingress;
    }
    std::string acceptance;
    for (auto [i, owners] : enumerate(source.getOutputRoles())) {
      if (!owns(owners, role))
        continue;
      if (role.getValue() == policy.validator && i == policy.acceptance)
        acceptance = std::to_string(outputs.size());
      auto logical = protocol::encodeBoundType(type.getResult(i), false);
      if (!logical)
        return logical.takeError();
      outputs.push_back(json::Array{std::to_string(i), logical->spelling()});
    }
    unsigned state = !policy.suite.empty();
    if (service != participant->services.size() ||
        participant->arguments.size() != inputs.size() + state ||
        participant->results.size() != outputs.size() + state ||
        (role.getValue() == policy.validator && acceptance.empty()))
      return error("native-deployment-correspondence");
    maps.push_back(json::Array{role.str(), participant->name, std::move(inputs),
                               std::move(outputs), std::move(services),
                               acceptance});
  }
  return maps;
}
} // namespace
Error verifyNativeDeployment(ModuleOp source, ModuleOp physical,
                             StringRef sourceBytes,
                             const NativeProofPolicy &policy,
                             const NativeProofOptions &options,
                             const json::Value &descriptor,
                             const json::Array &wireSites, StringRef bytes) {
  if (!source || !physical || failed(verify(source)) ||
      failed(verify(physical)))
    return error("native-deployment-subject");
  auto parsed = parseArtifactJson(bytes);
  if (!parsed)
    return parsed.takeError();
  auto *deployment = parsed->getAsArray();
  if (!deployment || deployment->size() != 9)
    return error("native-deployment-correspondence");
  auto &out = *deployment;
  auto candidate = out[4].getAsString();
  auto expectedDescriptor = encodeLogicalTree(descriptor);
  if (!expectedDescriptor)
    return expectedDescriptor.takeError();
  auto actualDescriptor = encodeLogicalTree(out[2]);
  if (!actualDescriptor)
    return actualDescriptor.takeError();
  auto *record = out[2].getAsArray();
  if (!candidate || !record || record->size() != 6 ||
      (*record)[0].getAsString() != "zkc.native-proof-descriptor" ||
      (*record)[1] != encodeNativeProofPolicy(policy) ||
      out[0].getAsString() != "zkc.native-proof" ||
      out[1].getAsString() != digest(sourceBytes) ||
      *actualDescriptor != *expectedDescriptor ||
      out[3].getAsString() != digest(*actualDescriptor) ||
      out[5].getAsString() != digest(*candidate) ||
      out[7] !=
          json::Value(json::Array{options.simplify ? "true" : "false",
                                  options.releaseStorage ? "true" : "false"}) ||
      !out[8].getAsArray() || *out[8].getAsArray() != wireSites)
    return error("native-deployment-correspondence");
  auto decoded = protocol::verifyProgramArtifact(physical, *candidate);
  if (!decoded)
    return decoded.takeError();
  auto *program = &*decoded;
  pir::MathematicalOp entry;
  source.walk([&](pir::MathematicalOp op) {
    if (op.getSymName() == policy.entry)
      entry = op;
  });
  if (!entry)
    return error("native-deployment-subject");
  auto maps = ports(entry, *program, policy);
  if (!maps)
    return maps.takeError();
  if (!out[6].getAsArray() || *out[6].getAsArray() != *maps)
    return error("native-deployment-correspondence");
  // Public context uses original source indices/types, including setup-key
  // ports. Source policy admission established full validator coverage.
  auto *publicBindings = (*record)[4].getAsArray();
  if (!publicBindings || publicBindings->size() != policy.publicInputs.size())
    return error("native-deployment-correspondence");
  for (auto [row, index] : zip(*publicBindings, policy.publicInputs)) {
    auto *binding = row.getAsArray();
    if (index >= entry.getFunctionType().getNumInputs() || !binding ||
        binding->size() != 4 ||
        (*binding)[0].getAsString() != policy.validator ||
        (*binding)[1].getAsString() != std::to_string(index))
      return error("native-deployment-correspondence");
    auto type = protocol::encodeBoundType(
        entry.getFunctionType().getInput(index), false);
    if (!type)
      return type.takeError();
    if ((*binding)[2].getAsString() != type->spelling())
      return error("native-deployment-correspondence");
  }
  return Error::success();
}
} // namespace zkc::detail
