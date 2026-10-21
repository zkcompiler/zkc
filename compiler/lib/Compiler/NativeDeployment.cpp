#include "NativeDeployment.h"
#include "ArtifactJson.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Protocol/Construction.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Program/Admission.h"
#include "zkc/Program/Codec.h"
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
                            const NativeProofPolicy &policy,
                            StringRef selectedRole = {}) {
  const program::ParticipantEntry *entry = nullptr;
  for (const auto &candidate : program.entries)
    if (candidate.name == policy.entry)
      entry = &candidate;
  auto count = selectedRole.empty() ? source.getRoles().size() : 1;
  if (!entry || entry->participants.size() != count ||
      program.entries.size() != 1 || program.participants.size() != count)
    return error("native-deployment-correspondence");
  json::Array maps;
  unsigned stateInputs = !policy.suite.empty(), stateOutputs = stateInputs;
  bool codec = false;
  if (!policy.construction.empty()) {
    SymbolTableCollection symbols;
    auto record = symbols.lookupNearestSymbolFrom<pir::ConstructionOp>(
        source, StringAttr::get(source.getContext(), policy.construction));
    if (!record)
      return error("native-deployment-construction");
    auto plan = protocol::readConstructionPlan(record, symbols);
    if (!plan)
      return plan.takeError();
    codec = plan->codec.has_value();
    stateOutputs = plan->state.size();
    stateInputs =
        plan->root == protocol::ConstructionPlan::Root::Host ? stateOutputs : 0;
  }
  auto type = source.getFunctionType();
  for (auto item : source.getRoles()) {
    auto role = cast<StringAttr>(item);
    if (!selectedRole.empty() && role.getValue() != selectedRole)
      continue;
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
      if (is_contained(policy.services, i))
        continue;
      if (auto reference =
              dyn_cast<pir::ServiceReferenceType>(type.getInput(i))) {
        if (service == participant->services.size())
          return error("native-deployment-correspondence");
        const auto &port = participant->services[service++];
        if (port.contract != reference.getContract() ||
            port.inputIndex != ingress)
          return error("native-deployment-correspondence");
        services.push_back(json::Array{std::to_string(i), port.name,
                                       port.contract, std::to_string(ingress)});
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
    if (service != participant->services.size() ||
        participant->arguments.size() !=
            inputs.size() + stateInputs +
                unsigned(codec && role.getValue() == policy.validator) ||
        participant->results.size() !=
            outputs.size() + stateOutputs +
                unsigned(codec && role.getValue() == policy.producer) ||
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
  if (!candidate || !record || record->size() != 7 ||
      (*record)[0].getAsString() != "zkc.native-proof-descriptor/0" ||
      (*record)[1] != encodeNativeProofPolicy(policy) ||
      out[0].getAsString() != "zkc.native-proof/0" ||
      out[1].getAsString() != digest(sourceBytes) ||
      *actualDescriptor != *expectedDescriptor ||
      out[3].getAsString() != digest(*actualDescriptor) ||
      out[5].getAsString() != digest(*candidate) ||
      out[7] !=
          json::Value(json::Array{
              options.simplify ? "true" : "false",
              options.releaseStorage ? "true" : "false",
              options.mathematicalSelection.vectorReductionFusion ? "true"
                                                                  : "false",
              options.mathematicalSelection.finiteBulk ? "true" : "false",
              options.mathematicalSelection.collectFoldFusion ? "true"
                                                              : "false",
              options.mathematicalSelection.calculationBatching ? "true"
                                                                : "false"}) ||
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
  StringRef selectedRole;
  if (options.operation)
    selectedRole = *options.operation == NativeProofOperation::Verify
                       ? policy.validator
                       : policy.producer;
  auto maps = ports(entry, *program, policy, selectedRole);
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
Error checkNativeOperationArtifact(StringRef bytes, StringRef original,
                                   StringRef role) {
  auto artifact = parseJson(bytes, 16 * 1024 * 1024);
  if (!artifact)
    return artifact.takeError();
  auto *deployment = artifact->getAsArray();
  if (!deployment || deployment->size() != 9 ||
      (*deployment)[0].getAsString() != "zkc.native-proof/0" ||
      (*deployment)[1].getAsString() != original ||
      !(*deployment)[4].getAsString() || !(*deployment)[6].getAsArray() ||
      (*deployment)[6].getAsArray()->size() != 1)
    return error("entry.deployment",
                 "invalid operation-specific native proof deployment");
  auto descriptor = encodeLogicalTree((*deployment)[2]);
  if (!descriptor)
    return descriptor.takeError();
  auto candidate = *(*deployment)[4].getAsString();
  if ((*deployment)[3].getAsString() != digest(*descriptor) ||
      (*deployment)[5].getAsString() != digest(candidate))
    return error("entry.deployment",
                 "child native deployment identities differ");
  auto program = program::parse(candidate);
  if (!program)
    return program.takeError();
  if (auto e = protocol::admit(*program))
    return e;
  if (program->participants.size() != 1 || program->entries.size() != 1 ||
      program->participants.front().role != role)
    return error("entry.closure",
                 "proof child retained the wrong operation closure");
  auto *map = (*(*deployment)[6].getAsArray())[0].getAsArray();
  if (!map || map->size() != 6 || (*map)[0].getAsString() != role ||
      (*map)[1].getAsString() != program->participants.front().name)
    return error("entry.signature", "proof child port map differs");
  return Error::success();
}
} // namespace zkc::detail
