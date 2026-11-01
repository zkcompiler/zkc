#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Evm.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Transforms/Stages.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
struct EvmCompilation::Storage {
  MLIRContext context;
  OwningOpRef<ModuleOp> module;
  std::string yul, source, digest;
  json::Value abi = nullptr, descriptor = nullptr, manifest = nullptr;
  NativeProofPolicy policy;
  EvmLimits limits;
  std::unique_ptr<CheckedEndpoint> endpoint;
  std::shared_ptr<const mathematical::RealizedProtocol> realization;
  explicit Storage(const DialectRegistry &registry) : context(registry) {
    DialectRegistry builtins;
    registerDialects(builtins);
    builtins.insert<evm::EvmDialect>();
    context.appendDialectRegistry(builtins);
    context.loadAllAvailableDialects();
  }
};
EvmCompilation::EvmCompilation(std::unique_ptr<Storage> value)
    : storage(std::move(value)) {}
EvmCompilation::EvmCompilation(EvmCompilation &&) noexcept = default;
EvmCompilation &EvmCompilation::operator=(EvmCompilation &&) noexcept = default;
EvmCompilation::~EvmCompilation() = default;
const std::string &EvmCompilation::yul() const { return storage->yul; }
const json::Value &EvmCompilation::abi() const { return storage->abi; }
const json::Value &EvmCompilation::descriptor() const {
  return storage->descriptor;
}
const json::Value &EvmCompilation::manifest() const {
  return storage->manifest;
}
const NativeProofPolicy &EvmCompilation::policy() const {
  return storage->policy;
}
const EvmLimits &EvmCompilation::limits() const { return storage->limits; }
StringRef EvmCompilation::sourceSha256() const { return storage->digest; }
StringRef EvmCompilation::sourceBytes() const { return storage->source; }
OwningOpRef<ModuleOp> EvmCompilation::targetSnapshot() const {
  return cast<ModuleOp>(storage->module->getOperation()->clone());
}

json::Value encodeEvmLimits(const EvmLimits &limits) {
  return json::Object{{"rounds", limits.rounds},
                      {"public_elements", limits.publicElements},
                      {"frame_bytes", limits.frameBytes},
                      {"public_bytes", limits.publicBytes},
                      {"context_bytes", limits.contextBytes},
                      {"proof_bytes", limits.proofBytes},
                      {"calldata_bytes", limits.calldataBytes},
                      {"root_bytes", limits.rootBytes},
                      {"memory_bytes", limits.memoryBytes},
                      {"transcript_transitions", limits.transcriptTransitions},
                      {"practical_gas", limits.practicalGas}};
}
namespace {
Error validateLimits(const EvmLimits &limits) {
  EvmLimits ceiling;
  uint64_t EvmLimits::*members[] = {
      &EvmLimits::rounds,        &EvmLimits::publicElements,
      &EvmLimits::frameBytes,    &EvmLimits::publicBytes,
      &EvmLimits::contextBytes,  &EvmLimits::proofBytes,
      &EvmLimits::calldataBytes, &EvmLimits::rootBytes,
      &EvmLimits::memoryBytes,   &EvmLimits::transcriptTransitions,
      &EvmLimits::practicalGas};
  for (auto member : members)
    if (limits.*member == 0 || limits.*member > ceiling.*member)
      return error("evm.limits", "deployment ceilings must be positive and "
                                 "cannot exceed the supported profile");
  if (limits.memoryBytes < 4096)
    return error("evm.limits",
                 "memory ceiling cannot hold the fixed target state");
  return Error::success();
}
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
json::Value standardAbi() {
  return json::Array{json::Object{
      {"type", "function"},
      {"name", "verify"},
      {"stateMutability", "view"},
      {"inputs",
       json::Array{json::Object{{"name", "publicInputs"}, {"type", "bytes[]"}},
                   json::Object{{"name", "context"}, {"type", "bytes"}},
                   json::Object{{"name", "proof"}, {"type", "bytes"}}}},
      {"outputs",
       json::Array{json::Object{{"name", "accepted"}, {"type", "bool"}}}}}};
}
} // namespace

Expected<EvmCompilation> compileEvmProof(StringRef bytes, StringRef filename,
                                         const EvmOptions &options,
                                         const DialectRegistry &registry) {
  if (auto error = validateLimits(options.limits))
    return std::move(error);
  if (bytes.empty() || bytes.size() > 16 * 1024 * 1024 ||
      filename.size() > 4096 || !mlirNestingWithinLimit(bytes))
    return error("evm.source-limit",
                 "source input exceeds the compiler limits");
  auto result = std::make_unique<EvmCompilation::Storage>(registry);
  std::string diagnostics;
  ScopedDiagnosticHandler handler(&result->context,
                                  [&](Diagnostic &diagnostic) {
                                    raw_string_ostream out(diagnostics);
                                    diagnostic.print(out);
                                    out << '\n';
                                    return success();
                                  });
  auto source = parseSourceString<ModuleOp>(bytes, &result->context);
  if (!source || failed(admitStage(source->getOperation())))
    return error("evm.source", diagnostics);
  auto policy = options.policy;
  if (policy.suite != "hash-chain.keccak256.bls12-381.fr64be/0" ||
      !policy.construction.empty() ||
      policy.format != protocol::ProofFormat::Native)
    return error("evm.construction",
                 "EVM requires the managed framed Keccak Fr64BE construction");
  if (policy.draws.empty()) {
    auto selected = selectNativeProofDraws(*source, policy, options.mathematics,
                                           options.oracleSelection);
    if (!selected)
      return selected.takeError();
    policy = std::move(*selected);
  }
  auto constructed = constructNativeProof(*source, policy, options.mathematics,
                                          options.oracleSelection);
  if (!constructed)
    return constructed.takeError();
  if (auto checked =
          checkNativeProof(*source, *constructed->module, policy,
                           options.mathematics, options.oracleSelection))
    return std::move(checked);
  auto *descriptor = constructed->descriptor.getAsArray();
  if (!descriptor || descriptor->size() != 9 ||
      (*descriptor)[0].getAsString() != "zkc.native-proof-descriptor/0" ||
      (*descriptor)[1] != encodeNativeProofPolicy(policy) ||
      !(*descriptor)[8].getAsString())
    return error("evm.descriptor",
                 "common construction returned an invalid descriptor");
  PassManager pipeline(&result->context);
  buildClosedExecutionPipeline(pipeline, false, false, options.mathematics);
  if (failed(pipeline.run(*constructed->module)))
    return error("evm.closed-execution", diagnostics);
  auto endpoint = closeEndpoint(*constructed->module, policy.validator);
  if (!endpoint)
    return endpoint.takeError();
  EvmOptions selected = options;
  selected.policy = policy;
  auto module = evm::lowerEndpoint(*endpoint, selected);
  if (!module)
    return joinErrors(module.takeError(),
                      error("evm.diagnostics", diagnostics));
  auto yul = evm::exportYul(**module, bytes, constructed->descriptor, policy,
                            options.limits);
  if (!yul)
    return yul.takeError();
  result->source = bytes.str();
  result->digest = digest(bytes);
  result->yul = std::move(*yul);
  result->module = std::move(*module);
  result->descriptor = std::move(constructed->descriptor);
  result->abi = standardAbi();
  result->policy = std::move(policy);
  result->limits = options.limits;
  result->endpoint = std::make_unique<CheckedEndpoint>(std::move(*endpoint));
  result->realization = std::move(constructed->realization);
  result->manifest = json::Object{
      {"format", "zkc.evm-source-manifest/0"},
      {"target", "evm"},
      {"fork", "cancun"},
      {"source_sha256", result->digest},
      {"source_format", "zkc.original-mlir/0"},
      {"entry", result->policy.entry},
      {"producer", result->policy.producer},
      {"validator", result->policy.validator},
      {"compiler", language::compilerToolchainIdentity()},
      {"yul_sha256", digest(result->yul)},
      {"limits", encodeEvmLimits(options.limits)},
      {"solc_version", "0.8.38"},
      {"optimizer_steps", ":"},
      {"release_validation", "pending-deployment-and-dynamic-trace"}};
  return EvmCompilation(std::move(result));
}

Expected<EvmCompilation>
compileEvmEntry(const language::CheckedOriginal &original,
                const EvmOptions &options) {
  const auto &view = original.interface();
  if (!view.proof || view.host)
    return error("evm.entry", "EVM requires a checked proof Entry");
  const auto &proof = *view.proof;
  if (proof.acceptance.native.size() != 1)
    return error("evm.entry", "EVM requires one selected Boolean acceptance");
  EvmOptions selected = options;
  auto policy = language::proofPolicy(original);
  if (!policy)
    return policy.takeError();
  selected.policy = std::move(*policy);
  return compileEvmProof(original.bytes(), "zkc-language-original.mlir",
                         selected, DialectRegistry());
}

json::Value encodeEvmCompilation(const EvmCompilation &compiled) {
  return json::Object{{"format", "zkc.evm-source/0"},
                      {"target", "evm"},
                      {"fork", "cancun"},
                      {"yul", compiled.yul()},
                      {"abi", compiled.abi()},
                      {"descriptor", compiled.descriptor()},
                      {"policy", encodeNativeProofPolicy(compiled.policy())},
                      {"limits", encodeEvmLimits(compiled.limits())},
                      {"source_sha256", compiled.sourceSha256()},
                      {"manifest", compiled.manifest()}};
}
} // namespace zkc
