#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "zkc/Compiler/Evm.h"
#include "zkc/Compiler/LanguagePackage.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Evm/Evm.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/MLIRInput.h"
#include "zkc/Support/Refusal.h"
#include "zkc/Target/Evm/Target.h"
#include "zkc/Target/Evm/Transcript.h"
#include "zkc/Transforms/Stages.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
// The declared fork names, in declaration order, for fork refusals.
std::string declaredForks() {
  std::string names;
#define ZKC_EVM_FORK_NAME(Enumerator, name, ...)                               \
  names += (names.empty() ? "" : ", ") + std::string(name);
  ZKC_EVM_TARGET_FORKS(ZKC_EVM_FORK_NAME)
#undef ZKC_EVM_FORK_NAME
  return names;
}
} // namespace

StringRef evmForkName(EvmFork fork) {
  switch (fork) {
#define ZKC_EVM_FORK_CASE(Enumerator, name, ...)                               \
  case EvmFork::Enumerator:                                                    \
    return name;
    ZKC_EVM_TARGET_FORKS(ZKC_EVM_FORK_CASE)
#undef ZKC_EVM_FORK_CASE
  }
  return {};
}
Expected<EvmFork> parseEvmFork(StringRef name) {
#define ZKC_EVM_FORK_PARSE(Enumerator, spelling, ...)                          \
  if (name == spelling)                                                        \
    return EvmFork::Enumerator;
  ZKC_EVM_TARGET_FORKS(ZKC_EVM_FORK_PARSE)
#undef ZKC_EVM_FORK_PARSE
  return error("evm.fork", "expected a declared fork: " + declaredForks());
}
struct EvmCompilation::Storage {
  MLIRContext context;
  OwningOpRef<ModuleOp> module;
  std::string yul, source, digest;
  json::Value descriptor = nullptr, options = nullptr;
  EvmFork fork = EvmFork::ZKC_EVM_TARGET_DEFAULT_FORK;
  NativeProofPolicy policy;
  EvmLimits limits;
  std::unique_ptr<CheckedEndpoint> endpoint;
  std::unique_ptr<evm::EvmEndpoint> exported;
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
const json::Value &EvmCompilation::descriptor() const {
  return storage->descriptor;
}
const NativeProofPolicy &EvmCompilation::policy() const {
  return storage->policy;
}
const EvmLimits &EvmCompilation::limits() const { return storage->limits; }
EvmFork EvmCompilation::fork() const { return storage->fork; }
const json::Value &EvmCompilation::options() const { return storage->options; }
StringRef EvmCompilation::sourceSha256() const { return storage->digest; }
const evm::EvmEndpoint &EvmCompilation::endpoint() const {
  return *storage->exported;
}
StringRef EvmCompilation::sourceBytes() const { return storage->source; }
OwningOpRef<ModuleOp> EvmCompilation::targetSnapshot() const {
  return cast<ModuleOp>(storage->module->getOperation()->clone());
}

json::Value encodeEvmLimits(const EvmLimits &limits) {
  json::Object result;
#define ZKC_EVM_LIMIT_ENCODE(member, name, minimum, maximum)                   \
  result[name] = limits.member;
  ZKC_EVM_TARGET_LIMITS(ZKC_EVM_LIMIT_ENCODE)
#undef ZKC_EVM_LIMIT_ENCODE
  return result;
}
namespace {
// Each ceiling lies within its declared row. The declared minimum of the
// memory ceiling holds the fixed target state.
Error validateLimits(const EvmLimits &limits) {
#define ZKC_EVM_LIMIT_CHECK(member, name, minimum, maximum)                    \
  if (limits.member < minimum || limits.member > maximum)                      \
    return error("evm.limits", Twine("deployment ceiling ") + name +           \
                                   " lies outside its declared range");
  ZKC_EVM_TARGET_LIMITS(ZKC_EVM_LIMIT_CHECK)
#undef ZKC_EVM_LIMIT_CHECK
  return Error::success();
}
std::string digest(StringRef bytes) {
  return toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
}
} // namespace

Expected<EvmCompilation> compileEvmProof(StringRef bytes, StringRef filename,
                                         const EvmOptions &options,
                                         const DialectRegistry &registry) {
  if (evmForkName(options.fork).empty())
    return error("evm.fork", "expected a declared fork: " + declaredForks());
  if (auto error = validateLimits(options.limits))
    return std::move(error);
  // The CPU storage choice never reaches this target. The numerical
  // expression mode is not published: only CPU physical selection reads it.
  auto published = language::encodeCompileOptions(
      options.simplify, false, options.mathematics, options.oracleSelection);
  if (!published)
    return published.takeError();
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
  if (!policy.construction.empty() ||
      (policy.suite.empty() &&
       (!policy.services.empty() || !policy.draws.empty() ||
        !policy.gates.empty())) ||
      policy.format != protocol::ProofFormat::Native)
    return error("evm.construction",
                 "EVM requires framed transport with no transcript or a "
                 "managed construction over a realized transcript suite");
  if (!policy.suite.empty()) {
    evm::NativeLayouts layouts(result->context);
    if (auto realized =
            evm::realizeTranscript(layouts, result->context, policy.suite);
        !realized)
      return realized.takeError();
  }
  if (!policy.suite.empty() && policy.draws.empty()) {
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
  buildClosedExecutionPipeline(pipeline, options.simplify, false,
                               options.mathematics);
  if (failed(pipeline.run(*constructed->module)))
    return error("evm.closed-execution", diagnostics);
  auto endpoint = closeEndpoint(*constructed->module, policy.validator);
  if (!endpoint)
    return endpoint.takeError();
  // The exported schemas come from checked rows while the complete source
  // and the candidate are available.
  auto described = evm::describeEndpoint(*endpoint, constructed->descriptor,
                                         policy, digest(bytes));
  if (!described)
    return described.takeError();
  EvmOptions selected = options;
  selected.policy = policy;
  auto module = evm::lowerEndpoint(*endpoint, selected);
  if (!module)
    return joinErrors(module.takeError(),
                      error("evm.diagnostics", diagnostics));
  auto yul = evm::exportYul(**module, *described, policy, options.limits);
  if (!yul)
    return yul.takeError();
  result->source = bytes.str();
  result->digest = digest(bytes);
  result->yul = std::move(*yul);
  result->module = std::move(*module);
  result->descriptor = std::move(constructed->descriptor);
  result->policy = std::move(policy);
  result->limits = options.limits;
  result->fork = options.fork;
  json::Object publishedOptions;
  for (auto &[name, value] : *published)
    publishedOptions[name] = std::move(value);
  result->options = std::move(publishedOptions);
  result->endpoint = std::make_unique<CheckedEndpoint>(std::move(*endpoint));
  result->exported = std::make_unique<evm::EvmEndpoint>(std::move(*described));
  result->realization = std::move(constructed->realization);
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

json::Value encodeEvmCompilation(const EvmCompilation &compiled,
                                 const EvmSourceIdentity &source) {
  return json::Object{{"format", "zkc.evm-source/0"},
                      {"declaration", evm_target::identity},
                      {"fork", evmForkName(compiled.fork())},
                      {"options", compiled.options()},
                      {"limits", encodeEvmLimits(compiled.limits())},
                      {"entry", source.entry},
                      {"capture", source.capture},
                      {"installation", source.installation},
                      {"original", compiled.sourceSha256()},
                      {"source_format", "zkc.original-mlir/0"},
                      {"compiler", language::compilerToolchainIdentity()},
                      {"policy", encodeNativeProofPolicy(compiled.policy())},
                      {"descriptor", compiled.descriptor()},
                      {"yul", compiled.yul()}};
}
} // namespace zkc
