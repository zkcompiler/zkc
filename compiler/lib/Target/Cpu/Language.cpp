#include "../../Compiler/LanguageDiagnostics.h"
#include "LanguageSelection.h"
#include "zkc/Compiler/NativeCompilation.h"
#include "zkc/Compiler/NativeLanguage.h"
#include "zkc/Compiler/Observation.h"
#include "zkc/Language/Names.h"
#include "zkc/Support/Refusal.h"
using namespace llvm;
namespace zkc::language {
namespace {
constexpr StringLiteral filename = "zkc-language-original.mlir";
}
namespace detail {
Error checkCompiledProof(const CheckedOriginal &original,
                         const NativeProofPolicy &selection,
                         const CompiledNativeProof &compiled) {
  // Occurrence selection adds only the draws.
  auto selected = compiled.policy;
  selected.draws.clear();
  if (compiled.identity != original.identity() || selected != selection)
    return error("source.entry",
                 "compiled proof selected another source or policy");
  return Error::success();
}
Error checkCompiledRun(const CheckedOriginal &original, StringRef entry,
                       const CompiledRun &compiled) {
  if (compiled.identity != original.identity() || compiled.entry != entry)
    return error("source.entry", "compiled bundle selected another protocol");
  return Error::success();
}
} // namespace detail
StringRef CompiledEntry::bytes() const {
  if (auto *run = std::get_if<CompiledRun>(&compiled))
    return run->bundle;
  if (auto *host = std::get_if<CompiledHost>(&compiled))
    return host->artifact;
  return std::get<CompiledNativeProof>(compiled).deployment;
}
Expected<CompiledEntry> compileEntry(const CheckedOriginal &original,
                                     const EntryOptions &options) {
  auto scope =
      options.observations
          ? options.observations->scope(original.entry().root().qualifiedName)
          : CompilationObservation::Scope{};
  auto located = [&](Error error) {
    return locateCompilationFailure(original, std::move(error));
  };
  if (original.interface().host) {
    auto host = compileHost(original, options);
    if (!host)
      return located(host.takeError());
    return CompiledEntry(original, EntryArtifact(std::move(*host)), options);
  }
  const auto &view = original.interface();
  const auto &protocol = view.selectedProtocol();
  if (view.proof) {
    auto derived = proofPolicy(original);
    if (!derived)
      return located(derived.takeError());
    const auto &selection = *derived;
    NativeProofOptions native;
    native.observations = options.observations;
    native.cpuTarget = options.cpuTarget;
    native.policy = NativeProofSelection{selection};
    if (auto operation = original.entry().invocationKind())
      native.operation = *operation == HostInvocation::Kind::Verify
                             ? NativeProofOperation::Verify
                             : NativeProofOperation::Prove;
    native.simplify = options.simplify;
    native.releaseStorage = options.releaseStorage;
    native.mathematicalSelection = options.mathematicalSelection;
    native.oracleRealization = options.oracleRealization;
    auto compiled = compileNativeProof(original.bytes(), filename, native,
                                       mlir::DialectRegistry());
    if (!compiled)
      return located(compiled.takeError());
    // Native compilation independently checks the full deployment. Pin its
    // source and policy again at the source-language ownership boundary.
    if (auto e = detail::checkCompiledProof(original, selection, *compiled))
      return std::move(e);
    return CompiledEntry(original, EntryArtifact(std::move(*compiled)),
                         options);
  }
  RunOptions run;
  run.observations = options.observations;
  run.cpuTarget = options.cpuTarget;
  run.entry = protocol.symbol;
  run.simplify = options.simplify;
  run.releaseStorage = options.releaseStorage;
  run.mathematicalSelection = options.mathematicalSelection;
  run.oracleRealization = options.oracleRealization;
  auto compiled =
      compileRun(original.bytes(), filename, run, mlir::DialectRegistry());
  if (!compiled)
    return located(compiled.takeError());
  if (auto e = detail::checkCompiledRun(original, protocol.symbol, *compiled))
    return std::move(e);
  return CompiledEntry(original, EntryArtifact(std::move(*compiled)), options);
}
} // namespace zkc::language
