#include "../../Compiler/LanguageDiagnostics.h"
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
    auto parsed = json::parse(compiled->deployment);
    if (!parsed)
      return parsed.takeError();
    auto *deployment = parsed->getAsArray();
    const json::Array *descriptor = deployment && deployment->size() == 9
                                        ? (*deployment)[2].getAsArray()
                                        : nullptr;
    auto selected = compiled->policy;
    selected.draws.clear();
    if (!descriptor || descriptor->size() != 9 ||
        (*deployment)[0].getAsString() != "zkc.native-proof/0" ||
        (*deployment)[1].getAsString() != original.identity() ||
        encodeNativeProofPolicy(selected) !=
            encodeNativeProofPolicy(selection) ||
        (*descriptor)[1] != encodeNativeProofPolicy(compiled->policy))
      return error("source.entry",
                   "compiled proof selected another source or policy");
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
  auto bundle = json::parse(compiled->bundle);
  if (!bundle)
    return bundle.takeError();
  auto *object = bundle->getAsObject();
  if (!object || object->getString("entry") != protocol.symbol)
    return error("source.entry", "compiled bundle selected another protocol");
  return CompiledEntry(original, EntryArtifact(std::move(*compiled)), options);
}
} // namespace zkc::language
