//===- zkc-translate.cpp - canonical encoding and identity ------*- C++ -*-===//
// Drivers own IO; the encoder owns nothing but the walk. Exactly one
// protocol container per invocation: identity is per-artifact.
//===----------------------------------------------------------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/Support/FileUtilities.h"
#include "zkc/Dialect/Oir/OirOps.h"
#include "zkc/Dialect/Oir/TranscriptSchedule.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Interpreter/ExecutionProfile.h"
#include "zkc/Interpreter/Interpreter.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/ToolOutputFile.h"

using namespace mlir;
namespace cl = llvm::cl;

static cl::opt<std::string> inputFilename(cl::Positional, cl::init("-"),
                                          cl::desc("<input .mlir>"));
static cl::opt<std::string> outputFilename("o", cl::init("-"),
                                           cl::desc("Output filename"));
static cl::opt<bool> emitCanonical(
    "canonical", cl::init(false),
    cl::desc("Emit the canonical encoding bytes of the protocol"));
static cl::opt<bool>
    emitId("id", cl::init(false),
           cl::desc("Emit the protocol identity (SHA-256 of the canonical "
                    "encoding)"));
static cl::opt<bool> emitOirCanonical(
    "oir-canonical", cl::init(false),
    cl::desc("Emit the canonical encoding bytes of the OIR artifact"));
static cl::opt<bool> emitOirId("oir-id", cl::init(false),
                               cl::desc("Emit the OIR artifact identity"));
static cl::opt<bool> emitOirSemanticId(
    "oir-semantic-id", cl::init(false),
    cl::desc("Emit the provenance-independent OIR semantic identity"));
static cl::opt<bool> emitProofSize(
    "proof-size", cl::init(false),
    cl::desc("Emit the proof size in bytes (sum of codec widths over "
             "the OIR program's proof-stream reads)"));
static cl::opt<bool> emitTranscriptSchedule(
    "transcript-schedule", cl::init(false),
    cl::desc("Emit the deterministic machine-readable OIR transcript "
             "schedule"));
static cl::opt<std::string>
    profileName("profile", cl::init("toy"),
                cl::desc("Execution profile (supplier set) pricing "
                         "--proof-size: toy | plonky3 | toy-cheat"));

/// The cost model's first entry: proof size from static structure —
/// the interpreter library prices each proof-stream read at its codec's
/// wire width under the selected profile, and an unroutable codec is a
/// refusal (never a zero that undercounts a proof).
static llvm::Expected<std::string> proofSizeText(Operation *container) {
  auto profile = zkc::interpreter::selectProfile(profileName);
  if (!profile)
    return profile.takeError();
  auto bytes = zkc::interpreter::proofSizeBytes(
      cast<zkc::oir::ArtifactOp>(container), *profile);
  if (!bytes)
    return bytes.takeError();
  return std::to_string(*bytes);
}

static llvm::json::Array sourcePositions(llvm::ArrayRef<int64_t> positions) {
  llvm::json::Array result;
  for (int64_t position : positions)
    result.push_back(position);
  return result;
}

/// Serialize the typed schedule view, not the textual MLIR.  The fixed
/// limitation algebra is part of the schema: this command reports projected
/// declarations and never silently upgrades them to execution/conformance
/// evidence.
static llvm::Expected<std::string>
transcriptScheduleJson(Operation *container) {
  auto schedule = zkc::oir::extractTranscriptSchedule(
      cast<zkc::oir::ArtifactOp>(container));
  if (!schedule)
    return schedule.takeError();

  llvm::json::Array events;
  for (const zkc::oir::TranscriptScheduleEvent &event : schedule->events) {
    if (const auto *absorb = std::get_if<zkc::oir::TranscriptAbsorb>(&event)) {
      events.push_back(llvm::json::Object{
          {"codec", absorb->codec},
          {"index", absorb->index},
          {"kind", "absorb"},
          {"payload_class", absorb->payloadClass},
          {"source_positions", sourcePositions(absorb->sourcePositions)},
      });
      continue;
    }
    const auto &squeeze = std::get<zkc::oir::TranscriptSqueeze>(event);
    events.push_back(llvm::json::Object{
        {"codec", squeeze.codec},
        {"count", squeeze.count},
        {"domain", squeeze.domain},
        {"index", squeeze.index},
        {"kind", "squeeze"},
        {"label", squeeze.label},
        {"payload_class", squeeze.payloadClass},
        {"rule", squeeze.rule},
        {"source_positions", sourcePositions(squeeze.sourcePositions)},
        {"space", squeeze.space},
    });
  }

  llvm::json::Value document = llvm::json::Object{
      {"artifact_id", schedule->artifactId},
      {"endpoint_kind", schedule->endpointKind},
      {"events", std::move(events)},
      {"limits",
       llvm::json::Object{
           {"challenge_codec_selection", "per_event_payload_class"},
           {"challenge_values", "not_computed"},
           {"construction_execution", "not_performed"},
           {"domain_evidence", "declaration_only"},
           {"protocol_correspondence", "not_evaluated"},
           {"squeeze_projection", "counted_scalar_or_vector"},
       }},
      {"schema", "zkc.oir.transcript_schedule"},
      {"source", schedule->source},
      {"sponge", llvm::json::Object{{"construction", schedule->sponge},
                                    {"iv", schedule->iv}}},
  };
  return zkc::encoding::canonicalJsonBytes(document);
}

int main(int argc, char **argv) {
  llvm::InitLLVM initLlvm(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv,
      "zkc-translate: emit one canonical encoding or identity for a sealed "
      "protocol or a projected endpoint. Exactly one emission flag per "
      "invocation; identity is per-artifact.\n");

  // The flag choice is validated before any file is touched, so a
  // zero-flag invocation names the actual problem, not a container
  // mismatch it implies.
  if ((int)emitCanonical + (int)emitId + (int)emitOirCanonical +
          (int)emitOirId + (int)emitOirSemanticId + (int)emitProofSize +
          (int)emitTranscriptSchedule !=
      1) {
    return zkc::tool::reportCannotAnswer("[zkc-E901] exactly one emission flag required");
  }

  MLIRContext context;
  context.loadDialect<zkc::pir::PirDialect, zkc::oir::OirDialect>();
  zkc::tool::ParsedModule parsed =
      zkc::tool::parseModule(inputFilename, context);
  if (!parsed)
    return 1;
  ModuleOp module = parsed.get();

  bool wantOir = emitOirCanonical || emitOirId || emitOirSemanticId ||
                 emitProofSize || emitTranscriptSchedule;
  Operation *container =
      zkc::tool::getSingleOp(module, "protocol container", [&](Operation &op) {
        return wantOir ? isa<zkc::oir::ArtifactOp>(op)
                       : isa<zkc::pir::ProtocolOp, zkc::pir::SealedOp>(op);
      });
  // Not the container this flag takes: the invocation handed the tool
  // the wrong document, and getSingleOp has already named it.
  if (!container)
    return 2;

  std::string error;
  auto output = openOutputFile(outputFilename, &error);
  if (!output) {
    return zkc::tool::reportCannotAnswer(llvm::Twine("[zkc-E900] ") + error);
  }

  auto result =
      emitCanonical       ? zkc::encoding::encodeCanonical(container)
      : emitId            ? zkc::encoding::computeId(container)
      : emitOirCanonical  ? zkc::encoding::encodeOirCanonical(container)
      : emitOirId         ? zkc::encoding::computeOirId(container)
      : emitOirSemanticId ? zkc::encoding::computeOirSemanticId(container)
      : emitProofSize     ? proofSizeText(container)
                          : transcriptScheduleJson(container);
  if (!result) {
    container->emitError() << llvm::toString(result.takeError());
    return 1;
  }
  output->os() << *result;
  if (emitId || emitOirId || emitOirSemanticId || emitProofSize ||
      emitTranscriptSchedule)
    output->os() << "\n";
  output->keep();
  return 0;
}
