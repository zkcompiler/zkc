//===- zkc-run.cpp - execute an endpoint against golden vectors -*- C++ -*-===//
// The Tier-2 gate (docs/spec/boundaries.md §5): replay every vector,
// require the expected verdict and the exact challenge sequence.
// Drivers own IO; a mismatch is a non-zero exit.
//===----------------------------------------------------------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Dialect/Pir/Transforms/Projection.h"
#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Interpreter/ExecutionProfile.h"
#include "zkc/Interpreter/Interpreter.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Tools/ToolUtils.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/MemoryBuffer.h"

#include <vector>

using namespace mlir;
namespace cl = llvm::cl;

static cl::opt<std::string> inputFilename(cl::Positional, cl::init("-"),
                                          cl::desc("<oir .mlir>"));
static cl::opt<std::string>
    vectorsFilename("vectors", cl::init(""),
                    cl::desc("Golden vector file (JSON)"));
static cl::opt<std::string> replayDuplexFilename(
    "replay-duplex", cl::init(""),
    cl::desc("Replay a captured upstream transcript (a replay-slice fixture) "
             "through the native pinned duplex and compare every derived "
             "sample"));
static cl::opt<std::string>
    profileName("profile", cl::init("toy"),
                cl::desc("Execution profile (supplier set): toy | plonky3 | "
                         "toy-cheat"));
static cl::opt<std::string> proveWitness(
    "prove", cl::init(""),
    cl::desc("Run the prover endpoint: comma-separated label=hex witness "
             "payloads (with --statement; the input is the prover artifact)"));
static cl::opt<std::string> proveStatement(
    "statement", cl::init(""),
    cl::desc("Comma-separated label=value statement inputs for --prove"));
static cl::opt<std::string> verifyWith(
    "verify-with", cl::init(""),
    cl::desc("After --prove, execute this verifier artifact on the emitted "
             "bytes with the same statement — the in-process round trip"));
static cl::opt<std::string> protocolVocabulary(
    "protocol-vocabulary", cl::init(""),
    cl::desc("Admit the standalone artifact against this "
             "ProtocolVocabulary before executing it. Read on both the "
             "prover and the verifier path; the hole-contract ABI is "
             "re-resolved from it."));
static cl::opt<std::string> constructionProfileRegistry(
    "construction-profile-registry", cl::init(""),
    cl::desc("Construction-profile registry accompanying "
             "--protocol-vocabulary"));

namespace {

struct GoldenVector {
  llvm::StringMap<std::string> statement;
  std::string proofBytes;
  std::string expectedVerdict;
  std::string name;
  std::string expectedChallenges;
};

/// One endpoint container loaded from one file, keeping the parsed
/// module (and its source-line diagnostic handler) alive alongside the
/// artifact op it owns.
struct LoadedEndpoint {
  zkc::tool::ParsedModule module;
  zkc::oir::ArtifactOp artifact;
  explicit operator bool() const { return static_cast<bool>(artifact); }
};

} // namespace

/// Parse one .mlir file and find its single oir.artifact; parse and
/// single-op diagnostics are already emitted on failure.
static LoadedEndpoint loadEndpoint(llvm::StringRef path, MLIRContext &context) {
  LoadedEndpoint loaded;
  loaded.module = zkc::tool::parseModule(path, context);
  if (loaded.module)
    loaded.artifact = zkc::tool::getSingleOp<zkc::oir::ArtifactOp>(
        loaded.module.get(), "oir.artifact");
  return loaded;
}

/// Resolve --profile through the library's one selection vocabulary, or
/// report the refusal and return null.
static const zkc::interpreter::ExecutionProfile *resolveProfile() {
  auto profile = zkc::interpreter::selectProfile(profileName);
  if (!profile) {
    llvm::errs() << llvm::toString(profile.takeError()) << "\n";
    return nullptr;
  }
  return &*profile;
}

namespace {

/// The upstream-to-native agreement check (docs/spec/endpoints.md §4):
/// drive the native pinned duplex
/// over the captured upstream verifier transcript and require every
/// derived sample to equal what the upstream verifier derived. Primitives
/// held fixed by the known-answer self-check, this validates the
/// orchestration-layer semantics — the layer where the weak-Fiat-Shamir
/// bug class lives.
int replayDuplex(llvm::StringRef path) {
  auto buffer = llvm::MemoryBuffer::getFile(path);
  if (!buffer) {
    llvm::errs() << "cannot read " << path << "\n";
    return 1;
  }
  auto parsed = llvm::json::parse((*buffer)->getBuffer());
  if (!parsed) {
    llvm::errs() << "fixture: " << llvm::toString(parsed.takeError()) << "\n";
    return 1;
  }
  const llvm::json::Object *root = parsed->getAsObject();
  const llvm::json::Array *events =
      root ? root->getArray("transcript") : nullptr;
  if (!events) {
    llvm::errs() << "fixture carries no transcript\n";
    return 1;
  }

  // The element framing belongs to the profile's codec, not to this
  // driver: one absorbed element frames through the low-bits codec's
  // absorbFraming, and one derived sample decodes one squeezed symbol
  // back through the same supplier (framing and wire form agree for
  // this codec family by construction).
  const zkc::interpreter::CodecSupplier *codec =
      zkc::interpreter::plonky3Profile().codec("plonky3_bb31_low_bits");
  if (!codec) {
    llvm::errs() << "the plonky3 profile supplies no low-bits codec for "
                    "replay framing\n";
    return 1;
  }
  auto duplex = zkc::interpreter::rawPlonky3Duplex();
  auto absorbElement = [&](uint64_t element) {
    llvm::SmallVector<uint8_t, 4> framed;
    codec->absorbFraming(llvm::APInt(zkc::interpreter::kValueBits, element),
                         framed);
    duplex->absorb(framed);
  };
  auto sampleElement = [&]() -> uint64_t {
    llvm::SmallVector<uint8_t, 32> symbols =
        duplex->squeeze("", codec->squeezeSymbols());
    return codec->decodeWire(symbols).getZExtValue();
  };

  unsigned samples = 0;
  for (auto indexedEntry : llvm::enumerate(*events)) {
    size_t index = indexedEntry.index();
    const llvm::json::Value &entry = indexedEntry.value();
    // A malformed fixture is a clean named refusal, never a null deref —
    // the same fail-closed treatment the --vectors file gets.
    auto malformed = [&](llvm::StringRef what) {
      llvm::errs() << "fixture: malformed event " << index << " (" << what
                   << ")\n";
      return 1;
    };
    const llvm::json::Object *event = entry.getAsObject();
    if (!event)
      return malformed("not an object");
    std::optional<llvm::StringRef> kind = event->getString("event");
    if (!kind)
      return malformed("no string 'event'");
    auto diverged = [&](llvm::StringRef what) {
      llvm::errs() << "divergence at event " << index << " (" << *kind
                   << "): " << what << "\n";
      return 1;
    };
    if (*kind == "ObserveVal") {
      std::optional<int64_t> value = event->getInteger("value");
      if (!value)
        return malformed("no integer 'value'");
      absorbElement(*value);
    } else if (*kind == "ObserveCap") {
      const llvm::json::Array *rows = event->getArray("value");
      if (!rows)
        return malformed("no array 'value'");
      for (const llvm::json::Value &row : *rows) {
        const llvm::json::Array *words = row.getAsArray();
        if (!words)
          return malformed("cap row is not an array");
        for (const llvm::json::Value &word : *words) {
          std::optional<int64_t> element = word.getAsInteger();
          if (!element)
            return malformed("cap word is not an integer");
          absorbElement(*element);
        }
      }
    } else if (*kind == "SampleVal") {
      std::optional<int64_t> expected = event->getInteger("value");
      if (!expected)
        return malformed("no integer 'value'");
      uint64_t got = sampleElement();
      ++samples;
      if (got != (uint64_t)*expected)
        return diverged("derived " + std::to_string(got) + ", upstream " +
                        std::to_string(*expected));
    } else if (*kind == "SampleBits") {
      const llvm::json::Object *value = event->getObject("value");
      if (!value)
        return malformed("no object 'value'");
      std::optional<int64_t> bits = value->getInteger("bits");
      std::optional<int64_t> expected = value->getInteger("value");
      if (!bits || !expected)
        return malformed("'value' needs integers 'bits' and 'value'");
      if (*bits < 0 || *bits > 63)
        return malformed("'bits' out of range");
      uint64_t got = sampleElement() & ((1ull << *bits) - 1);
      ++samples;
      if (got != (uint64_t)*expected)
        return diverged("derived " + std::to_string(got) + ", upstream " +
                        std::to_string(*expected));
    } else if (*kind == "CheckWitness") {
      const llvm::json::Object *value = event->getObject("value");
      if (!value)
        return malformed("no object 'value'");
      std::optional<int64_t> bits = value->getInteger("bits");
      if (!bits)
        return malformed("no integer 'bits'");
      if (*bits == 0)
        continue; // a sponge no-op upstream, mirrored here
      if (*bits < 0 || *bits > 63)
        return malformed("'bits' out of range");
      std::optional<int64_t> witness = value->getInteger("witness");
      std::optional<bool> ok = value->getBoolean("ok");
      if (!witness || !ok)
        return malformed("'value' needs integer 'witness' and boolean 'ok'");
      absorbElement(*witness);
      bool held = (sampleElement() & ((1ull << *bits) - 1)) == 0;
      ++samples;
      if (held != *ok)
        return diverged("grinding verdict disagrees");
    } else {
      return diverged("unknown event kind");
    }
  }
  llvm::outs() << "duplex replay: " << events->size() << " events, " << samples
               << " derived samples, all agree with the captured "
               << "upstream transcript\n";
  return 0;
}

} // namespace

/// Parse "k=v,k2=v2" into a map; empty text yields an empty map.
static bool parsePairs(llvm::StringRef text, llvm::StringMap<std::string> &out,
                       llvm::StringRef what) {
  llvm::SmallVector<llvm::StringRef> entries;
  text.split(entries, ',', -1, /*KeepEmpty=*/false);
  for (llvm::StringRef entry : entries) {
    auto [key, value] = entry.split('=');
    if (key.empty() || value.empty()) {
      llvm::errs() << what << ": malformed entry '" << entry << "'\n";
      return false;
    }
    out[key] = value.str();
  }
  return true;
}

/// The in-process round trip (docs/spec/endpoints.md §6.3): run
/// the prover endpoint, then — when a verifier artifact is supplied —
/// execute it on the emitted bytes with the same statement. The
/// challenge logs must agree entry for entry: that agreement is the
/// Fiat-Shamir erasure observed at run time, both replicas deriving the
/// same stream from the same absorb prefix.
static int proveRoundTrip() {
  MLIRContext context;
  context.loadDialect<zkc::oir::OirDialect, zkc::pir::PirDialect>();
  LoadedEndpoint prover = loadEndpoint(inputFilename, context);
  if (!prover)
    return 1;
  zkc::oir::ArtifactOp artifact = prover.artifact;
  if (!protocolVocabulary.empty()) {
    auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
        protocolVocabulary, constructionProfileRegistry);
    if (!environment) {
      llvm::errs() << "prove: " << llvm::toString(environment.takeError())
                   << "\n";
      return 1;
    }
    if (llvm::Error error =
            zkc::pir::admitOirArtifact(artifact, *environment)) {
      llvm::errs() << "prove: standalone admission refused: "
                   << llvm::toString(std::move(error)) << "\n";
      return 1;
    }
  }
  const zkc::interpreter::ExecutionProfile *profile = resolveProfile();
  if (!profile)
    return 1;
  llvm::StringMap<std::string> statement, witness;
  if (!parsePairs(proveStatement, statement, "statement") ||
      !parsePairs(proveWitness, witness, "witness"))
    return 1;
  auto proved = zkc::interpreter::prove(artifact, *profile, statement, witness);
  if (!proved) {
    llvm::errs() << "prove: " << llvm::toString(proved.takeError()) << "\n";
    return 1;
  }
  llvm::outs() << "prove: emitted " << proved->proof.size() << " bytes\n"
               << "prover challenges: " << llvm::join(proved->challenges, ",")
               << "\n"
               << "proof: " << llvm::toHex(proved->proof, /*LowerCase=*/true)
               << "\n";
  if (verifyWith.empty())
    return 0;

  LoadedEndpoint verifier = loadEndpoint(verifyWith, context);
  if (!verifier)
    return 1;
  auto result = zkc::interpreter::execute(verifier.artifact, *profile,
                                          statement, proved->proof);
  if (!result) {
    llvm::errs() << "verify: " << llvm::toString(result.takeError()) << "\n";
    return 1;
  }
  bool challengesAgree = result->challenges == proved->challenges;
  llvm::outs() << "verifier verdict: " << result->verdict << "\n"
               << "round trip: "
               << (result->verdict == "accept" && challengesAgree
                       ? "the derived prover's bytes are accepted by the "
                         "derived verifier, and both replicas derived the "
                         "same challenge stream"
                       : "FAILED")
               << "\n";
  return result->verdict == "accept" && challengesAgree ? 0 : 1;
}

int main(int argc, char **argv) {
  llvm::InitLLVM initLlvm(argc, argv);
  cl::ParseCommandLineOptions(
      argc, argv,
      "zkc-run: execute one OIR endpoint. --vectors checks a verifier against "
      "golden vectors, --prove runs a prover skeleton and can verify the "
      "proof it produced, --replay-duplex replays a pinned upstream "
      "transcript. Supplying the registries admits the artifact first.\n");

  if (!replayDuplexFilename.empty())
    return replayDuplex(replayDuplexFilename);
  if (!proveWitness.empty())
    return proveRoundTrip();
  if (vectorsFilename.empty()) {
    llvm::errs() << "either --vectors, --prove, or --replay-duplex is "
                    "required\n";
    return 1;
  }

  MLIRContext context;
  context.loadDialect<zkc::oir::OirDialect, zkc::pir::PirDialect>();
  LoadedEndpoint endpoint = loadEndpoint(inputFilename, context);
  if (!endpoint)
    return 1;
  zkc::oir::ArtifactOp artifact = endpoint.artifact;

  // The verify side re-admits against the environment on the same terms the
  // prove side does. Admission is what re-establishes the facts an endpoint
  // cannot carry alone — that its cited contracts still resolve to the
  // content it dispatches on — and a verifier reading an artifact from
  // elsewhere is exactly the reader that cannot assume them.
  if (!protocolVocabulary.empty()) {
    auto environment = zkc::registry::ProtocolEnvironment::loadFromFiles(
        protocolVocabulary, constructionProfileRegistry);
    if (!environment) {
      llvm::errs() << "vectors: " << llvm::toString(environment.takeError())
                   << "\n";
      return 1;
    }
    if (llvm::Error error =
            zkc::pir::admitOirArtifact(artifact, *environment)) {
      llvm::errs() << "vectors: standalone admission refused: "
                   << llvm::toString(std::move(error)) << "\n";
      return 1;
    }
  }

  auto buffer = llvm::MemoryBuffer::getFile(vectorsFilename);
  if (!buffer) {
    llvm::errs() << "cannot read " << vectorsFilename << "\n";
    return 1;
  }
  auto json = zkc::encoding::parseJsonUniqueKeys((*buffer)->getBuffer());
  if (!json) {
    llvm::errs() << "vectors: " << llvm::toString(json.takeError()) << "\n";
    return 1;
  }
  // A malformed vector file is a clean refusal, never a null deref:
  // this tool is a conformance gate and its own inputs get the same
  // fail-closed treatment as the artifacts it judges. Validate the complete
  // data shape before testing the citation: otherwise a stale or forged id
  // masks the actual malformed-input diagnostic and makes negative fixtures
  // accidentally depend on one validation order.
  auto malformed = [&](llvm::StringRef what) {
    llvm::errs() << "vectors: malformed file (" << what << ")\n";
    return 1;
  };
  const auto *root = json->getAsObject();
  if (!root)
    return malformed("root is not an object");
  std::optional<llvm::StringRef> artifactId = root->getString("artifact_id");
  if (!artifactId)
    return malformed("no string 'artifact_id'");
  const llvm::json::Array *vectors = root->getArray("vectors");
  if (!vectors)
    return malformed("no 'vectors' array");

  std::vector<GoldenVector> validated;
  validated.reserve(vectors->size());
  for (const llvm::json::Value &entry : *vectors) {
    const auto *vector = entry.getAsObject();
    if (!vector)
      return malformed("vector entry is not an object");
    const llvm::json::Object *stmt = vector->getObject("statement");
    std::optional<llvm::StringRef> proof = vector->getString("proof");
    std::optional<llvm::StringRef> expect = vector->getString("expect");
    std::optional<llvm::StringRef> name = vector->getString("name");
    const llvm::json::Array *expectChals = vector->getArray("challenges");
    if (!stmt || !proof || !expect || !name || !expectChals)
      return malformed("a vector needs statement, proof, expect, name, "
                       "and challenges");
    GoldenVector parsedVector;
    for (const auto &kv : *stmt) {
      std::optional<llvm::StringRef> value = kv.second.getAsString();
      if (!value)
        return malformed("statement values are strings");
      parsedVector.statement[kv.first.str()] = value->str();
    }
    if (!llvm::tryGetFromHex(*proof, parsedVector.proofBytes))
      return malformed("proof is not hex");
    parsedVector.expectedVerdict = expect->str();
    parsedVector.name = name->str();
    for (const llvm::json::Value &c : *expectChals) {
      std::optional<llvm::StringRef> value = c.getAsString();
      if (!value)
        return malformed("challenges are decimal strings");
      parsedVector.expectedChallenges +=
          (parsedVector.expectedChallenges.empty() ? "" : ",") + value->str();
    }
    validated.push_back(std::move(parsedVector));
  }

  // The tool-level identity pre-gate: authenticate the authored id
  // before any vector runs (execute() re-validates per vector; this
  // gate exists so the citation below is judged against the recomputed
  // identity, never against an unauthenticated authored string).
  if (llvm::Error error = zkc::encoding::validateOirIdentity(artifact)) {
    llvm::errs() << llvm::toString(std::move(error)) << "\n";
    return 1;
  }
  auto identity = zkc::encoding::computeOirId(artifact);
  if (!identity) {
    llvm::errs() << llvm::toString(identity.takeError()) << "\n";
    return 1;
  }

  if (*artifactId != *identity) {
    llvm::errs() << "vectors do not cite this artifact\n";
    return 1;
  }

  const zkc::interpreter::ExecutionProfile *profile = resolveProfile();
  if (!profile)
    return 1;

  bool allHeld = true;
  for (const GoldenVector &vector : validated) {
    auto result = zkc::interpreter::execute(
        artifact, *profile, vector.statement,
        ArrayRef<uint8_t>((const uint8_t *)vector.proofBytes.data(),
                          vector.proofBytes.size()));
    if (!result) {
      llvm::errs() << "profile error: " << llvm::toString(result.takeError())
                   << "\n";
      return 1;
    }
    std::string challenges = llvm::join(result->challenges, ",");
    bool held = result->verdict == vector.expectedVerdict &&
                challenges == vector.expectedChallenges;
    allHeld &= held;
    llvm::outs() << vector.name << ": " << result->verdict << " [" << challenges
                 << "]" << (held ? "" : "  MISMATCH") << "\n";
  }
  return allHeld ? 0 : 1;
}
