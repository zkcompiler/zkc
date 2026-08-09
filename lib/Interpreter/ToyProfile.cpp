//===- ToyProfile.cpp - the toy supplier set --------------------*- C++ -*-===//
// The first supplier set behind the profile interface: an SHA-256 chaining
// duplex, big-endian 8-byte codecs, and the safe-prime group moduli
// (p = 2q + 1, g = 4 of order q). Dependency-free on both sides —
// reference/oracle/exec.py defines the same semantics and generates the
// golden vectors the interpreter must replay bit-exactly.
//===----------------------------------------------------------------------===//

#include "zkc/Interpreter/ExecutionProfile.h"

#include "llvm/Support/SHA256.h"

using namespace llvm;

namespace zkc {
namespace interpreter {

namespace {

constexpr uint64_t kP = 4611686018427394499ull;
constexpr uint64_t kQ = 2305843009213697249ull;

/// The toy codec: one shape for both admitted names (`tg_be8`, `ts_be8`),
/// eight big-endian bytes on the wire and in absorb framing, squeeze
/// derivation by reducing the first eight digest bytes into the space.
class ToyCodec : public CodecSupplier {
public:
  ToyCodec(StringRef name, unsigned symbols)
      : codecName(name), symbols(symbols) {}

  StringRef name() const override { return codecName; }

  unsigned wireWidth() const override { return 8; }

  /// The registry's declared squeeze shape for this codec, which is what the
  /// soundness layer prices challenge entropy from. Reporting the interface
  /// default instead left the analysis and the execution describing different
  /// derivations — invisible only because this profile's sponge answers with
  /// a whole digest and discards the count.
  unsigned squeezeSymbols() const override { return symbols; }

  APInt decodeWire(ArrayRef<uint8_t> bytes) const override {
    uint64_t value = 0;
    for (uint8_t byte : bytes)
      value = (value << 8) | byte;
    return APInt(kValueBits, value);
  }

  void encodeWire(const APInt &value,
                  SmallVectorImpl<uint8_t> &out) const override {
    // The write direction is the framing: eight big-endian bytes, so
    // decode(encode(v)) == v and every emitted value is canonical.
    absorbFraming(value, out);
  }

  void absorbFraming(const APInt &value,
                     SmallVectorImpl<uint8_t> &out) const override {
    uint64_t narrow = value.getZExtValue();
    for (int shift = 56; shift >= 0; shift -= 8)
      out.push_back((narrow >> shift) & 0xff);
  }

  APInt squeezeDerive(ArrayRef<uint8_t> digest,
                      const APInt &space) const override {
    uint64_t value = 0;
    for (unsigned i = 0; i < 8; ++i)
      value = (value << 8) | digest[i];
    return APInt(kValueBits, value % space.getZExtValue());
  }

private:
  StringRef codecName;
  unsigned symbols;
};

/// The toy duplex: SHA-256 chaining with per-call framing tags. Byte 0x00
/// says "absorbed value" and 0x01 prefixes a squeeze domain, so no absorb
/// input can collide with a squeeze input — ambiguous framing would void
/// the Binding Lemma's a-injectivity independently of everything else
/// (kernel.md §13(e)).
class ToyDuplexState : public SpongeState {
public:
  explicit ToyDuplexState(StringRef sourceIdentity) {
    state =
        sha256({(const uint8_t *)sourceIdentity.data(), sourceIdentity.size()});
  }

  void absorb(ArrayRef<uint8_t> framed) override {
    SmallVector<uint8_t> input(state.begin(), state.end());
    input.push_back(0x00);
    input.append(framed.begin(), framed.end());
    state = sha256(input);
  }

  SmallVector<uint8_t, 32> squeeze(StringRef domain,
                                   unsigned nSymbols) override {
    // One 32-byte digest regardless of symbol count: the toy codec derives
    // its single scalar from the leading bytes.
    (void)nSymbols;
    SmallVector<uint8_t> input(state.begin(), state.end());
    input.push_back(0x01);
    input.append(domain.begin(), domain.end());
    state = sha256(input);
    return SmallVector<uint8_t, 32>(state.begin(), state.end());
  }

private:
  static std::array<uint8_t, 32> sha256(ArrayRef<uint8_t> bytes) {
    llvm::SHA256 hasher;
    hasher.update(bytes);
    return hasher.final();
  }

  std::array<uint8_t, 32> state{};
};

class ToyDuplexSupplier : public SpongeSupplier {
public:
  StringRef construction() const override { return "toy_duplex"; }
  StringRef ivPolicy() const override { return "artifact-id"; }
  std::unique_ptr<SpongeState> init(StringRef sourceIdentity) const override {
    return std::make_unique<ToyDuplexState>(sourceIdentity);
  }
};

/// Toy modular helpers over the 63-bit safe-prime pair.
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) {
  return static_cast<uint64_t>((static_cast<__uint128_t>(a) * b) % m);
}
static uint64_t powmod(uint64_t base, uint64_t exponent, uint64_t m) {
  uint64_t result = 1 % m;
  base %= m;
  while (exponent) {
    if (exponent & 1)
      result = mulmod(result, base, m);
    base = mulmod(base, base, m);
    exponent >>= 1;
  }
  return result;
}

/// The sigma witness payload convention shared with the reference twin:
/// sixteen bytes, x then k, each eight big-endian bytes.
static llvm::Error parseSigmaWitness(ArrayRef<SmallVector<uint8_t, 32>> handles,
                                     uint64_t &x, uint64_t &k) {
  if (handles.size() != 1 || handles[0].size() != 16)
    return llvm::createStringError(
        "sigma witness payload must be sixteen bytes (x, k big-endian)");
  x = k = 0;
  for (unsigned i = 0; i < 8; ++i)
    x = (x << 8) | handles[0][i];
  for (unsigned i = 8; i < 16; ++i)
    k = (k << 8) | handles[0][i];
  return llvm::Error::success();
}

/// The honest toy fill for the sigma commit: a = g^k, witness threaded.
class ToySigmaCommit : public HoleSupplier {
public:
  StringRef contractDigest() const override {
    return "sha256:b939155d962c0e82baee8477daebdd8168d59a1c828dabfd8f5724ab"
           "18b13e15";
  }
  llvm::Error fill(
      ArrayRef<StringRef> params, ArrayRef<StringRef> semanticParams,
      ArrayRef<APInt> values, ArrayRef<SmallVector<uint8_t, 32>> handles,
      SmallVectorImpl<APInt> &valueResults,
      SmallVectorImpl<SmallVector<uint8_t, 32>> &handleResults) const override {
    if (values.size() != 1)
      return llvm::createStringError("sigma commit takes one generator");
    uint64_t x, k;
    if (llvm::Error err = parseSigmaWitness(handles, x, k))
      return err;
    valueResults.push_back(
        APInt(kValueBits, powmod(values[0].getZExtValue(), k, kP)));
    handleResults.push_back(handles[0]);
    return llvm::Error::success();
  }
};

/// The honest toy fill for the sigma response: z = k + c*x mod q.
class ToySigmaResponse : public HoleSupplier {
public:
  StringRef contractDigest() const override {
    return "sha256:8ebf84fc8ed71a4c19d7af0dade5db63eda92c84888e903e2eadae4d"
           "444692d9";
  }
  llvm::Error fill(
      ArrayRef<StringRef> params, ArrayRef<StringRef> semanticParams,
      ArrayRef<APInt> values, ArrayRef<SmallVector<uint8_t, 32>> handles,
      SmallVectorImpl<APInt> &valueResults,
      SmallVectorImpl<SmallVector<uint8_t, 32>> &handleResults) const override {
    (void)handleResults;
    if (values.size() != 1)
      return llvm::createStringError("sigma response takes one challenge");
    uint64_t x, k;
    if (llvm::Error err = parseSigmaWitness(handles, x, k))
      return err;
    uint64_t c = values[0].getZExtValue() % kQ;
    valueResults.push_back(
        APInt(kValueBits, (k % kQ + mulmod(c, x % kQ, kQ)) % kQ));
    return llvm::Error::success();
  }
};

class ToyProfile : public ExecutionProfile {
public:
  StringRef name() const override { return "toy"; }

  const CodecSupplier *codec(StringRef codecName) const override {
    // These suppliers are the profile's whole codec vocabulary: the
    // proof-size view prices through their wireWidth(), so execution
    // and pricing cannot drift.
    if (codecName == tg.name())
      return &tg;
    if (codecName == ts.name())
      return &ts;
    return nullptr;
  }

  const SpongeSupplier *sponge(StringRef construction,
                               StringRef ivPolicy) const override {
    if (construction != duplex.construction() || ivPolicy != duplex.ivPolicy())
      return nullptr;
    return &duplex;
  }

  std::optional<SamplingPlan> admitSampling(StringRef rule, StringRef count,
                                            StringRef space) const override {
    // The toy profile samples eight digest bytes for one scalar, so it
    // sizes spaces as uint64 and admits only single uniform draws; a
    // wider space or a counted vector is a profile limit, not a verdict.
    if (count != "1" || rule != "uniform")
      return std::nullopt;
    uint64_t cardinality;
    if (space.getAsInteger(10, cardinality) || cardinality < 2)
      return std::nullopt;
    return SamplingPlan{APInt(kValueBits, cardinality), 1};
  }

  std::optional<APInt> canonicalModulus(StringRef valueClass) const override {
    // Challenge origin is orthogonal to semantic class: a sampled
    // `scalar` uses the same arithmetic modulus as a wire or pinned one.
    if (valueClass == "tg")
      return APInt(kValueBits, kP);
    if (valueClass == "scalar")
      return APInt(kValueBits, kQ);
    return std::nullopt;
  }

  std::optional<AlgebraModuli> algebraModuli() const override {
    return AlgebraModuli{kP, kQ};
  }

  std::optional<StringRef>
  constructionDigest(StringRef taggedName) const override {
    // The registry shape digests these suppliers implement — the
    // supplier's half of the realisation pair. The values are the
    // content digests of the registry entries
    // (registry/construction-profiles.json, tagged preimages
    // `zkc/profile-codec` / `zkc/profile-sponge`); a change over
    // there is a deliberate registry transition, and drifting here would
    // be caught by the pin gate refusing every sealed artifact.
    if (taggedName == "codec:tg_be8" || taggedName == "codec:ts_be8")
      return StringRef("sha256:3350aaa6e9a9a99ed351e5da7429dc552e32597e"
                       "ef3990c26e7d414b8683c8aa");
    if (taggedName == "sponge:toy_duplex")
      return StringRef("sha256:35aefee5b893ded95c3a1397e67477204f5f5371"
                       "1c9e7dc60d17efb6b2e26407");
    return std::nullopt;
  }

  const HoleSupplier *hole(StringRef contractDigest) const override {
    if (contractDigest == sigmaCommit.contractDigest())
      return &sigmaCommit;
    if (contractDigest == sigmaResponse.contractDigest())
      return &sigmaResponse;
    return nullptr;
  }

private:
  ToyCodec tg{"tg_be8", 8};
  ToyCodec ts{"ts_be8", 8};
  ToyDuplexSupplier duplex;
  ToySigmaCommit sigmaCommit;
  ToySigmaResponse sigmaResponse;
};

/// The wrong algebra behind the same boundary: z+1 survives every
/// boundary check (in range, canonical) and dies exactly where it must
/// — at the verifier's equation.
class CheatSigmaResponse : public ToySigmaResponse {
public:
  llvm::Error fill(
      ArrayRef<StringRef> params, ArrayRef<StringRef> semanticParams,
      ArrayRef<APInt> values, ArrayRef<SmallVector<uint8_t, 32>> handles,
      SmallVectorImpl<APInt> &valueResults,
      SmallVectorImpl<SmallVector<uint8_t, 32>> &handleResults) const override {
    if (llvm::Error err =
            ToySigmaResponse::fill(params, semanticParams, values, handles,
                                   valueResults, handleResults))
      return err;
    valueResults.back() =
        APInt(kValueBits, (valueResults.back().getZExtValue() + 1) % kQ);
    return llvm::Error::success();
  }
};

class ToyCheatProfile : public ToyProfile {
public:
  StringRef name() const override { return "toy-cheat"; }
  const HoleSupplier *hole(StringRef contractDigest) const override {
    if (contractDigest == cheat.contractDigest())
      return &cheat;
    return ToyProfile::hole(contractDigest);
  }

private:
  CheatSigmaResponse cheat;
};

} // namespace

const ExecutionProfile &toyProfile() {
  static ToyProfile profile;
  return profile;
}

const ExecutionProfile &toyCheatProfile() {
  static ToyCheatProfile profile;
  return profile;
}

} // namespace interpreter
} // namespace zkc
