//===- Plonky3Profile.cpp - native real-profile suppliers -------*- C++ -*-===//
// The native real execution profile (docs/spec/endpoints.md §4):
// Poseidon2-16 over BabyBear and the real codecs, implemented
// natively — no proof backend enters the compiler build path. Constants
// are transliterated from the pinned upstream source (baby-bear/src/
// poseidon2.rs at the revision the replay harness's Cargo.toml names)
// and the permutation self-checks against the
// pinned known-answer test at first use: a supplier whose permutation
// drifts refuses to exist rather than deriving wrong challenges.
//
// The duplex follows the pinned DuplexChallenger semantics: width 16,
// rate 8, absorb buffering with output invalidation, length binding into
// the first capacity element on duplexing, LIFO output. The pinned
// construction hashes no domain strings — domain separation in this
// profile lives in the event schedule, not the sponge — and the iv policy
// "artifact-id" is zkc's binding layer on top: the source identity is
// absorbed before any event, which is deliberately stronger than the raw
// upstream transcript (the upstream verifier does not bind the AIR; the
// replay slice records that gap as residual trust).
//===----------------------------------------------------------------------===//

#include "zkc/Interpreter/ExecutionProfile.h"

#include "llvm/Support/ErrorHandling.h"

using namespace llvm;

namespace zkc {
namespace interpreter {

namespace {

//===-- BabyBear canonical arithmetic -------------------------------------===//

constexpr uint64_t kBB = 2013265921; // 2^31 - 2^27 + 1

uint64_t bbAdd(uint64_t a, uint64_t b) { return (a + b) % kBB; }
uint64_t bbSub(uint64_t a, uint64_t b) { return (a + kBB - b % kBB) % kBB; }
uint64_t bbMul(uint64_t a, uint64_t b) { return (a * b) % kBB; }

uint64_t bbPow(uint64_t base, uint64_t exp) {
  uint64_t result = 1;
  base %= kBB;
  while (exp) {
    if (exp & 1)
      result = bbMul(result, base);
    base = bbMul(base, base);
    exp >>= 1;
  }
  return result;
}

uint64_t bbSbox(uint64_t x) { // x^7, alpha = 7 at n = 31
  uint64_t x2 = bbMul(x, x);
  uint64_t x3 = bbMul(x2, x);
  return bbMul(bbMul(x3, x3), x);
}

/// Multiplication by 2^-k: the internal diagonal is spelled in halvings.
uint64_t bbDiv2exp(uint64_t x, unsigned k) {
  // inv2 = (p + 1) / 2.
  return bbMul(x, bbPow((kBB + 1) / 2, k));
}

//===-- Poseidon2-16 constants (pinned source, canonical values) ----------===//

constexpr uint64_t kRcExternalInitial[4][16] = {
    {0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef,
     0x72c246de, 0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271,
     0x0f49b029, 0x47872fe1, 0x221e2e36, 0x1ab7202e},
    {0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da,
     0x5b9ad32e, 0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334,
     0x7507d8b4, 0x6ceeb94e, 0x52eb6ba2, 0x50642905},
    {0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a,
     0x15737c9c, 0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4,
     0x3502aaa0, 0x0f475fd7, 0x29fbda49, 0x018afffd},
    {0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c,
     0x6e5f250a, 0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913,
     0x2cfe5f15, 0x023427ca, 0x2cc78315, 0x1e36ea47}};

constexpr uint64_t kRcExternalFinal[4][16] = {
    {0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af,
     0x13271d3f, 0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26,
     0x2c589c9e, 0x20bd37a7, 0x6a2d3d10, 0x20523767},
    {0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d,
     0x2c46a83f, 0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f,
     0x170eaf81, 0x5a9c314f, 0x49a12590, 0x35ec52a1},
    {0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad,
     0x0cbec0ea, 0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde,
     0x1e3afb3e, 0x296fb027, 0x45e1547b, 0x4a8db2ab},
    {0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747,
     0x038a98a3, 0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481,
     0x3f93bf64, 0x644d987b, 0x3c8bcd87, 0x608758b8}};

constexpr uint64_t kRcInternal[13] = {
    0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8,
    0x4e2b1ccb, 0x61210ce0, 0x3c318939, 0x0b5b2f22, 0x2edb11d5,
    0x213effdf, 0x0cac4606, 0x241af16d};

//===-- The permutation
//----------------------------------------------------===//

/// The 4x4 kernel of the external MDS (upstream `apply_mat4`, MDSMat4).
void mat4(uint64_t x[4]) {
  uint64_t t01 = bbAdd(x[0], x[1]);
  uint64_t t23 = bbAdd(x[2], x[3]);
  uint64_t t0123 = bbAdd(t01, t23);
  uint64_t t01123 = bbAdd(t0123, x[1]);
  uint64_t t01233 = bbAdd(t0123, x[3]);
  uint64_t x0 = x[0], x2 = x[2];
  x[3] = bbAdd(t01233, bbAdd(x0, x0));
  x[1] = bbAdd(t01123, bbAdd(x2, x2));
  x[0] = bbAdd(t01123, t01);
  x[2] = bbAdd(t01233, t23);
}

/// The external linear layer (upstream `mds_light_permutation`, width 16).
void mdsLight(uint64_t state[16]) {
  for (unsigned chunk = 0; chunk < 16; chunk += 4)
    mat4(state + chunk);
  uint64_t sums[4];
  for (unsigned k = 0; k < 4; ++k) {
    sums[k] = 0;
    for (unsigned j = 0; j < 16; j += 4)
      sums[k] = bbAdd(sums[k], state[j + k]);
  }
  for (unsigned i = 0; i < 16; ++i)
    state[i] = bbAdd(state[i], sums[i % 4]);
}

/// The internal diagonal multiplication (upstream
/// `BabyBearInternalLayerParameters::internal_layer_mat_mul`), with
/// state[0] handled by the caller. V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4,
/// 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27].
void internalMatMul(uint64_t state[16], uint64_t sum) {
  state[1] = bbAdd(state[1], sum);
  state[2] = bbAdd(bbAdd(state[2], state[2]), sum);
  state[3] = bbAdd(bbDiv2exp(state[3], 1), sum);
  state[4] = bbAdd(sum, bbMul(state[4], 3));
  state[5] = bbAdd(sum, bbMul(state[5], 4));
  state[6] = bbSub(sum, bbDiv2exp(state[6], 1));
  state[7] = bbSub(sum, bbMul(state[7], 3));
  state[8] = bbSub(sum, bbMul(state[8], 4));
  state[9] = bbAdd(bbDiv2exp(state[9], 8), sum);
  state[10] = bbAdd(bbDiv2exp(state[10], 2), sum);
  state[11] = bbAdd(bbDiv2exp(state[11], 3), sum);
  state[12] = bbAdd(bbDiv2exp(state[12], 27), sum);
  state[13] = bbSub(sum, bbDiv2exp(state[13], 8));
  state[14] = bbSub(sum, bbDiv2exp(state[14], 4));
  state[15] = bbSub(sum, bbDiv2exp(state[15], 27));
}

void poseidon2Permute(uint64_t state[16]) {
  mdsLight(state);
  for (unsigned round = 0; round < 4; ++round) {
    for (unsigned i = 0; i < 16; ++i)
      state[i] = bbSbox(bbAdd(state[i], kRcExternalInitial[round][i]));
    mdsLight(state);
  }
  for (unsigned round = 0; round < 13; ++round) {
    uint64_t s0 = bbSbox(bbAdd(state[0], kRcInternal[round]));
    uint64_t partSum = 0;
    for (unsigned i = 1; i < 16; ++i)
      partSum = bbAdd(partSum, state[i]);
    uint64_t fullSum = bbAdd(partSum, s0);
    state[0] = bbSub(partSum, s0);
    internalMatMul(state, fullSum);
  }
  for (unsigned round = 0; round < 4; ++round) {
    for (unsigned i = 0; i < 16; ++i)
      state[i] = bbSbox(bbAdd(state[i], kRcExternalFinal[round][i]));
    mdsLight(state);
  }
}

/// The pinned known-answer test (baby-bear/src/poseidon2.rs,
/// `test_default_babybear_poseidon2_width_16`). A supplier whose
/// permutation cannot reproduce it refuses to exist. The permutation is
/// process-immutable, so one reproduction per process suffices.
void selfCheck() {
  static const bool once = [] {
    uint64_t state[16] = {894848333, 1437655012, 1200606629, 1690012884,
                          71131202,  1749206695, 1717947831, 120589055,
                          19776022,  42382981,   1831865506, 724844064,
                          171220207, 1299207443, 227047920,  1783754913};
    constexpr uint64_t expected[16] = {
        516096821,  90309867,   1101817252, 1660784290, 360715097,  1789519026,
        1788910906, 563338433,  319524748,  1741414159, 1650859320, 894311162,
        1121347488, 1692793758, 1052633829, 1344246938};
    poseidon2Permute(state);
    for (unsigned i = 0; i < 16; ++i)
      if (state[i] != expected[i])
        llvm::report_fatal_error(
            "plonky3 profile self-check failed: the native Poseidon2-16 "
            "permutation does not reproduce the pinned known-answer test");
    return true;
  }();
  (void)once;
}

//===-- The duplex
//---------------------------------------------------------===//

/// The pinned DuplexChallenger semantics (width 16, rate 8): buffered
/// absorbs invalidate outputs; duplexing overwrites the first `len` state
/// slots, binds `len` into the first capacity element, permutes, and
/// refills the output buffer from the rate slots; samples pop LIFO.
class DuplexState final : public SpongeState {
public:
  explicit DuplexState(StringRef sourceIdentity = StringRef()) {
    selfCheck();
    // zkc's iv policy: the source identity commits the transcript to the
    // sealed protocol before any event. The identity string is absorbed
    // as rate-many elements derived from its bytes, reduced canonically.
    // An empty identity absorbs nothing: raw construction, for replay
    // validation.
    SmallVector<uint8_t> framed;
    for (unsigned i = 0; i < sourceIdentity.size(); i += 4) {
      uint64_t word = 0;
      for (unsigned j = 0; j < 4 && i + j < sourceIdentity.size(); ++j)
        word = (word << 8) | (uint8_t)sourceIdentity[i + j];
      appendElement(framed, word % kBB);
    }
    absorb(framed);
  }

  void absorb(ArrayRef<uint8_t> framed) override {
    assert(framed.size() % 4 == 0 && "symbols are 4-byte field elements");
    for (unsigned i = 0; i < framed.size(); i += 4) {
      uint64_t element = ((uint64_t)framed[i] << 24) |
                         ((uint64_t)framed[i + 1] << 16) |
                         ((uint64_t)framed[i + 2] << 8) | framed[i + 3];
      outputBuffer.clear();
      inputBuffer.push_back(element % kBB);
      if (inputBuffer.size() == 8)
        duplexing();
    }
  }

  SmallVector<uint8_t, 32> squeeze(StringRef domain,
                                   unsigned nSymbols) override {
    // The pinned construction hashes no domain strings; the declared
    // domain stays schedule metadata (see the file header).
    (void)domain;
    SmallVector<uint8_t, 32> out;
    for (unsigned k = 0; k < nSymbols; ++k) {
      if (!inputBuffer.empty() || outputBuffer.empty())
        duplexing();
      uint64_t element = outputBuffer.pop_back_val();
      appendElement(out, element);
    }
    return out;
  }

private:
  static void appendElement(SmallVectorImpl<uint8_t> &out, uint64_t element) {
    out.push_back((element >> 24) & 0xff);
    out.push_back((element >> 16) & 0xff);
    out.push_back((element >> 8) & 0xff);
    out.push_back(element & 0xff);
  }

  void duplexing() {
    unsigned len = inputBuffer.size();
    for (unsigned i = 0; i < len; ++i)
      state[i] = inputBuffer[i];
    inputBuffer.clear();
    if (len > 0) {
      // An absorb is made prefix-free: the rate slots the inputs did not
      // overwrite are zeroed, and the absorbed length binds into the
      // first capacity element — length and zero-padding cannot collide.
      // An empty buffer is a squeeze: the rate stays untouched.
      for (unsigned i = len; i < 8; ++i)
        state[i] = 0;
      state[8] = bbAdd(state[8], len);
    }
    poseidon2Permute(state);
    outputBuffer.clear();
    for (unsigned i = 0; i < 8; ++i)
      outputBuffer.push_back(state[i]);
  }

  uint64_t state[16] = {};
  SmallVector<uint64_t, 8> inputBuffer;
  SmallVector<uint64_t, 8> outputBuffer;
};

} // namespace

std::unique_ptr<SpongeState> rawPlonky3Duplex() {
  return std::make_unique<DuplexState>();
}

namespace {

class LenpadSupplier : public SpongeSupplier {
public:
  StringRef construction() const override {
    return "plonky3_bb31_poseidon2_w16_r8_lenpad";
  }
  StringRef ivPolicy() const override { return "artifact-id"; }
  std::unique_ptr<SpongeState> init(StringRef sourceIdentity) const override {
    return std::make_unique<DuplexState>(sourceIdentity);
  }
};

/// The value-faithful iv policy (evaluation/upstream/plonky3-replay/README.md):
/// a fresh zero-state duplex, exactly the counterpart verifier's own start. The
/// identity binding zkc's artifact-id policy adds is deliberately absent,
/// because matching the counterpart exactly is what this policy is for. The
/// artifact records which policy it uses, so the weaker binding is a stated
/// property of the artifact rather than an implicit one.
class ZeroIvLenpadSupplier : public SpongeSupplier {
public:
  StringRef construction() const override {
    return "plonky3_bb31_poseidon2_w16_r8_lenpad";
  }
  StringRef ivPolicy() const override { return "zero"; }
  std::unique_ptr<SpongeState> init(StringRef sourceIdentity) const override {
    (void)sourceIdentity;
    auto state = std::make_unique<DuplexState>(StringRef(""));
    return state;
  }
};

//===-- Codecs
//-------------------------------------------------------------===//

uint64_t element(ArrayRef<uint8_t> bytes, unsigned index) {
  unsigned base = index * 4;
  return ((uint64_t)bytes[base] << 24) | ((uint64_t)bytes[base + 1] << 16) |
         ((uint64_t)bytes[base + 2] << 8) | bytes[base + 3];
}

/// The shared spine of the BabyBear codecs: the wire is canonical 32-bit
/// big-endian words, the framing is the wire form, and squeeze
/// derivation reduces one squeezed element into the declared space. Each
/// codec keeps only its shape: width, symbol count, decode, and framing.
class Bb31WordCodec : public CodecSupplier {
public:
  bool wireCanonical(ArrayRef<uint8_t> bytes) const override {
    for (unsigned word = 0; word < bytes.size() / 4; ++word)
      if (element(bytes, word) >= kBB)
        return false;
    return true;
  }

  void encodeWire(const APInt &value,
                  SmallVectorImpl<uint8_t> &out) const override {
    // The framing is the wire form (32-bit big-endian words), so the
    // write direction round-trips and emits canonically by sharing it.
    absorbFraming(value, out);
  }

  APInt squeezeDerive(ArrayRef<uint8_t> symbols,
                      const APInt &space) const override {
    return APInt(kValueBits, element(symbols, 0)).urem(space);
  }
};

/// BabyBear^4 as one machine value: four canonical coordinates packed in
/// 32-bit limbs, least-significant coordinate first.
class Ext4TupleCodec : public Bb31WordCodec {
public:
  StringRef name() const override { return "plonky3_bb31_ext4_tuple"; }
  /// Four 32-bit coordinates travel as one value.
  unsigned framingBits() const override { return 128; }
  unsigned wireWidth() const override { return 16; }
  unsigned squeezeSymbols() const override { return 4; }

  APInt decodeWire(ArrayRef<uint8_t> bytes) const override {
    APInt value(kValueBits, 0);
    for (unsigned coord = 0; coord < 4; ++coord)
      value.insertBits(APInt(32, element(bytes, coord)), coord * 32);
    return value;
  }

  void absorbFraming(const APInt &value,
                     SmallVectorImpl<uint8_t> &out) const override {
    for (unsigned coord = 0; coord < 4; ++coord) {
      uint64_t word = value.extractBitsAsZExtValue(32, coord * 32);
      out.push_back((word >> 24) & 0xff);
      out.push_back((word >> 16) & 0xff);
      out.push_back((word >> 8) & 0xff);
      out.push_back(word & 0xff);
    }
  }

  APInt squeezeDerive(ArrayRef<uint8_t> symbols,
                      const APInt &space) const override {
    // Tuple bijection: one squeezed element per coordinate, exact over
    // the declared space |F|^4 — no reduction happens here.
    (void)space;
    APInt value(kValueBits, 0);
    for (unsigned coord = 0; coord < 4; ++coord)
      value.insertBits(APInt(32, element(symbols, coord)), coord * 32);
    return value;
  }
};

/// One canonical element on the wire; squeeze derivation keeps the low
/// bits of one squeezed element (the space is a power of two, so the mask
/// and the modulus agree, as in the pinned `sample_bits`).
class LowBitsCodec : public Bb31WordCodec {
public:
  StringRef name() const override { return "plonky3_bb31_low_bits"; }
  /// One 32-bit word travels as one value, so the framing carries 32
  /// bits and says so. Inheriting the 64-bit default let a wider value
  /// absorb as its low half — two distinct constants entering the
  /// transcript identically, which is the collision the width gate
  /// exists to refuse.
  unsigned framingBits() const override { return 32; }
  unsigned wireWidth() const override { return 4; }
  unsigned squeezeSymbols() const override { return 1; }

  APInt decodeWire(ArrayRef<uint8_t> bytes) const override {
    return APInt(kValueBits, element(bytes, 0));
  }

  void absorbFraming(const APInt &value,
                     SmallVectorImpl<uint8_t> &out) const override {
    uint64_t word = value.getZExtValue();
    out.push_back((word >> 24) & 0xff);
    out.push_back((word >> 16) & 0xff);
    out.push_back((word >> 8) & 0xff);
    out.push_back(word & 0xff);
  }
};

/// An eight-element digest (a Merkle root or cap row): wire and framing
/// only — nothing squeezes a digest.
class Digest8Codec : public Bb31WordCodec {
public:
  StringRef name() const override { return "plonky3_bb31_digest8"; }
  unsigned wireWidth() const override { return 32; }
  unsigned squeezeSymbols() const override { return 1; }
  /// Eight 32-bit limbs: this codec carries the whole digest, which is the
  /// point of it, so it frames far past the algebra's 64-bit domain.
  unsigned framingBits() const override { return 256; }

  APInt decodeWire(ArrayRef<uint8_t> bytes) const override {
    APInt value(kValueBits, 0);
    for (unsigned word = 0; word < 8; ++word)
      value.insertBits(APInt(32, element(bytes, word)), word * 32);
    return value;
  }

  void absorbFraming(const APInt &value,
                     SmallVectorImpl<uint8_t> &out) const override {
    for (unsigned word = 0; word < 8; ++word) {
      uint64_t limb = value.extractBitsAsZExtValue(32, word * 32);
      out.push_back((limb >> 24) & 0xff);
      out.push_back((limb >> 16) & 0xff);
      out.push_back((limb >> 8) & 0xff);
      out.push_back(limb & 0xff);
    }
  }
};

//===-- The profile
//--------------------------------------------------------===//

class Plonky3Profile : public ExecutionProfile {
public:
  StringRef name() const override { return "plonky3"; }

  const CodecSupplier *codec(StringRef codecName) const override {
    if (codecName == ext4.name())
      return &ext4;
    if (codecName == lowBits.name())
      return &lowBits;
    if (codecName == digest8.name())
      return &digest8;
    return nullptr;
  }

  const SpongeSupplier *sponge(StringRef construction,
                               StringRef ivPolicy) const override {
    if (construction == lenpad.construction() && ivPolicy == lenpad.ivPolicy())
      return &lenpad;
    if (construction == zeroIv.construction() && ivPolicy == zeroIv.ivPolicy())
      return &zeroIv;
    return nullptr;
  }

  std::optional<SamplingPlan> admitSampling(StringRef rule, StringRef count,
                                            StringRef space) const override {
    uint64_t draws;
    if (count.getAsInteger(10, draws) || draws < 1)
      return std::nullopt;
    if (rule != "uniform" && rule != "uniform_independent")
      return std::nullopt;
    if (rule == "uniform" && draws != 1)
      return std::nullopt;
    // Arbitrary-precision cardinality: |F|^4 for the extension space.
    unsigned bits = APInt::getSufficientBitsNeeded(space, 10);
    if (bits == 0 || bits > kValueBits)
      return std::nullopt;
    APInt cardinality(kValueBits, space, 10);
    if (cardinality.ult(APInt(kValueBits, 2)))
      return std::nullopt;
    return SamplingPlan{cardinality, draws};
  }

  std::optional<APInt> canonicalModulus(StringRef valueClass) const override {
    // Per-coordinate canonicality is checked by the codecs at decode;
    // the packed representation has no single modulus to compare against,
    // so classes here declare none at the machine level.
    (void)valueClass;
    return std::nullopt;
  }

  std::optional<StringRef>
  constructionDigest(StringRef taggedName) const override {
    // Filled per entry as the registry's construction digests; computed
    // by the loader and pinned by seal — the executor compares, never
    // recomputes. Values are the registry entries' content digests.
    if (taggedName == "sponge:plonky3_bb31_poseidon2_w16_r8_lenpad")
      return StringRef("sha256:961fc67e87a582f6d38f0c82047af0480269d340"
                       "e1c9714fced6163e62984efc");
    if (taggedName == "codec:plonky3_bb31_ext4_tuple")
      return StringRef("sha256:cb6f0f7790e47814634648f59d467917e13cdb4f"
                       "d7151d8640d8f2f4b6821a5b");
    if (taggedName == "codec:plonky3_bb31_low_bits")
      return StringRef("sha256:dbe9226c119680601f413ad689abf1bd77784f72"
                       "a44e16ef8a0b7cb714d8641f");
    if (taggedName == "codec:plonky3_bb31_digest8")
      return StringRef("sha256:a3425c10251b787fbef3da60b57a7eedc8e889ff"
                       "b46219eb26c70109e6dacb2d");
    return std::nullopt;
  }

private:
  Ext4TupleCodec ext4;
  LowBitsCodec lowBits;
  Digest8Codec digest8;
  LenpadSupplier lenpad;
  ZeroIvLenpadSupplier zeroIv;
};

} // namespace

const ExecutionProfile &plonky3Profile() {
  static Plonky3Profile profile;
  return profile;
}

} // namespace interpreter
} // namespace zkc
