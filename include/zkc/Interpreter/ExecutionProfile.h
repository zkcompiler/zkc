//===- ExecutionProfile.h - vocabulary suppliers for execution --*- C++ -*-===//
// The executor's pluggable axis. A profile is a closed set of vocabulary
// suppliers — codec, sponge, sampling — behind one interface; the toy
// profile is the first supplier set, not a special case. Ops are never the
// pluggable axis: dispatch stays central in the interpreter, so the
// refusal surface keeps its diagnostic ids in one place
// (docs/spec/endpoints.md §4).
//
// A supplier that is absent is a "cannot judge" refusal naming the missing
// supplier, never a verdict. Nothing here reaches artifact identity: which
// profile executes an artifact is a run fact.
//===----------------------------------------------------------------------===//

#ifndef ZKC_INTERPRETER_EXECUTIONPROFILE_H
#define ZKC_INTERPRETER_EXECUTIONPROFILE_H

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

#include <memory>
#include <optional>

namespace zkc {
namespace interpreter {

/// The machine value width. One fixed width so comparisons and arithmetic
/// compose without per-site alignment; wide enough for an eight-word digest
/// or a degree-four extension element with headroom. The per-class
/// canonical-width discipline arrives with the real-profile suppliers;
/// until then every supplier speaks this width.
constexpr unsigned kValueBits = 512;

/// One codec, all three of its operations. The registry today declares
/// only the squeeze-derivation shape; decode width and absorb framing are
/// supplier facts until the registry schema grows them
/// (docs/spec/endpoints.md §4).
class CodecSupplier {
public:
  virtual ~CodecSupplier() = default;
  virtual llvm::StringRef name() const = 0;
  /// Exact wire width of one encoded value, in bytes.
  virtual unsigned wireWidth() const = 0;
  /// Whether the wire bytes are the canonical encoding of a value —
  /// checked before decode, so a non-canonical proof rejects rather than
  /// silently reducing. Codecs whose class modulus lives with the profile
  /// (the toy pair) return true and leave the range check to the caller.
  virtual bool wireCanonical(llvm::ArrayRef<uint8_t> bytes) const {
    (void)bytes;
    return true;
  }
  /// Wire bytes (exactly wireWidth of them) to a machine value.
  virtual llvm::APInt decodeWire(llvm::ArrayRef<uint8_t> bytes) const = 0;
  /// A machine value to its canonical wire bytes — the write direction
  /// (docs/spec/endpoints.md §6.3). Two obligations, exercised by
  /// vectors on both legs: round-trip (decodeWire(encodeWire(v)) == v
  /// for in-range v) and canonicity (wireCanonical(encodeWire(v))), so
  /// emitted proofs are canonical by construction.
  virtual void encodeWire(const llvm::APInt &value,
                          llvm::SmallVectorImpl<uint8_t> &out) const = 0;
  /// A machine value to the symbols the sponge absorbs for it.
  virtual void absorbFraming(const llvm::APInt &value,
                             llvm::SmallVectorImpl<uint8_t> &out) const = 0;
  /// The widest value this codec frames without losing information. The
  /// default is the 64-bit domain the profile algebra computes in; a codec
  /// that carries wider values — a digest, an extension element — says so.
  /// Framing cannot refuse (it returns void), so the interpreter asks this
  /// before handing a value over: silently keeping a value's low bits would
  /// let two distinct public inputs absorb identically.
  virtual unsigned framingBits() const { return 64; }
  /// How many sponge symbols one squeeze derivation consumes — the
  /// registry's declared squeeze shape.
  virtual unsigned squeezeSymbols() const { return 1; }
  /// Squeezed sponge output to a value in a space of the given
  /// cardinality.
  virtual llvm::APInt squeezeDerive(llvm::ArrayRef<uint8_t> symbols,
                                    const llvm::APInt &space) const = 0;
};

/// A live sponge instance. The framing tags that keep absorb and squeeze
/// inputs disjoint are sponge-internal: they are load-bearing for the
/// Binding Lemma's injectivity and no caller may need to remember them.
class SpongeState {
public:
  virtual ~SpongeState() = default;
  /// An independent copy of the current state. This is the transcript
  /// peek's mechanism (docs/spec/endpoints.md §6.2): a pow_search trial
  /// runs on a clone, so the live transcript never moves.
  virtual std::unique_ptr<SpongeState> clone() const = 0;
  virtual void absorb(llvm::ArrayRef<uint8_t> framed) = 0;
  /// Yield the symbols one squeeze event provides for `nSymbols`-symbol
  /// derivation. Constructions that hash a domain use it; constructions
  /// whose pinned semantics carry no domains ignore it and say so.
  virtual llvm::SmallVector<uint8_t, 32> squeeze(llvm::StringRef domain,
                                                 unsigned nSymbols) = 0;
};

class SpongeSupplier {
public:
  virtual ~SpongeSupplier() = default;
  virtual llvm::StringRef construction() const = 0;
  virtual llvm::StringRef ivPolicy() const = 0;
  virtual std::unique_ptr<SpongeState>
  init(llvm::StringRef sourceIdentity) const = 0;
};

/// An admitted sampling shape: the exact space cardinality and how many
/// values one squeeze event yields.
struct SamplingPlan {
  llvm::APInt space;
  uint64_t count;
};

/// One prover compute-hole fill (docs/spec/endpoints.md §6.3).
/// Keyed by hole-contract content digest — the supplier's half of the
/// realisation pair, exactly as construction suppliers declare theirs.
/// Values cross the boundary as machine values; handles cross as opaque
/// byte payloads whose meaning is the supplier's own. zkc checks the
/// boundary (arity, kinds, canonicity), never the algebra inside.
class HoleSupplier {
public:
  virtual ~HoleSupplier() = default;
  /// The hole-contract content digest this supplier implements.
  virtual llvm::StringRef contractDigest() const = 0;
  /// Fill the hole: the cited contract's static parameters, then its
  /// semantic parameters, each in that contract's lexical name order
  /// (admission holds both bindings to the contract, so a supplier may
  /// index them positionally); then operand values and handle payloads in
  /// declared order (each list in its own order), results likewise. A
  /// semantic parameter is a content reference naming material the supplier
  /// is expected to hold — it is passed, never resolved here: this
  /// interface knows identities, not stores. Returning an error is a defect
  /// of the fill, not a proof verdict.
  virtual llvm::Error
  fill(llvm::ArrayRef<llvm::StringRef> params,
       llvm::ArrayRef<llvm::StringRef> semanticParams,
       llvm::ArrayRef<llvm::APInt> values,
       llvm::ArrayRef<llvm::SmallVector<uint8_t, 32>> handles,
       llvm::SmallVectorImpl<llvm::APInt> &valueResults,
       llvm::SmallVectorImpl<llvm::SmallVector<uint8_t, 32>> &handleResults)
      const = 0;
};

/// One typed check operand as the supplier sees it: the payload class
/// and the operand's elements — one for a scalar reference, `count` for
/// a counted one. Flattening is the executor's; the supplier validates
/// the element counts against its own contract shape (the atomic check
/// owns its shape refusals, docs/spec/carrier.md §7).
struct CheckOperandView {
  llvm::StringRef valueClass;
  llvm::ArrayRef<llvm::APInt> values;
};

/// One opaque-check executor (docs/spec/endpoints.md §3): the
/// executable half of a CheckContract, keyed by contract content
/// digest exactly as hole suppliers are. The supplier decides the
/// proposition; the executor owns the verdict channel.
class CheckSupplier {
public:
  virtual ~CheckSupplier() = default;
  /// The check-contract content digest this supplier implements.
  virtual llvm::StringRef contractDigest() const = 0;
  /// Decide the proposition over the cited static parameters and typed
  /// operands. Returns nullopt when it holds, and a message naming the
  /// failing fact when it does not — that message becomes a
  /// check_failure verdict. An error is a defect (malformed operand
  /// shape, missing internal material), a refusal and never a verdict.
  virtual llvm::Expected<std::optional<std::string>>
  decide(llvm::ArrayRef<llvm::StringRef> params,
         llvm::ArrayRef<CheckOperandView> operands) const = 0;
};

/// The transcript-peek fill (docs/spec/endpoints.md §6.2): the one
/// supplier whose operand is not a value but a trial oracle the
/// interpreter builds over a cloned sponge, so the fill can read the
/// state it grinds against without ever holding it. The supplier owns
/// the enumeration but the specification binds it: canonical ascending
/// order, least valid witness, so every conforming implementation
/// returns the same nonce. Keyed by hole-contract content digest like
/// every other fill.
class PowSearchSupplier {
public:
  virtual ~PowSearchSupplier() = default;
  /// The hole-contract content digest this supplier implements.
  virtual llvm::StringRef contractDigest() const = 0;
  /// The least candidate in [0, domainEnd) whose trial derivation is
  /// zero, or an error when the domain is exhausted — a defect of the
  /// fill, never a verdict.
  virtual llvm::Expected<llvm::APInt>
  search(const llvm::APInt &domainEnd,
         llvm::function_ref<llvm::Expected<llvm::APInt>(const llvm::APInt &)>
             trial) const = 0;
};

/// A closed supplier set. Lookups return null/nullopt for "not supplied",
/// and the interpreter turns that into the named refusal — the profile
/// never formats diagnostics itself.
class ExecutionProfile {
public:
  virtual ~ExecutionProfile() = default;
  virtual llvm::StringRef name() const = 0;
  virtual const CodecSupplier *codec(llvm::StringRef codecName) const = 0;
  virtual const SpongeSupplier *sponge(llvm::StringRef construction,
                                       llvm::StringRef ivPolicy) const = 0;
  virtual std::optional<SamplingPlan>
  admitSampling(llvm::StringRef rule, llvm::StringRef count,
                llvm::StringRef space) const = 0;
  /// The canonical modulus a value of this class must lie under, where the
  /// profile knows one. Classes without a modulus are absorbed unchecked.
  virtual std::optional<llvm::APInt>
  canonicalModulus(llvm::StringRef valueClass) const = 0;

  /// The moduli for transparent-predicate algebra: g_exp/g_mul over the
  /// group modulus, f_add/f_mul/f_neg over the field modulus. A profile
  /// that supplies none refuses every algebra op — falling back to another
  /// profile's field would be a silent wrong-field execution.
  struct AlgebraModuli {
    uint64_t group;
    uint64_t field;
  };
  virtual std::optional<AlgebraModuli> algebraModuli() const {
    return std::nullopt;
  }

  /// The registry construction digest this profile's supplier implements,
  /// for a tagged name (`sponge:<name>` / `codec:<name>`). This is the
  /// supplier's half of the realisation pair: the artifact pins the digest
  /// it was sealed against, and execution proceeds only when the two
  /// agree. Nullopt means no supplier for that construction.
  virtual std::optional<llvm::StringRef>
  constructionDigest(llvm::StringRef taggedName) const = 0;

  /// The hole supplier implementing a hole-contract content digest, or
  /// null — a profile refusal naming the digest, never a verdict. The
  /// base returns null: verifier-only profiles supply no fills.
  virtual const HoleSupplier *hole(llvm::StringRef contractDigest) const {
    (void)contractDigest;
    return nullptr;
  }

  /// The transcript-peek supplier for a hole-contract content digest, or
  /// null — the same refusal shape as `hole`. The base returns null:
  /// verifier-only profiles supply no fills.
  virtual const PowSearchSupplier *
  powSearch(llvm::StringRef contractDigest) const {
    (void)contractDigest;
    return nullptr;
  }

  /// The check supplier implementing a check-contract content digest,
  /// or null — the executor turns null into zkc-E403, the fail-closed
  /// default every unsupplied check keeps.
  virtual const CheckSupplier *check(llvm::StringRef contractDigest) const {
    (void)contractDigest;
    return nullptr;
  }
};

/// The toy profile: SHA-256 chaining duplex, big-endian 8-byte codecs, the
/// safe-prime group moduli. Semantics identical to reference/oracle/exec.py.
const ExecutionProfile &toyProfile();

/// The toy profile with a deliberately wrong response fill — a
/// boundary-conformant cheating supplier for negative conformance
/// vectors (docs/spec/endpoints.md §§4, 6.3): the derived
/// orchestration runs it honestly, and the emitted proof must be
/// rejected by the verifier's checks. Never a default; selected only
/// by name.
const ExecutionProfile &toyCheatProfile();

/// The native real profile, leg (b): Poseidon2-16 over BabyBear with the
/// pinned duplex semantics and the real codecs, self-checked against the
/// pinned known-answer test (docs/spec/endpoints.md §4).
const ExecutionProfile &plonky3Profile();

/// Select a profile by name — the one selection vocabulary, shared by
/// every driver: toy | plonky3 | toy-cheat. toy-cheat is test support
/// (the boundary-conformant cheating supplier set above), selectable
/// only by this explicit name and never a default. An unknown name is
/// an error naming the profile; callers keep only the flag.
llvm::Expected<const ExecutionProfile &> selectProfile(llvm::StringRef name);

/// A raw pinned duplex for replay validation against captured upstream
/// transcripts and for the framing corpus. An empty identity is the
/// zero-state construction with no identity binding; a non-empty one is
/// absorbed exactly as the iv policy does it — big-endian four-byte
/// chunks with a short final chunk — which is one of the framing rules
/// the corpus exists to pin.
std::unique_ptr<SpongeState>
rawPlonky3Duplex(llvm::StringRef sourceIdentity = llvm::StringRef());

} // namespace interpreter
} // namespace zkc

#endif // ZKC_INTERPRETER_EXECUTIONPROFILE_H
