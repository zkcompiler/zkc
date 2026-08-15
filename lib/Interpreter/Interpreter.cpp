//===- Interpreter.cpp - reference endpoint execution -----------*- C++ -*-===//
// The Tier-2 conformance authority. Execution semantics are supplied by an
// ExecutionProfile — a closed set of codec/sponge/sampling suppliers — and
// dispatch stays central (the in-tree precedent for a sealed interpreted
// vocabulary; the pluggable axis is the supplier, never the op).
//
// Verdicts and errors are disjoint by construction: a reject class is a
// successful execution of a bad proof; an llvm::Error is "this profile
// cannot judge this artifact", carrying a stable [zkc-E4xx] id that names
// what is missing (registry/diagnostic-allocation.json).
//===----------------------------------------------------------------------===//

#include "zkc/Interpreter/Interpreter.h"

#include "zkc/Encoding/CanonicalEncoder.h"
#include "zkc/Interpreter/ExecutionProfile.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;

namespace zkc {
namespace interpreter {

namespace {

uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) {
  return (uint64_t)((__uint128_t)a * b % m);
}

uint64_t powmod(uint64_t base, uint64_t exp, uint64_t m) {
  uint64_t result = 1 % m;
  base %= m;
  while (exp) {
    if (exp & 1)
      result = mulmod(result, base, m);
    base = mulmod(base, base, m);
    exp >>= 1;
  }
  return result;
}

llvm::APInt makeValue(uint64_t value) { return llvm::APInt(kValueBits, value); }

/// Profile algebra and the shipped codecs compute in 64 bits, while a value
/// is carried at kValueBits so that a wide class (a digest, an extension
/// element) can be represented at all. Narrowing is therefore a real
/// boundary, not a formality: the low 64 bits of two different values are
/// equal for infinitely many pairs, so a silent truncation here would let
/// two distinct public inputs absorb identically and derive the same
/// challenges — a binding collision inside the channel the seal battery
/// exists to protect. Callers ask first.
bool fitsExecutionDomain(const llvm::APInt &value) {
  return value.getActiveBits() <= 64;
}

uint64_t narrow64(const llvm::APInt &value) {
  assert(fitsExecutionDomain(value) && "caller must gate the narrowing");
  return value.getZExtValue();
}

std::string decimal(const llvm::APInt &value) {
  llvm::SmallString<40> text;
  value.toStringUnsigned(text, 10);
  return std::string(text);
}

/// The codec route for a value class: the artifact's baked map names the
/// codec, and the profile supplies its implementation. Either half
/// missing is the same refusal — no route to an executable codec.
llvm::Expected<const CodecSupplier *>
routeCodec(DictionaryAttr codecs, StringRef valueClass,
           const ExecutionProfile &profile) {
  if (!codecs)
    return llvm::createStringError("[zkc-E400] no codec route for class '" +
                                   valueClass +
                                   "': artifact carries no codec map");
  auto codec = codecs.getNamed(valueClass);
  if (!codec)
    return llvm::createStringError("[zkc-E400] no codec route for class '" +
                                   valueClass + "': artifact names no codec");
  StringRef name = cast<StringAttr>(codec->getValue()).getValue();
  const CodecSupplier *supplier = profile.codec(name);
  if (!supplier)
    return llvm::createStringError(
        "[zkc-E400] no codec route for class '" + valueClass + "': codec '" +
        name + "' has no supplier in profile '" + profile.name() + "'");
  return supplier;
}

/// The machine both endpoints share. The pin gate, the statement channel,
/// the codec route, and the transcript events are one discipline on both
/// sides of the wire; each endpoint supplies its own side's operations
/// plus one policy — whether a pin mismatch or an unbindable statement is
/// a verdict (verification executed successfully against a bad input) or
/// an error (the prover has no verdict channel; every failure there is a
/// refusal or a defect).
template <typename EndpointT> class Machine {
protected:
  Machine(oir::ArtifactOp artifact, const ExecutionProfile &profile,
          const llvm::StringMap<std::string> &statement)
      : artifact(artifact), profile(profile), statement(statement) {}

  EndpointT &endpoint() { return static_cast<EndpointT &>(*this); }

  //===-- channels --------------------------------------------------===//

  /// Pinned parameters are digest-gated before any transcript event
  /// (endpoints.md §2). The artifact pins the construction digests it was
  /// sealed against; the profile declares which digests its suppliers
  /// implement. A pinned construction with no supplier cannot be judged;
  /// a supplier implementing different bytes than the pin does not bind
  /// against this executor — the endpoint names that outcome.
  llvm::Error gateParamDigests(oir::ProgramOp program) {
    for (Attribute entry : program.getParamDigests()) {
      StringRef pin = cast<StringAttr>(entry).getValue();
      auto [taggedName, digest] = pin.split('=');
      // Row shape is ProgramOp::verify's; only digest agreement is this
      // profile's question.
      std::optional<StringRef> supplied =
          profile.constructionDigest(taggedName);
      if (!supplied)
        return fail((taggedName.starts_with("sponge:")
                         ? "[zkc-E401] pinned construction '"
                         : "[zkc-E400] pinned construction '") +
                    taggedName + "' has no supplier in profile '" +
                    profile.name() + "'");
      // A supplier implementing different bytes than the pin cannot judge
      // this artifact: a profile refusal, never a proof verdict
      // (docs/spec/endpoints.md §4).
      if (*supplied != digest)
        return fail("[zkc-E408] param_digest_mismatch at '" + taggedName +
                    "': artifact pins " + digest + ", supplier implements " +
                    *supplied);
    }
    return llvm::Error::success();
  }

  llvm::Error bindStatement(oir::ProgramOp program) {
    Block &body = program.getBody().front();
    for (auto [index, label] : llvm::enumerate(program.getStatementLabels())) {
      StringRef name = cast<StringAttr>(label).getValue();
      auto entry = statement.find(name);
      if (entry == statement.end())
        return fail("[zkc-E405] statement value '" + name + "' missing");
      BlockArgument arg = body.getArgument(index);
      auto valueClass = cast<oir::ValType>(arg.getType()).getValueClass();
      StringRef text(entry->second);
      // Arbitrary-precision statement values: an `rs` digest or an
      // extension element does not fit 64 bits. Non-decimal or oversized
      // text still cannot bind.
      if (text.empty() ||
          text.find_first_not_of("0123456789") != StringRef::npos ||
          llvm::APInt::getSufficientBitsNeeded(text, 10) > kValueBits)
        return fail("[zkc-E405] statement value '" + name + "' is not decimal");
      llvm::APInt value(kValueBits, text, 10);
      if (auto modulus = profile.canonicalModulus(valueClass))
        if (value.uge(*modulus))
          return endpoint().statementOutOfRange(name);
      env.try_emplace(arg, value);
    }
    return llvm::Error::success();
  }

  /// The codec route for a value class — shared with the static
  /// proof-size view, so execution and pricing name the same refusal.
  llvm::Expected<const CodecSupplier *> requireCodec(StringRef valueClass) {
    return routeCodec(codecs, valueClass, profile);
  }

  //===-- shared operations -----------------------------------------===//

  /// Checked value read: every operand of a verified projection is
  /// defined before use (SSA block order), so an unbound value can
  /// only come from a hand-crafted artifact — refuse it instead of
  /// silently reading zero, which could accept a bad proof.
  llvm::Expected<llvm::APInt> get(Value value) {
    auto it = env.find(value);
    if (it == env.end())
      return llvm::createStringError(
          "value has no binding: not the output of a verified "
          "projection");
    return it->second;
  }

  llvm::Error stepTranscriptInit(oir::TranscriptInitOp init) {
    const SpongeSupplier *supplier =
        profile.sponge(init.getSponge(), init.getIv());
    if (!supplier)
      return fail("[zkc-E401] sponge construction '" + init.getSponge() +
                  "' with iv policy '" + init.getIv() +
                  "' has no supplier in profile '" + profile.name() + "'");
    // The IV commits the transcript to the sealed protocol executed.
    sponge = supplier->init(artifact.getSource());
    return llvm::Error::success();
  }

  llvm::Error stepAbsorb(oir::AbsorbOp absorb) {
    auto valueClass =
        cast<oir::ValType>(absorb.getValue().getType()).getValueClass();
    llvm::Expected<const CodecSupplier *> codec = requireCodec(valueClass);
    if (!codec)
      return codec.takeError();
    llvm::Expected<llvm::APInt> value = get(absorb.getValue());
    if (!value)
      return value.takeError();
    SmallVector<uint8_t> framed;
    if (value->getActiveBits() > (*codec)->framingBits())
      return fail(
          "[zkc-E411] value needs " + std::to_string(value->getActiveBits()) +
          " bits; the codec for class '" + valueClass + "' frames at most " +
          std::to_string((*codec)->framingBits()));
    (*codec)->absorbFraming(*value, framed);
    sponge->absorb(framed);
    return llvm::Error::success();
  }

  llvm::Error stepSqueeze(oir::SqueezeOp squeeze) {
    llvm::Expected<const CodecSupplier *> codec =
        requireCodec(squeeze.getPayloadClass());
    if (!codec)
      return codec.takeError();
    // The space string is the exact cardinality |C| (zkc-E139).
    std::optional<SamplingPlan> plan = profile.admitSampling(
        squeeze.getRule(), squeeze.getCount(), squeeze.getSpace());
    if (!plan)
      return fail("[zkc-E402] sampling shape at '" + squeeze.getLabel() +
                  "' (rule '" + squeeze.getRule() + "', count " +
                  squeeze.getCount() + ", space " + squeeze.getSpace() +
                  ") has no supplier in profile '" + profile.name() + "'");
    // One event, `count` draws. A vector event's challenge-log entry
    // joins its draws with '|', so one vector event can never be
    // confused with `count` scalar events. The log is the Fiat-Shamir
    // erasure's witness: the prover's replica squeeze must equal the
    // verifier's, and the challenge log is how a record proves it did.
    // Whether the drawn value binds to the SSA result is the
    // endpoint's policy.
    std::string entry;
    llvm::APInt lastValue(kValueBits, 0);
    for (uint64_t draw = 0; draw < plan->count; ++draw) {
      SmallVector<uint8_t, 32> symbols =
          sponge->squeeze(squeeze.getDomain(), (*codec)->squeezeSymbols());
      lastValue = (*codec)->squeezeDerive(symbols, plan->space);
      entry += (draw ? "|" : "") + decimal(lastValue);
    }
    endpoint().bindSqueeze(squeeze.getVal(), lastValue, plan->count);
    challenges.push_back(entry);
    return llvm::Error::success();
  }

  llvm::Error stepConstant(oir::ConstantOp constant) {
    uint64_t value;
    if (StringRef(constant.getValue()).getAsInteger(10, value))
      return fail("[zkc-E406] constant is not decimal");
    env.try_emplace(constant.getVal(), makeValue(value));
    return llvm::Error::success();
  }

  //===-- outcomes ---------------------------------------------------===//

  llvm::Error fail(const llvm::Twine &message) {
    return llvm::createStringError(message);
  }

  template <typename T> llvm::Expected<T> fail(const llvm::Twine &message) {
    return llvm::createStringError(message);
  }

  oir::ArtifactOp artifact;
  const ExecutionProfile &profile;
  const llvm::StringMap<std::string> &statement;
  DictionaryAttr codecs;
  llvm::DenseMap<Value, llvm::APInt> env;
  std::unique_ptr<SpongeState> sponge;
  std::vector<std::string> challenges;
};

class Execution : public Machine<Execution> {
public:
  Execution(oir::ArtifactOp artifact, const ExecutionProfile &profile,
            const llvm::StringMap<std::string> &statement,
            ArrayRef<uint8_t> proof)
      : Machine(artifact, profile, statement), proof(proof) {}

  llvm::Expected<ExecutionResult> run() {
    auto program = *artifact.getBody().getOps<oir::ProgramOp>().begin();
    if (auto baked = program.getCodecs())
      codecs = *baked;
    if (llvm::Error error = gateParamDigests(program))
      return std::move(error);
    if (verdict)
      return ExecutionResult{*verdict, challenges, diag};
    if (llvm::Error error = bindStatement(program))
      return std::move(error);
    // A statement that failed to bind is already the verdict; stepping
    // the program would let a later reject overwrite it (and would
    // read arguments the failed binding left unbound).
    if (verdict)
      return ExecutionResult{*verdict, challenges, diag};

    for (Operation &op : program.getBody().front()) {
      llvm::Error error = step(&op);
      if (error)
        return std::move(error);
      if (verdict)
        return ExecutionResult{*verdict, challenges, diag};
    }
    return ExecutionResult{"accept", challenges, ""};
  }

private:
  friend Machine<Execution>;

  //===-- endpoint policy -------------------------------------------===//

  /// Statements are the public-binding channel; a value that does not
  /// bind is a public_binding_failure, not a structural ABI defect
  /// (endpoints.md §4).
  llvm::Error statementOutOfRange(StringRef name) {
    reject("public_binding_failure",
           "statement value '" + name + "' out of range");
    return llvm::Error::success();
  }

  /// A vector event's SSA value stays unbound: no minted contract
  /// consumes one yet, and a crafted artifact reading it hits the
  /// unbound-value refusal instead of a silently invented
  /// representation.
  void bindSqueeze(Value val, const llvm::APInt &value, uint64_t count) {
    if (count == 1)
      env.try_emplace(val, value);
  }

  //===-- one operation ---------------------------------------------===//

  /// The algebra moduli, resolved once. Absent means every algebra op
  /// refuses — computing in a field the profile never declared would be
  /// a silent wrong-field execution.
  std::optional<ExecutionProfile::AlgebraModuli> algebra =
      profile.algebraModuli();

  llvm::Error requireAlgebra(StringRef opName) {
    if (algebra)
      return llvm::Error::success();
    return fail("[zkc-E404] algebra op '" + opName +
                "' has no moduli in profile '" + profile.name() + "'");
  }

  /// Checked two-operand read-compute-bind: the one place the checked
  /// read is sequenced (an llvm::Expected must be examined before the
  /// next one is created, or an early error aborts a checked build).
  /// The computation stays 64-bit; an operand that does not fit refuses
  /// rather than narrowing (see narrow64).
  llvm::Error binary(Value out, Value lhsValue, Value rhsValue,
                     llvm::function_ref<uint64_t(uint64_t, uint64_t)> fn) {
    llvm::Expected<llvm::APInt> lhs = get(lhsValue);
    if (!lhs)
      return lhs.takeError();
    llvm::Expected<llvm::APInt> rhs = get(rhsValue);
    if (!rhs)
      return rhs.takeError();
    if (!fitsExecutionDomain(*lhs) || !fitsExecutionDomain(*rhs))
      return fail("[zkc-E411] algebra operand needs more than 64 bits; this "
                  "profile computes on 64-bit values");
    env.insert_or_assign(out, makeValue(fn(narrow64(*lhs), narrow64(*rhs))));
    return llvm::Error::success();
  }

  llvm::Error step(Operation *op) {
    return llvm::TypeSwitch<Operation *, llvm::Error>(op)
        .Case<oir::TranscriptInitOp>([&](oir::TranscriptInitOp init) {
          return stepTranscriptInit(init);
        })
        .Case<oir::AbsorbOp>(
            [&](oir::AbsorbOp absorb) { return stepAbsorb(absorb); })
        .Case<oir::ReadOp>([&](oir::ReadOp read) -> llvm::Error {
          llvm::Expected<const CodecSupplier *> codec =
              requireCodec(read.getPayloadClass());
          if (!codec)
            return codec.takeError();
          unsigned width = (*codec)->wireWidth();
          if (cursor + width > proof.size()) {
            reject("abi_decode_failure",
                   "proof stream underrun at '" + read.getLabel() + "'");
            return llvm::Error::success();
          }
          // Canonical-or-reject: a non-canonical wire value is a bad
          // proof, never an implementation choice. Packed layouts check
          // per word in the codec; scalar classes check against the
          // profile's modulus.
          if (!(*codec)->wireCanonical(proof.slice(cursor, width))) {
            reject("abi_decode_failure",
                   "non-canonical value at '" + read.getLabel() + "'");
            return llvm::Error::success();
          }
          llvm::APInt value = (*codec)->decodeWire(proof.slice(cursor, width));
          cursor += width;
          if (auto modulus = profile.canonicalModulus(read.getPayloadClass()))
            if (value.uge(*modulus)) {
              reject("abi_decode_failure",
                     "non-canonical value at '" + read.getLabel() + "'");
              return llvm::Error::success();
            }
          env.try_emplace(read.getVal(), value);
          return llvm::Error::success();
        })
        .Case<oir::SqueezeOp>(
            [&](oir::SqueezeOp squeeze) { return stepSqueeze(squeeze); })
        .Case<oir::ConstantOp>(
            [&](oir::ConstantOp constant) { return stepConstant(constant); })
        .Case<oir::GExpOp>([&](oir::GExpOp gExp) -> llvm::Error {
          if (llvm::Error error = requireAlgebra("g_exp"))
            return error;
          return binary(gExp.getVal(), gExp.getLhs(), gExp.getRhs(),
                        [&](uint64_t l, uint64_t r) {
                          return powmod(l, r, algebra->group);
                        });
        })
        .Case<oir::GMulOp>([&](oir::GMulOp gMul) -> llvm::Error {
          if (llvm::Error error = requireAlgebra("g_mul"))
            return error;
          return binary(gMul.getVal(), gMul.getLhs(), gMul.getRhs(),
                        [&](uint64_t l, uint64_t r) {
                          return mulmod(l, r, algebra->group);
                        });
        })
        .Case<oir::FAddOp>([&](oir::FAddOp fAdd) -> llvm::Error {
          // Operands reduce before the sum: pinned constants are decimal
          // uint64 with no range gate (only wire reads are canonical-or-
          // reject), and the oracle's exact-integer sum must be matched
          // on every representable input, not only canonical ones.
          if (llvm::Error error = requireAlgebra("f_add"))
            return error;
          return binary(fAdd.getVal(), fAdd.getLhs(), fAdd.getRhs(),
                        [&](uint64_t l, uint64_t r) {
                          uint64_t field = algebra->field;
                          return (l % field + r % field) % field;
                        });
        })
        .Case<oir::FMulOp>([&](oir::FMulOp fMul) -> llvm::Error {
          if (llvm::Error error = requireAlgebra("f_mul"))
            return error;
          return binary(fMul.getVal(), fMul.getLhs(), fMul.getRhs(),
                        [&](uint64_t l, uint64_t r) {
                          return mulmod(l, r, algebra->field);
                        });
        })
        .Case<oir::FNegOp>([&](oir::FNegOp fNeg) -> llvm::Error {
          if (llvm::Error error = requireAlgebra("f_neg"))
            return error;
          llvm::Expected<llvm::APInt> value = get(fNeg.getOperand());
          if (!value)
            return value.takeError();
          if (!fitsExecutionDomain(*value))
            return fail("[zkc-E411] algebra operand needs more than 64 bits; "
                        "this profile computes on 64-bit values");
          uint64_t field = algebra->field;
          env.insert_or_assign(
              fNeg.getVal(),
              makeValue((field - narrow64(*value) % field) % field));
          return llvm::Error::success();
        })
        .Case<oir::AssertEqOp>([&](oir::AssertEqOp assertEq) -> llvm::Error {
          llvm::Expected<llvm::APInt> lhs = get(assertEq.getLhs());
          if (!lhs)
            return lhs.takeError();
          llvm::Expected<llvm::APInt> rhs = get(assertEq.getRhs());
          if (!rhs)
            return rhs.takeError();
          // Fixed-width equality: the comparison is exact over the typed
          // value, independent of any supplier's representation.
          if (*lhs != *rhs)
            reject("check_failure",
                   "check '" + assertEq.getLabel() + "' failed");
          return llvm::Error::success();
        })
        .Case<oir::CheckCallOp>([&](oir::CheckCallOp call) -> llvm::Error {
          return fail("[zkc-E403] opaque check kind '" + call.getKind() +
                      "' has no executable contract in profile '" +
                      profile.name() + "'");
        })
        .Case<oir::ExpectEndOp>([&](oir::ExpectEndOp) -> llvm::Error {
          if (cursor != proof.size())
            reject("proof_trailing_data", "proof stream not exhausted");
          return llvm::Error::success();
        })
        .Case<oir::DecideOp>([&](oir::DecideOp) -> llvm::Error {
          return llvm::Error::success();
        })
        .Default([&](Operation *other) -> llvm::Error {
          // Unreachable through an identity-valid artifact: the canonical
          // encoder refuses foreign operations at minting, so this arm is
          // defense in depth, not a conformance surface — no diagnostic id.
          return fail("operation outside the executable set: " +
                      other->getName().getStringRef());
        });
  }

  //===-- outcomes ---------------------------------------------------===//

  void reject(StringRef verdictClass, const llvm::Twine &message) {
    verdict = verdictClass.str();
    diag = message.str();
  }

  ArrayRef<uint8_t> proof;
  size_t cursor = 0;
  std::optional<std::string> verdict;
  std::string diag;
};

/// One prover-skeleton run: the write-side mirror of Execution. The
/// pin gate and statement channel are the verifier's own disciplines;
/// the wire is produced instead of consumed; holes dispatch by
/// contract digest under the realisation pair; and there is no
/// verdict channel at all — every failure is a refusal or a defect.
class Prove : public Machine<Prove> {
public:
  Prove(oir::ArtifactOp artifact, const ExecutionProfile &profile,
        const llvm::StringMap<std::string> &statement,
        const llvm::StringMap<std::string> &witness)
      : Machine(artifact, profile, statement), witness(witness) {}

  llvm::Expected<ProveResult> run() {
    if (artifact.getEndpointKind() != oir::kEndpointProverSkeleton)
      return fail<ProveResult>("[zkc-E409] endpoint kind '" +
                               artifact.getEndpointKind() +
                               "' is not executable by the prove entry point");
    auto program = *artifact.getBody().getOps<oir::ProgramOp>().begin();
    if (auto baked = program.getCodecs())
      codecs = *baked;
    if (llvm::Error error = gateParamDigests(program))
      return std::move(error);
    if (llvm::Error error = bindStatement(program))
      return std::move(error);
    if (llvm::Error error = bindWitness(program))
      return std::move(error);
    for (Operation &op : program.getBody().front())
      if (llvm::Error error = step(&op))
        return std::move(error);
    return ProveResult{std::move(proof), std::move(challenges)};
  }

private:
  friend Machine<Prove>;

  //===-- endpoint policy -------------------------------------------===//

  llvm::Error statementOutOfRange(StringRef name) {
    return fail("[zkc-E405] statement value '" + name +
                "' out of range for the prover's own inputs");
  }

  /// The challenge log records every draw, but the current scalar SSA
  /// runtime binds only the final draw; a vector-valued hole ABI is
  /// not implemented (docs/spec/endpoints.md §6.3).
  void bindSqueeze(Value val, const llvm::APInt &value, uint64_t) {
    env.try_emplace(val, value);
  }

  //===-- one operation ---------------------------------------------===//

  /// Witness payloads bind opaque, by their declared labels, as hex
  /// bytes; the run record carries nothing of their content beyond what
  /// the holes emit (the digest membrane at the execution boundary).
  llvm::Error bindWitness(oir::ProgramOp program) {
    Block &body = program.getBody().front();
    ArrayAttr labels = program.getWitnessLabelsAttr();
    unsigned base = program.getStatementLabels().size();
    for (auto [index, entry] : llvm::enumerate(labels)) {
      StringRef name = cast<StringAttr>(cast<ArrayAttr>(entry)[0]).getValue();
      auto payload = witness.find(name);
      if (payload == witness.end())
        return fail("[zkc-E410] witness payload '" + name + "' missing");
      StringRef hex(payload->second);
      if (hex.size() % 2 ||
          hex.find_first_not_of("0123456789abcdef") != StringRef::npos)
        return fail("[zkc-E410] witness payload '" + name +
                    "' is not lowercase hex");
      SmallVector<uint8_t, 32> bytes;
      auto nibble = [](char digit) -> uint8_t {
        return digit <= '9' ? digit - '0' : digit - 'a' + 10;
      };
      for (unsigned i = 0; i < hex.size(); i += 2)
        bytes.push_back(
            static_cast<uint8_t>((nibble(hex[i]) << 4) | nibble(hex[i + 1])));
      handleEnv.try_emplace(body.getArgument(base + index), std::move(bytes));
    }
    return llvm::Error::success();
  }

  /// The transcript peek (docs/spec/endpoints.md §6.2). The fill never
  /// holds the sponge: each trial runs on a clone, and the hole's
  /// sponge result is the unchanged live state. The peek's meaning is
  /// the three rows after the hole — the nonce write, its absorb, and
  /// the proof-of-work squeeze — so the trial is re-derived from
  /// exactly those rows and any other neighborhood refuses: a trial
  /// that is not the verifier's own check would search for the wrong
  /// witness.
  llvm::Error stepPowSearch(oir::HoleCallOp hole) {
    const PowSearchSupplier *supplier =
        profile.powSearch(hole.getContractDigest());
    if (!supplier)
      return fail("[zkc-E407] hole contract '" + hole.getContractDigest() +
                  "' (kind '" + hole.getKind() +
                  "') has no supplier in profile '" + profile.name() + "'");
    auto mismatch = [&](const llvm::Twine &what) {
      return fail("[zkc-E412] pow_search hole '" + hole.getLabel() + "': " +
                  what +
                  "; the trial the fill would run is not the check the "
                  "verifier performs");
    };
    Value nonce, spongeOut;
    for (Value output : hole.getOutputs()) {
      if (isa<oir::ValType>(output.getType()))
        nonce = output;
      else if (isa<oir::SpongeType>(output.getType()))
        spongeOut = output;
    }
    if (hole.getOutputs().size() != 2 || !nonce || !spongeOut)
      return mismatch("the contract must yield exactly one nonce value and "
                      "the state-identical sponge");
    ArrayAttr params = hole.getParams();
    uint64_t bits = 0;
    if (params.size() != 1 ||
        cast<StringAttr>(params[0]).getValue().getAsInteger(10, bits) ||
        bits == 0 || bits >= kValueBits)
      return mismatch(
          "the contract's one static parameter must be a positive bit count");
    auto write = dyn_cast_or_null<oir::WriteOp>(hole->getNextNode());
    if (!write || write.getValue() != nonce)
      return mismatch("the next row must write the nonce to the wire");
    auto absorbOp = dyn_cast_or_null<oir::AbsorbOp>(write->getNextNode());
    if (!absorbOp || absorbOp.getValue() != nonce ||
        absorbOp.getSponge() != spongeOut)
      return mismatch("the row after the write must absorb the nonce "
                      "through the hole's sponge result");
    auto squeezeOp = dyn_cast_or_null<oir::SqueezeOp>(absorbOp->getNextNode());
    if (!squeezeOp || squeezeOp.getSponge() != absorbOp.getOut())
      return mismatch("the row after the absorb must squeeze from it");
    llvm::APInt space = llvm::APInt::getZero(kValueBits);
    space.setBit(bits);
    if (squeezeOp.getCount() != "1" || squeezeOp.getRule() != "uniform" ||
        squeezeOp.getSpace() != decimal(space))
      return mismatch("the proof-of-work squeeze must draw one uniform "
                      "value from a space of exactly 2^bits");
    auto nonceClass = cast<oir::ValType>(nonce.getType()).getValueClass();
    llvm::Expected<const CodecSupplier *> nonceCodec = requireCodec(nonceClass);
    if (!nonceCodec)
      return nonceCodec.takeError();
    llvm::Expected<const CodecSupplier *> powCodec =
        requireCodec(squeezeOp.getPayloadClass());
    if (!powCodec)
      return powCodec.takeError();
    std::optional<SamplingPlan> plan = profile.admitSampling(
        squeezeOp.getRule(), squeezeOp.getCount(), squeezeOp.getSpace());
    if (!plan)
      return fail("[zkc-E402] sampling shape at '" + squeezeOp.getLabel() +
                  "' (rule '" + squeezeOp.getRule() + "', count " +
                  squeezeOp.getCount() + ", space " + squeezeOp.getSpace() +
                  ") has no supplier in profile '" + profile.name() + "'");
    // The search enumerates the nonce class's canonical values: the
    // class modulus where the profile knows one, the codec's whole
    // framing domain otherwise. The bound only matters at exhaustion —
    // the least witness is the same under either.
    llvm::APInt domainEnd =
        profile.canonicalModulus(nonceClass)
            .value_or(llvm::APInt::getOneBitSet(
                kValueBits, (*nonceCodec)->framingBits()));
    auto trial =
        [&](const llvm::APInt &candidate) -> llvm::Expected<llvm::APInt> {
      std::unique_ptr<SpongeState> probe = sponge->clone();
      SmallVector<uint8_t> framed;
      (*nonceCodec)->absorbFraming(candidate, framed);
      probe->absorb(framed);
      SmallVector<uint8_t, 32> symbols =
          probe->squeeze(squeezeOp.getDomain(), (*powCodec)->squeezeSymbols());
      return (*powCodec)->squeezeDerive(symbols, plan->space);
    };
    llvm::Expected<llvm::APInt> found = supplier->search(domainEnd, trial);
    if (!found)
      return llvm::joinErrors(fail("[zkc-E408] fill for hole contract '" +
                                   hole.getContractDigest() +
                                   "' reported a defect"),
                              found.takeError());
    env.try_emplace(nonce, *found);
    return llvm::Error::success();
  }

  llvm::Error step(Operation *op) {
    return llvm::TypeSwitch<Operation *, llvm::Error>(op)
        .Case<oir::TranscriptInitOp>([&](oir::TranscriptInitOp init) {
          return stepTranscriptInit(init);
        })
        .Case<oir::AbsorbOp>(
            [&](oir::AbsorbOp absorb) { return stepAbsorb(absorb); })
        .Case<oir::WriteOp>([&](oir::WriteOp write) -> llvm::Error {
          llvm::Expected<const CodecSupplier *> codec =
              requireCodec(write.getPayloadClass());
          if (!codec)
            return codec.takeError();
          llvm::Expected<llvm::APInt> value = get(write.getValue());
          if (!value)
            return value.takeError();
          // Emitted proofs are canonical by construction: an
          // out-of-range or non-canonical emission is a defect of the
          // fill that produced the value, reported before any byte
          // reaches the wire.
          if (auto modulus = profile.canonicalModulus(write.getPayloadClass()))
            if (value->uge(*modulus))
              return fail("[zkc-E408] fill produced an out-of-range value "
                          "at '" +
                          write.getLabel() + "'");
          SmallVector<uint8_t> encoded;
          (*codec)->encodeWire(*value, encoded);
          if (encoded.size() != (*codec)->wireWidth() ||
              !(*codec)->wireCanonical(encoded))
            return fail("[zkc-E408] emission at '" + write.getLabel() +
                        "' is not the canonical wire form");
          proof.insert(proof.end(), encoded.begin(), encoded.end());
          return llvm::Error::success();
        })
        .Case<oir::SqueezeOp>(
            [&](oir::SqueezeOp squeeze) { return stepSqueeze(squeeze); })
        .Case<oir::ConstantOp>(
            [&](oir::ConstantOp constant) { return stepConstant(constant); })
        .Case<oir::HoleCallOp>([&](oir::HoleCallOp hole) -> llvm::Error {
          if (llvm::any_of(hole.getInputs().getTypes(),
                           llvm::IsaPred<oir::SpongeType>))
            return stepPowSearch(hole);
          const HoleSupplier *supplier = profile.hole(hole.getContractDigest());
          if (!supplier)
            return fail("[zkc-E407] hole contract '" +
                        hole.getContractDigest() + "' (kind '" +
                        hole.getKind() + "') has no supplier in profile '" +
                        profile.name() + "'");
          SmallVector<llvm::APInt> values;
          SmallVector<SmallVector<uint8_t, 32>> handles;
          for (Value input : hole.getInputs()) {
            if (isa<oir::ValType>(input.getType())) {
              llvm::Expected<llvm::APInt> value = get(input);
              if (!value)
                return value.takeError();
              values.push_back(*value);
            } else if (isa<oir::HandleType>(input.getType())) {
              auto it = handleEnv.find(input);
              if (it == handleEnv.end())
                return llvm::createStringError(
                    "handle has no binding: not the output of a verified "
                    "projection");
              handles.push_back(it->second);
            } else {
              // Sponge operands were routed to the peek path above, and
              // zkc-E149 admits them on pow_search holes alone: reaching
              // here takes a hand-crafted artifact.
              return llvm::createStringError(
                  "sponge operand outside the peek path: not the output "
                  "of a verified projection");
            }
          }
          SmallVector<StringRef> params;
          for (Attribute entry : hole.getParams())
            params.push_back(cast<StringAttr>(entry).getValue());
          SmallVector<StringRef> semanticParams;
          for (Attribute entry : hole.getSemanticParams())
            semanticParams.push_back(cast<StringAttr>(entry).getValue());
          SmallVector<llvm::APInt> valueResults;
          SmallVector<SmallVector<uint8_t, 32>> handleResults;
          if (llvm::Error error =
                  supplier->fill(params, semanticParams, values, handles,
                                 valueResults, handleResults))
            return llvm::joinErrors(fail("[zkc-E408] fill for hole contract '" +
                                         hole.getContractDigest() +
                                         "' reported a defect"),
                                    std::move(error));
          unsigned valueIdx = 0, handleIdx = 0;
          for (Value output : hole.getOutputs()) {
            if (isa<oir::ValType>(output.getType())) {
              if (valueIdx >= valueResults.size())
                return fail("[zkc-E408] fill for hole contract '" +
                            hole.getContractDigest() +
                            "' returned too few value results");
              env.try_emplace(output, valueResults[valueIdx++]);
            } else if (isa<oir::HandleType>(output.getType())) {
              if (handleIdx >= handleResults.size())
                return fail("[zkc-E408] fill for hole contract '" +
                            hole.getContractDigest() +
                            "' returned too few handle results");
              handleEnv.try_emplace(output, handleResults[handleIdx++]);
            }
          }
          if (valueIdx != valueResults.size() ||
              handleIdx != handleResults.size())
            return fail("[zkc-E408] fill for hole contract '" +
                        hole.getContractDigest() +
                        "' returned surplus results");
          return llvm::Error::success();
        })
        .Case<oir::EndStreamOp, oir::FinishOp>(
            [](auto) { return llvm::Error::success(); })
        .Default([&](Operation *op) {
          // Defense in depth, not a conformance surface: the container
          // verifier already refuses verifier ops in a prover program.
          return llvm::createStringError(
              "operation outside the prover-executable set: " +
              op->getName().getStringRef());
        });
  }

  const llvm::StringMap<std::string> &witness;
  llvm::DenseMap<Value, SmallVector<uint8_t, 32>> handleEnv;
  std::vector<uint8_t> proof;
};

} // namespace

llvm::Expected<ExecutionResult>
execute(oir::ArtifactOp artifact, const ExecutionProfile &profile,
        const llvm::StringMap<std::string> &statement,
        ArrayRef<uint8_t> proof) {
  if (llvm::Error error = zkc::encoding::validateOirIdentity(artifact))
    return std::move(error);
  if (artifact.getEndpointKind() != oir::kEndpointVerifier)
    return llvm::createStringError(
        "[zkc-E409] endpoint kind '" + artifact.getEndpointKind() +
        "' is not executable by the verify entry point");
  return Execution(artifact, profile, statement, proof).run();
}

llvm::Expected<ProveResult> prove(oir::ArtifactOp artifact,
                                  const ExecutionProfile &profile,
                                  const llvm::StringMap<std::string> &statement,
                                  const llvm::StringMap<std::string> &witness) {
  if (llvm::Error error = zkc::encoding::validateOirIdentity(artifact))
    return std::move(error);
  return Prove(artifact, profile, statement, witness).run();
}

llvm::Expected<uint64_t> proofSizeBytes(oir::ArtifactOp artifact,
                                        const ExecutionProfile &profile) {
  // A static cost view is still an attributable consumer: it
  // authenticates the OIR bytes instead of pricing a program under a
  // forged authored id.
  if (llvm::Error error = zkc::encoding::validateOirIdentity(artifact))
    return std::move(error);
  // Proof size is the sum over the verifier's proof-stream reads. A prover
  // skeleton has none — it writes — so pricing one would answer zero, which
  // reads as "this proof is free" rather than "wrong endpoint".
  if (artifact.getEndpointKind() != oir::kEndpointVerifier)
    return llvm::createStringError("[zkc-E409] endpoint kind '" +
                                   artifact.getEndpointKind() +
                                   "' has no proof-stream reads to price");
  auto program = *artifact.getBody().getOps<oir::ProgramOp>().begin();
  DictionaryAttr codecs = program.getCodecs().value_or(DictionaryAttr());
  uint64_t bytes = 0;
  for (auto read : program.getBody().front().getOps<oir::ReadOp>()) {
    llvm::Expected<const CodecSupplier *> codec =
        routeCodec(codecs, read.getPayloadClass(), profile);
    if (!codec)
      return codec.takeError();
    bytes += (*codec)->wireWidth();
  }
  return bytes;
}

} // namespace interpreter
} // namespace zkc
