//===- OirOps.cpp - Operator IR ops -----------------------------*- C++ -*-===//
// Container verification for the endpoint carrier (docs/spec/carrier.md
// §6.1, docs/spec/endpoints.md): the artifact packages exactly one program;
// the program's sponge
// and stream are linear (the same exactly-one-use discipline that
// carries pir's thread and claims); the decision is last. Diagnostic
// ids zkc-E141..E143 are the endpoint half of the conformance surface.
//===----------------------------------------------------------------------===//

#include "zkc/Dialect/Oir/OirOps.h"

#include "zkc/ChallengeShape.h"
#include "zkc/Encoding/EncodingDomain.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;

namespace zkc {
namespace oir {

//===----------------------------------------------------------------------===//
// Result type inference: origins are decided by the producing op — the
// three channels' integrity disciplines are type-level facts. The
// algebra ops' derived-class inference is generated from the ODS class
// (OirOps.td); only the three channel producers differ.
//===----------------------------------------------------------------------===//

LogicalResult
SqueezeOp::inferReturnTypes(MLIRContext *ctx, std::optional<Location>,
                            SqueezeOp::Adaptor adaptor,
                            SmallVectorImpl<Type> &inferredReturnTypes) {
  inferredReturnTypes.push_back(SpongeType::get(ctx));
  inferredReturnTypes.push_back(
      ValType::get(ctx, adaptor.getPayloadClass(), "sampled"));
  return success();
}

LogicalResult SqueezeOp::verify() {
  StringRef count = getCount();
  std::optional<uint64_t> parsedCount = zkc::challenge::parseCount(count);
  if (!parsedCount)
    return emitOpError()
           << "[zkc-E146] " << zkc::challenge::kCountGrammarMessage
           << count << "\"";
  if (getPayloadClass().empty())
    return emitOpError() << "[zkc-E146] payload class must be non-empty";
  if (getPayloadClass() == "chal")
    return emitOpError()
           << "[zkc-E146] payload class 'chal' is retired: a squeeze must "
              "name its semantic payload class";
  if (getDomain().empty() ||
      !zkc::encoding::inEncodingDomain(getDomain()))
    return emitOpError()
           << "[zkc-E146] domain must be a non-empty printable-ASCII string";
  if (getRule().empty() || !zkc::encoding::inEncodingDomain(getRule()))
    return emitOpError()
           << "[zkc-E146] sampling rule must be a non-empty printable-ASCII "
              "string";
  if ((*parsedCount == 1 && getRule() != "uniform") ||
      (*parsedCount > 1 && getRule() != "uniform_independent"))
    return emitOpError()
           << "[zkc-E146] sampling rule must be 'uniform' for count 1 and "
              "'uniform_independent' for count 2 through 2^20; got rule '"
           << getRule() << "' with count " << count;
  if (!zkc::challenge::isCanonicalPositiveDecimal(getSpace()))
    return emitOpError()
           << "[zkc-E146] space must be an exact positive cardinality in "
              "minimal decimal form, got \""
           << getSpace() << "\"";
  return success();
}

LogicalResult CheckCallOp::verify() {
  if (!zkc::encoding::isSha256Ref(getContractDigest()))
    return emitOpError()
           << "[zkc-E147] contract_digest "
           << zkc::encoding::kSha256RefMessage;
  return success();
}

LogicalResult ReadOp::verify() {
  if (!zkc::challenge::parseCount(getCount()))
    return emitOpError()
           << "[zkc-E146] " << zkc::challenge::kCountGrammarMessage
           << getCount() << "\"";
  return success();
}

LogicalResult WriteOp::verify() {
  // The erasure lint (docs/spec/endpoints.md §2): a sampled
  // value is never a write operand directly — challenge-derived wire
  // content flows through a declared hole or derived binding; and
  // nothing is read on the prover side, so `wire` cannot occur.
  StringRef origin = cast<ValType>(getValue().getType()).getOrigin();
  if (origin == "sampled" || origin == "wire")
    return emitOpError()
           << "[zkc-E149] a write operand's origin must be hole, derived, "
              "public, or pinned; got '"
           << origin << "'";
  if (!zkc::challenge::parseCount(getCount()))
    return emitOpError()
           << "[zkc-E146] " << zkc::challenge::kCountGrammarMessage
           << getCount() << "\"";
  return success();
}

LogicalResult HoleCallOp::verify() {
  StringRef kind = getKind();
  bool known = kind == "commit" || kind == "extend" || kind == "evaluate" ||
               kind == "fold" || kind == "open" || kind == "pow_search";
  if (!known)
    return emitOpError()
           << "[zkc-E149] hole kind must be one of commit | extend | "
              "evaluate | fold | open | pow_search, got '"
           << kind << "'";
  if (!zkc::encoding::isSha256Ref(getContractDigest()))
    return emitOpError()
           << "[zkc-E149] contract_digest "
           << zkc::encoding::kSha256RefMessage;
  if (getOutputs().empty())
    return emitOpError() << "[zkc-E149] a hole declares at least one result";
  unsigned spongeIns = llvm::count_if(getInputs().getTypes(),
                                      llvm::IsaPred<SpongeType>);
  unsigned spongeOuts = llvm::count_if(getOutputs().getTypes(),
                                       llvm::IsaPred<SpongeType>);
  if (kind == "pow_search") {
    if (spongeIns != 1 || spongeOuts != 1)
      return emitOpError()
             << "[zkc-E149] a pow_search hole peeks the transcript: exactly "
                "one sponge operand and one sponge result (state-identical "
                "by semantic requirement)";
  } else if (spongeIns || spongeOuts) {
    return emitOpError()
           << "[zkc-E149] only a pow_search hole may take the sponge; kind '"
           << kind << "' has no transcript access";
  }
  // Result counts, when declared, cover every result positionally;
  // only value results may be counted — a handle or sponge is one
  // state, never a vector of them. Shape precedes linearity: a
  // mis-declared count is named before any use accounting.
  ArrayAttr resultCounts = getResultCounts();
  if (!resultCounts.empty()) {
    if (resultCounts.size() != getOutputs().size())
      return emitOpError() << "[zkc-E149] result_counts covers every result "
                              "positionally: "
                           << resultCounts.size() << " count(s) for "
                           << getOutputs().size() << " result(s)";
    for (auto [index, entry] : llvm::enumerate(resultCounts)) {
      StringRef count = cast<StringAttr>(entry).getValue();
      if (!zkc::challenge::parseCount(count))
        return emitOpError()
               << "[zkc-E146] " << zkc::challenge::kCountGrammarMessage
               << count << "\"";
      if (count != "1" &&
          !isa<ValType>(getOutputs()[index].getType()))
        return emitOpError() << "[zkc-E149] only a value result may be "
                                "counted; result "
                             << index << " is not a value";
    }
  }
  for (Value output : getOutputs()) {
    if (auto val = dyn_cast<ValType>(output.getType()))
      if (val.getOrigin() != "hole")
        return emitOpError() << "[zkc-E149] a hole's value results carry "
                                "origin 'hole', got '"
                             << val.getOrigin() << "'";
    if (output.use_empty())
      return emitOpError()
             << "[zkc-E149] every hole result has at least one use (an "
                "unconsumed result is a hole that silently did nothing)";
  }
  return success();
}

LogicalResult
ReadOp::inferReturnTypes(MLIRContext *ctx, std::optional<Location>,
                         ReadOp::Adaptor adaptor,
                         SmallVectorImpl<Type> &inferredReturnTypes) {
  inferredReturnTypes.push_back(StreamType::get(ctx));
  inferredReturnTypes.push_back(
      ValType::get(ctx, adaptor.getPayloadClass(), "wire"));
  return success();
}

LogicalResult
ConstantOp::inferReturnTypes(MLIRContext *ctx, std::optional<Location>,
                             ConstantOp::Adaptor adaptor,
                             SmallVectorImpl<Type> &inferredReturnTypes) {
  inferredReturnTypes.push_back(
      ValType::get(ctx, adaptor.getPayloadClass(), "pinned"));
  return success();
}

//===----------------------------------------------------------------------===//
// Containers
//===----------------------------------------------------------------------===//

LogicalResult ArtifactOp::verify() {
  if (!zkc::encoding::isLowerHex64(getId()))
    return emitOpError() << "[zkc-E141] id must be a 64-lowercase-hex "
                            "SHA-256 digest: one identity, one spelling";
  // References to identities carry the algorithm-prefixed form
  // (kernel.md §8); the artifact's own id stays bare.
  if (!zkc::encoding::isSha256Ref(getSource()))
    return emitOpError() << "[zkc-E141] source citation "
                         << zkc::encoding::kSha256RefMessage;
  auto programs = getBody().getOps<ProgramOp>();
  if (!llvm::hasSingleElement(programs) ||
      !llvm::hasSingleElement(getBody().front().getOperations()))
    return emitOpError()
           << "[zkc-E141] artifact packages exactly one oir.program";
  // The endpoint-kind vocabulary is closed (docs/spec/endpoints.md §1);
  // an unknown kind fails here, before any consumer reads program
  // semantics under a wrong frame.
  StringRef kind = getEndpointKind();
  if (kind == kEndpointVerifierGadgetReserved)
    return emitOpError()
           << "[zkc-E148] endpoint kind 'verifier_gadget' is reserved "
              "without carrier semantics (docs/spec/endpoints.md 5.1); "
              "no artifact of this kind can be minted";
  if (kind != kEndpointVerifier && kind != kEndpointProverSkeleton)
    return emitOpError()
           << "[zkc-E148] unknown endpoint kind '" << kind
           << "': the closed vocabulary is verifier | prover_skeleton | "
              "verifier_gadget";
  return success();
}

LogicalResult ProgramOp::verify() {
  Block &body = getBody().front();
  // The endpoint kind selects the program frame; the parent artifact's
  // verifier has already closed the kind vocabulary, so only the two
  // exercised kinds reach this point.
  bool prover =
      cast<ArtifactOp>((*this)->getParentOp()).getEndpointKind() ==
      kEndpointProverSkeleton;

  // Per-kind op admission (docs/spec/endpoints.md §6): the
  // read path and decision sinks belong to the verifier; the write
  // path and holes belong to the prover. Judged before frame shape so
  // a misplaced op is named directly.
  for (Operation &op : body) {
    bool verifierOnly =
        isa<ReadOp, ExpectEndOp, AssertEqOp, CheckCallOp, DecideOp>(op);
    bool proverOnly = isa<WriteOp, HoleCallOp, EndStreamOp, FinishOp>(op);
    if (prover ? verifierOnly : proverOnly)
      return op.emitOpError()
             << "[zkc-E148] operation is outside the "
             << (prover ? "prover_skeleton" : "verifier")
             << " endpoint's admitted operation set";
  }

  // witness_labels is prover-endpoint ABI: present (possibly empty)
  // exactly on prover programs, each entry a [label, handle-class]
  // string pair naming one opaque payload block argument.
  ArrayAttr witnessLabels = getWitnessLabelsAttr();
  if (prover != static_cast<bool>(witnessLabels))
    return emitOpError()
           << "[zkc-E148] witness_labels is present exactly when the "
              "endpoint kind is prover_skeleton";
  // Presence-iff-prover for counterparty is owned by the canonical encoder
  // (the copy on every consumer's path, live before this verifier at the
  // minting site); this walk owns the row structure the encoder serializes
  // verbatim: [position, discharge] with non-negative, duplicate-free
  // positions. Discharge-kind membership needs the environment and belongs
  // to registry-aware admission, not a hermetic op verifier.
  if (ArrayAttr counterparty = getCounterpartyAttr()) {
    llvm::SmallDenseSet<int64_t> seenPositions;
    for (auto [index, entry] : llvm::enumerate(counterparty)) {
      auto row = dyn_cast<ArrayAttr>(entry);
      auto position = row && row.size() == 2 ? dyn_cast<IntegerAttr>(row[0])
                                             : IntegerAttr();
      auto discharge =
          row && row.size() == 2 ? dyn_cast<StringAttr>(row[1]) : StringAttr();
      if (!position || !discharge)
        return emitOpError() << "[zkc-E148] counterparty row #" << index
                             << " must be a [position, discharge] pair";
      int64_t value = position.getValue().getSExtValue();
      if (value < 0)
        return emitOpError() << "[zkc-E148] counterparty row #" << index
                             << " cites a negative event position";
      if (!seenPositions.insert(value).second)
        return emitOpError() << "[zkc-E148] counterparty rows cite event "
                                "position "
                             << value << " more than once";
    }
  }
  if (witnessLabels)
    for (auto [index, entry] : llvm::enumerate(witnessLabels)) {
      auto pair = dyn_cast<ArrayAttr>(entry);
      if (!pair || pair.size() != 2 || !isa<StringAttr>(pair[0]) ||
          !isa<StringAttr>(pair[1]))
        return emitOpError() << "[zkc-E148] witness_labels entry #" << index
                             << " must be a [label, handle-class] string "
                                "pair";
    }

  // param_digests rows are "sponge:<name>=<digest>" / "codec:<name>=<digest>"
  // pins. Row shape is carrier structure with one owner here; whether the
  // digest agrees with a supplier stays with the execution profile, the
  // only party that can answer it.
  for (Attribute entry : getParamDigests()) {
    StringRef pin = cast<StringAttr>(entry).getValue();
    auto [taggedName, digest] = pin.split('=');
    if (digest.empty() || (!taggedName.starts_with("sponge:") &&
                           !taggedName.starts_with("codec:")))
      return emitOpError()
             << "[zkc-E148] malformed pinned-parameter entry '" << pin
             << "': rows are sponge:<name>=<digest> or codec:<name>=<digest>";
  }

  // The entry ABI is exact: the labeled statement values, then (prover
  // only) one handle per witness_labels entry, then the stream — no
  // unlisted arguments in any position. Every consumer reads through this
  // positional coupling, and an argument outside it would be unbound
  // ballast no execution can ever reach.
  ArrayAttr labels = getStatementLabels();
  unsigned nLabels = labels ? labels.size() : 0;
  unsigned nWitness = witnessLabels ? witnessLabels.size() : 0;
  unsigned nArgs = body.getNumArguments();
  if (nArgs != nLabels + nWitness + 1 ||
      !isa<StreamType>(body.getArgument(nArgs - 1).getType()))
    return emitOpError()
           << "[zkc-E144] the program's arguments are exactly the labeled "
              "statement values, the declared witness handles, and one "
              "final stream: expected "
           << (nLabels + nWitness + 1) << ", got " << nArgs;
  for (unsigned index = 0; index < nLabels; ++index)
    if (!isa<ValType>(body.getArgument(index).getType()))
      return emitOpError()
             << "[zkc-E144] statement label #" << index
             << " does not name a value argument (the leading block "
                "arguments are the labeled statement values)";
  for (unsigned i = 0; i < nWitness; ++i) {
    auto handle = dyn_cast<HandleType>(body.getArgument(nLabels + i).getType());
    StringRef declared =
        cast<StringAttr>(cast<ArrayAttr>(witnessLabels[i])[1]).getValue();
    if (!handle || handle.getHandleClass() != declared)
      return emitOpError()
             << "[zkc-E148] witness argument #" << i << " must be !oir.handle<"
             << declared << "> per its witness_labels declaration";
  }

  // Frame shape: the terminal consumer is the endpoint's own (decide /
  // finish), and it also guarantees a non-empty block, so the linearity
  // fallback below may anchor a diagnostic on the first operation
  // without dereferencing the list sentinel.
  if (!prover) {
    if (body.empty() || !isa<DecideOp>(body.back()))
      return emitOpError() << "[zkc-E142] the decision must be the final "
                              "operation of the program";
  } else {
    if (body.empty() || !isa<FinishOp>(body.back()))
      return emitOpError() << "[zkc-E149] finish must be the final "
                              "operation of a prover program";
  }

  // Linearity: every sponge, stream, and handle state is consumed
  // exactly once — the same exactly-one-use discipline for all three
  // threaded resources; an unconsumed handle is a committed tree
  // nobody opened.
  auto checkLinear = [&](Value state, Operation *producer) -> LogicalResult {
    if (state.hasOneUse())
      return success();
    Operation *at = producer ? producer : &body.front();
    Type type = state.getType();
    if (isa<HandleType>(type))
      return at->emitOpError()
             << "[zkc-E149] handle state must be consumed exactly once "
                "(every handle chain ends in a consuming hole before "
                "finish)";
    return at->emitOpError()
           << "[zkc-E143] " << (isa<SpongeType>(type) ? "sponge" : "stream")
           << " state must be consumed exactly once";
  };
  unsigned inits = 0, streamEnds = 0;
  for (BlockArgument arg : body.getArguments())
    if (isa<SpongeType, StreamType, HandleType>(arg.getType()))
      if (failed(checkLinear(arg, nullptr)))
        return failure();
  for (Operation &op : body) {
    if (isa<TranscriptInitOp>(op))
      ++inits;
    if (isa<ExpectEndOp, EndStreamOp>(op))
      ++streamEnds;
    for (Value result : op.getResults())
      if (isa<SpongeType, StreamType, HandleType>(result.getType()))
        if (failed(checkLinear(result, &op)))
          return failure();
  }
  if (inits != 1)
    return emitOpError()
           << "[zkc-E142] exactly one transcript_init required, got "
           << inits;
  if (streamEnds != 1)
    return emitOpError() << "[zkc-"
                         << (prover ? "E149] exactly one end_stream"
                                    : "E142] exactly one expect_end")
                         << " required, got " << streamEnds;
  return success();
}

} // namespace oir
} // namespace zkc

#define GET_OP_CLASSES
#include "zkc/Dialect/Oir/OirOps.cpp.inc"
