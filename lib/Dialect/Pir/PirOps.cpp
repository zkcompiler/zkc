//===- PirOps.cpp - Protocol IR ops -----------------------------*- C++ -*-===//
// Container verification for the kernel carrier (docs/spec/carrier.md
// §5, layer 2): body layout, thread continuity, claim linearity, label
// uniqueness, attachment injectivity, and check-role/membership
// resolution. These checks make
// the kernel's structural judgments (the layout half of WF and the
// single-use half of LIN, docs/spec/kernel.md §3–§4) unrepresentable
// to violate in verified IR; the seal pass adds the semantic judgments
// (BIND, COV, policy) on top. The walk is interface-driven: a member
// op declares its category once (ProtocolMemberOpInterface) and the
// automaton picks it up — fail-closed, since an op without the
// interface is not a member at all. Diagnostic ids are the conformance
// surface: every id below is exercised by a negative test.
//===----------------------------------------------------------------------===//

#include "zkc/Dialect/Pir/PirOps.h"

#include "zkc/ChallengeShape.h"
#include "zkc/Encoding/EncodingDomain.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;

namespace zkc {
namespace pir {

//===----------------------------------------------------------------------===//
// Result type inference: the val class mirrors the event's payload class
// by construction, so a mismatching handle class cannot be written.
//===----------------------------------------------------------------------===//

LogicalResult
BindOp::inferReturnTypes(MLIRContext *ctx, std::optional<Location>,
                         BindOp::Adaptor adaptor,
                         SmallVectorImpl<Type> &inferredReturnTypes) {
  inferredReturnTypes.push_back(getThreadType(ctx));
  inferredReturnTypes.push_back(ValType::get(ctx, adaptor.getPayloadClass()));
  return success();
}

LogicalResult
SlotOp::inferReturnTypes(MLIRContext *ctx, std::optional<Location>,
                         SlotOp::Adaptor adaptor,
                         SmallVectorImpl<Type> &inferredReturnTypes) {
  inferredReturnTypes.push_back(getThreadType(ctx));
  inferredReturnTypes.push_back(ValType::get(ctx, adaptor.getPayloadClass()));
  return success();
}

LogicalResult
ChalOp::inferReturnTypes(MLIRContext *ctx, std::optional<Location>,
                         ChalOp::Adaptor adaptor,
                         SmallVectorImpl<Type> &inferredReturnTypes) {
  inferredReturnTypes.push_back(getThreadType(ctx));
  inferredReturnTypes.push_back(ValType::get(ctx, adaptor.getPayloadClass()));
  return success();
}

LogicalResult ChalOp::verify() {
  // The challenge-space size is the exact cardinality |C| as a
  // minimal decimal string — no leading zeros, no fraction, never a
  // float — so one size has exactly one spelling and identity stays
  // bit-stable, and a prime-order sample space is spellable (the
  // retired log2 scale could not say it). This is the |C_i| a
  // Soundness Kernel rule reads (docs/spec/kernel.md §9); larger-than-i64
  // numerics are decimal strings by the domain rule (kernel.md §3, item 4).
  StringRef space = getSpace();
  if (!zkc::challenge::isCanonicalPositiveDecimal(space))
    return emitOpError() << "[zkc-E139] space is the exact sample-space "
                            "cardinality as a minimal decimal string, "
                            "got \""
                         << getSpace() << "\"";
  // P_req is a set of event references (kernel.md §1.5): the encoder
  // canonicalizes it by sorting, which is a quotient map only over
  // duplicate-free lists — a repeated operand is a second spelling of
  // one fact and is rejected here, not normalized away.
  llvm::SmallPtrSet<Value, 4> seen;
  for (Value dep : getDeps())
    if (!seen.insert(dep).second)
      return emitOpError()
             << "[zkc-E154] duplicate challenge dependency: P_req is a "
                "set, one event one entry";
  // Vector challenge capability (docs/spec/kernel.md §1.5): a challenge carries
  // a vector mode only when it departs the scalar default. Present ⟺ [shape,
  // count, sampling] with shape "vector", count the identity-bearing sample
  // multiplicity as a minimal decimal ≥ 2 (a 1-vector is a second spelling of a
  // scalar), sampling an admitted rule — the (1−δ)^ℓ query bound assumes
  // independent draws, so uniform_independent is the base value; distinct-index
  // sampling is a later mode. Absent = one scalar sample under the uniform
  // rule. Reuse belongs to the consuming reduction contract, not this
  // capability.
  if (auto mode = getMode()) {
    auto malformed =
        [&]() {
          return emitOpError()
                 << "[zkc-E140] a vector challenge mode is [\"vector\", count, "
                    "sampling] with count a minimal decimal from 2 through "
                    "2^20 and an "
                    "admitted sampling rule (uniform_independent)";
        };
    if (mode->size() != 3 || (*mode)[0] != "vector")
      return malformed();
    StringRef count = (*mode)[1];
    std::optional<uint64_t> parsed = zkc::challenge::parseCount(count);
    bool countWellFormed = parsed && *parsed >= 2;
    if (!countWellFormed)
      return malformed();
    if ((*mode)[2] != "uniform_independent")
      return malformed();
  }
  // The capability check is the container verifier's (see the body walk
  // below): MLIR verifies a parent on entrance, before its nested ops, and
  // this op's parent constraint admits only those two containers — so a call
  // here could never be the first owner and never fire. Two owners for one
  // invariant also means the diagnostic a reader sees is decided by traversal
  // order, which is how E140's own condition ended up reported as E145.
  return success();
}

llvm::StringRef ChalOp::getChallengePayloadClass() { return getPayloadClass(); }

mlir::Value ChalOp::getChallengeValue() { return getVal(); }

llvm::StringRef ChalOp::getChallengeCount() {
  if (auto mode = getMode(); mode && mode->size() == 3)
    return (*mode)[1];
  return getMode() ? llvm::StringRef() : llvm::StringRef("1");
}

llvm::StringRef ChalOp::getChallengeSamplingRule() {
  if (auto mode = getMode(); mode && mode->size() == 3)
    return (*mode)[2];
  return getMode() ? llvm::StringRef() : llvm::StringRef("uniform");
}

LogicalResult
verifyChallengeCapability(ChallengeCapabilityOpInterface capability) {
  Operation *op = capability.getOperation();
  StringRef payloadClass = capability.getChallengePayloadClass();
  if (payloadClass.empty())
    return op->emitOpError()
           << "[zkc-E145] challenge payload class must be non-empty";
  if (payloadClass == "chal")
    return op->emitOpError()
           << "[zkc-E145] payload class 'chal' is retired: a challenge "
              "must name its semantic payload class";

  if (!zkc::challenge::parseCount(capability.getChallengeCount()))
    return op->emitOpError()
           << "[zkc-E145] challenge capability count must be a canonical "
              "decimal from 1 through 2^20";
  if (capability.getChallengeSamplingRule().empty())
    return op->emitOpError()
           << "[zkc-E145] challenge sampling rule must be non-empty";

  // The two checks below cannot fail for the interface's only implementer:
  // ChalOp returns its own ODS result and infers its type. They are not
  // therefore dead — this function judges the interface, and the interface is
  // an extension boundary whose whole purpose is a second implementer. A seam
  // gets a typed refusal; that is what these are.
  Value value = capability.getChallengeValue();
  auto result = dyn_cast<OpResult>(value);
  if (!result || result.getOwner() != op)
    return op->emitOpError()
           << "[zkc-E145] challenge capability must identify one exact SSA "
              "result owned by the implementing operation";
  auto type = dyn_cast<ValType>(value.getType());
  if (!type || type.getValueClass() != payloadClass)
    return op->emitOpError()
           << "[zkc-E145] challenge capability value must have type "
              "!pir.val<\""
           << payloadClass << "\">";
  return success();
}

//===----------------------------------------------------------------------===//
// ProtocolMemberOpInterface implementations. Each member declares its
// layout category and verification-relevant state once; the container
// verifier below is generic over these answers.
//===----------------------------------------------------------------------===//

/// Membership from a slot's instance/role/idx props: absent only when
/// all three are unset, so a half-set shape is visible to the verifier
/// (zkc-E152) instead of silently reading as "no membership".
static std::optional<Membership> membershipOf(SlotOp op) {
  if (!op.getInstance() && !op.getRole() && op.getIdx() == 0)
    return std::nullopt;
  return Membership{op.getInstance().value_or(llvm::StringRef()),
                    op.getRole().value_or(llvm::StringRef()), op.getIdx()};
}

/// Anchor *shape* is an op-verifier fact (carrier.md §4): every anchor
/// value is a `sha256:`-prefixed 64-lowercase-hex digest reference —
/// kernel.md §8's reference form, so no anchor is reinterpretable as
/// another system's spelling of the same bytes. Anchor *completeness*
/// per descriptor profile stays a seal judgment (zkc-E247): exact anchor
/// schemas are vocabulary, and op verifiers must not know them.
static LogicalResult verifyAnchorValues(Operation *op, DictionaryAttr anchors) {
  for (NamedAttribute named : anchors) {
    auto value = dyn_cast<StringAttr>(named.getValue());
    if (!value || !zkc::encoding::isSha256Ref(value.getValue()))
      return op->emitOpError()
             << "[zkc-E156] anchor '" << named.getName().getValue()
             << "' must be a sha256:-prefixed 64-lowercase-hex digest "
                "reference";
  }
  return success();
}

LogicalResult InstantiateOp::verify() {
  return verifyAnchorValues(*this, getAnchors());
}

LogicalResult ReduceOp::verify() {
  // A reduction produces exactly one claim. The admitted vocabulary has said
  // so all along — its loader refuses a contract with a second output — but
  // the carrier's variadic result list did not, which left the positional
  // pairing below reachable only in principle and untestable in practice.
  // Rule: a seam has a consumer or a typed refusal, not silence.
  if (getOuts().size() != 1)
    return emitOpError() << "[zkc-E157] a reduction produces exactly one "
                            "claim, got "
                         << getOuts().size();
  // Same shape rule for the per-result anchor dictionaries; entry
  // derived-output equality stays a seal fact (zkc-E326) — only the
  // local value shape is judged here.
  if (auto outAnchors = getOutAnchors())
    for (Attribute entry : *outAnchors)
      if (auto dict = dyn_cast<DictionaryAttr>(entry))
        if (failed(verifyAnchorValues(*this, dict)))
          return failure();
  return success();
}

MemberPhase InstantiateOp::getPhase() { return MemberPhase::Source; }
llvm::StringRef InstantiateOp::getMemberLabel() { return getLabel(); }

MemberPhase BeginOp::getPhase() { return MemberPhase::SpineEvent; }
Value BeginOp::getThreadOut() { return getOut(); }

MemberPhase BindOp::getPhase() { return MemberPhase::SpineEvent; }
llvm::StringRef BindOp::getMemberLabel() { return getLabel(); }
Value BindOp::getThreadIn() { return getThread(); }
Value BindOp::getThreadOut() { return getOut(); }
bool BindOp::isAbsorbing() { return true; }

MemberPhase SlotOp::getPhase() { return MemberPhase::SpineEvent; }
llvm::StringRef SlotOp::getMemberLabel() { return getLabel(); }
Value SlotOp::getThreadIn() { return getThread(); }
Value SlotOp::getThreadOut() { return getOut(); }
bool SlotOp::isAbsorbing() { return !getUnabsorbed(); }
std::optional<Membership> SlotOp::getMembership() {
  return membershipOf(*this);
}

MemberPhase ChalOp::getPhase() { return MemberPhase::SpineEvent; }
llvm::StringRef ChalOp::getMemberLabel() { return getLabel(); }
Value ChalOp::getThreadIn() { return getThread(); }
Value ChalOp::getThreadOut() { return getOut(); }
bool ChalOp::isAbsorbing() { return true; }

MemberPhase CheckOp::getPhase() { return MemberPhase::SpineEvent; }
llvm::StringRef CheckOp::getMemberLabel() { return getLabel(); }

MemberPhase EndOp::getPhase() { return MemberPhase::SpineEvent; }
Value EndOp::getThreadIn() { return getThread(); }

MemberPhase ReduceOp::getPhase() { return MemberPhase::Transformer; }
llvm::StringRef ReduceOp::getMemberLabel() { return getLabel(); }

MemberPhase MaterialBindOp::getPhase() { return MemberPhase::Attachment; }

MemberPhase DischargeOp::getPhase() { return MemberPhase::Sink; }
MemberPhase ExportOp::getPhase() { return MemberPhase::Sink; }
MemberPhase AssumeOp::getPhase() { return MemberPhase::Sink; }
MemberPhase ResidualOp::getPhase() { return MemberPhase::Sink; }

//===----------------------------------------------------------------------===//
// The body battery. Layout is fixed (carrier.md §4):
//
//   [sources]* begin [spine events]* end [reduces]* [attachments]* [sinks]*
//
// and the thread chain must be exactly the block order, so ≤ is readable
// off the block and the canonical encoder walks one form. Body events
// forward-reference reduce instances in the tail, so verification is
// two passes: names first, then the automaton.
//===----------------------------------------------------------------------===//

namespace {

/// One in-flight body verification. Diagnostic ids: zkc-E131 foreign
/// member, zkc-E132 body layout, zkc-E133 thread discontinuity,
/// zkc-E134 duplicate label, zkc-E135 claim linearity, zkc-E136
/// unresolved selected check, zkc-E137 sealed identity shape, zkc-E138
/// reserved value class, zkc-E139 challenge space format, zkc-E151
/// membership to an unknown instance, zkc-E152 membership shape /
/// one-truth violations, zkc-E153 reduction arity, zkc-E154 duplicate
/// challenge dependency, zkc-E155 non-injective terminal check binding,
/// zkc-E157 malformed semantic string map, zkc-E158 empty semantic id,
/// zkc-E159 malformed material reference, zkc-E161 repeated value binding,
/// zkc-E162 repeated semantic reference. Cross-owner check accounting is a
/// ReductionClosure/TerminalClosure judgment: only those registry-backed
/// layers can recognize the one sound reuse case (a producer-pinned terminal
/// rule discharging that reduction's exact output).
class BodyVerifier {
public:
  LogicalResult verify(Operation *container, Block &body) {
    // Pass 1: the label namespace and the resolution sets. Membership
    // and semantic check selections resolve against these; collecting first
    // is what lets body events reference tail instances.
    for (Operation &op : body) {
      auto member = dyn_cast<ProtocolMemberOpInterface>(&op);
      if (!member)
        return op.emitOpError() << "[zkc-E131] is not a protocol member";
      StringRef label = member.getMemberLabel();
      // Ops that carry a label field must fill it: labels are the
      // check-selection and membership namespace, and an empty label would
      // make references to "" ambiguous the moment two exist.
      if (label.empty() &&
          isa<InstantiateOp, BindOp, SlotOp, ChalOp, CheckOp, ReduceOp>(op))
        return op.emitOpError() << "[zkc-E134] label must not be empty";
      if (!label.empty() && !labels.insert(label).second)
        return op.emitOpError()
               << "[zkc-E134] duplicate label '" << label << "'";
      if (isa<ReduceOp>(op))
        reduceLabels.insert(label);
      if (isa<CheckOp>(op))
        checkLabels.insert(label);
    }

    // Pass 2: the layout automaton over interface phases, the thread
    // chain, membership shape, and per-op structural rules.
    for (Operation &op : body)
      if (failed(step(&op)))
        return failure();

    if (phase == Phase::Sources || phase == Phase::Spine)
      return container->emitOpError()
             << "[zkc-E132] body must run [sources]* begin [events]* end "
                "[reduces]* [attachments]* [sinks]*; the spine "
             << (phase == Phase::Sources ? "never begins" : "never ends");

    return verifyClaimLinearity(body);
  }

private:
  // Sources → Spine (begin..end) → Tail (reduces, then attachments,
  // then sinks). Crossing a tail boundary is irreversible.
  enum class Phase { Sources, Spine, Tail, Attachments, Sinks };

  LogicalResult step(Operation *op) {
    // begin/end are the phase transitions themselves, not members of a
    // phase — they stay op-specific.
    if (auto begin = dyn_cast<BeginOp>(op)) {
      if (phase != Phase::Sources)
        return layoutError(op, "second spine head");
      phase = Phase::Spine;
      thread = begin.getOut();
      return success();
    }
    if (auto end = dyn_cast<EndOp>(op)) {
      if (phase != Phase::Spine)
        return layoutError(op, "end without a live spine");
      if (end.getThread() != thread)
        return threadError(op);
      phase = Phase::Tail;
      thread = nullptr;
      return success();
    }

    auto member = cast<ProtocolMemberOpInterface>(op);
    switch (member.getPhase()) {
    case MemberPhase::Source:
      if (phase != Phase::Sources)
        return layoutError(op, "claim source after the spine head");
      return success();

    case MemberPhase::SpineEvent: {
      if (phase != Phase::Spine)
        return layoutError(op, "spine event outside begin/end");
      if (Value in = member.getThreadIn()) {
        if (in != thread)
          return threadError(op);
        thread = member.getThreadOut();
      }
      if (auto challenge = dyn_cast<ChallengeCapabilityOpInterface>(op))
        if (failed(verifyChallengeCapability(challenge)))
          return failure();
      if (auto bind = dyn_cast<BindOp>(op)) {
        if (failed(reserveClass(op, bind.getPayloadClass())))
          return failure();
      }
      if (auto slot = dyn_cast<SlotOp>(op)) {
        if (failed(reserveClass(op, slot.getPayloadClass())))
          return failure();
      }
      if (auto check = dyn_cast<CheckOp>(op)) {
        if (check.getContract().empty())
          return op->emitOpError()
                 << "[zkc-E158] check contract id must not be empty";
        if (auto semanticArgs = check.getSemanticArgs())
          if (failed(verifyStringMap(op, *semanticArgs, "semantic_args")))
            return failure();
      }
      return verifyMembership(op, member.getMembership());
    }

    case MemberPhase::Transformer: {
      if (phase != Phase::Tail)
        return layoutError(op, phase == Phase::Sinks
                                   ? "transformer after a terminal sink"
                               : phase == Phase::Attachments
                                   ? "transformer after a material attachment"
                                   : "transformer before the spine ends");
      auto reduce = cast<ReduceOp>(op);
      if (reduce.getClaims().empty() || reduce.getOuts().empty())
        return op->emitOpError()
               << "[zkc-E153] a reduction consumes at least one claim and "
                  "produces at least one: zero inputs would be a source, "
                  "zero outputs a sink";
      if (reduce.getContract().empty())
        return op->emitOpError()
               << "[zkc-E158] reduction contract id must not be empty";
      if (failed(verifyCheckSelection(op, reduce.getChecks(), "reduction")))
        return failure();
      // One truth per fact (carrier.md §4): a value consumed as a dep
      // operand has its contract-shape role said by the operand position;
      // membership props on its defining event would be a second
      // spelling that can disagree.
      for (Value dep : reduce.getDeps())
        if (auto *def = dep.getDefiningOp())
          if (auto defMember = dyn_cast<ProtocolMemberOpInterface>(def))
            if (defMember.getMembership())
              return def->emitOpError()
                     << "[zkc-E152] event is a dep operand of reduce '"
                     << reduce.getLabel()
                     << "' and must not carry membership props: the "
                        "operand position is that fact's only spelling";
      return success();
    }

    case MemberPhase::Attachment: {
      if (phase != Phase::Tail && phase != Phase::Attachments)
        return layoutError(op,
                           phase == Phase::Sinks
                               ? "material attachment after a terminal sink"
                               : "material attachment before the spine ends");
      phase = Phase::Attachments;
      auto binding = cast<MaterialBindOp>(op);
      StringRef semanticRef = binding.getSemanticRef();
      if (!zkc::encoding::isSha256Ref(semanticRef))
        return op->emitOpError()
               << "[zkc-E159] semantic_ref must be a sha256:-prefixed "
                  "64-lowercase-hex digest reference";
      if (!boundValues.insert(binding.getValue()).second)
        return op->emitOpError()
               << "[zkc-E161] a verifier value may have at most one "
                  "semantic material binding";
      if (!boundSemanticRefs.insert(semanticRef).second)
        return op->emitOpError()
               << "[zkc-E162] semantic_ref '" << semanticRef
               << "' is already bound to another verifier value: material "
                  "bindings are reverse-injective";
      return success();
    }

    case MemberPhase::Sink: {
      if (phase != Phase::Tail && phase != Phase::Attachments &&
          phase != Phase::Sinks)
        return layoutError(op, "terminal sink before the spine ends");
      phase = Phase::Sinks;
      if (auto discharge = dyn_cast<DischargeOp>(op)) {
        if (discharge.getRule().empty())
          return op->emitOpError()
                 << "[zkc-E158] terminal rule id must not be empty";
        DictionaryAttr checks = discharge.getChecks();
        if (checks.empty())
          return op->emitOpError()
                 << "[zkc-E157] checks must bind at least one terminal role";
        if (failed(verifyCheckSelection(op, checks, "terminal")))
          return failure();
      } else {
        StringRef route;
        if (auto routed = dyn_cast<ExportOp>(op))
          route = routed.getRoute();
        else if (auto routed = dyn_cast<AssumeOp>(op))
          route = routed.getRoute();
        else if (auto routed = dyn_cast<ResidualOp>(op))
          route = routed.getRoute();
        if (route.empty())
          return op->emitOpError()
                 << "[zkc-E158] terminal route reference must not be empty";
      }
      return success();
    }
    }
    llvm_unreachable("unknown member phase");
  }

  LogicalResult layoutError(Operation *op, const Twine &what) {
    return op->emitOpError()
           << "[zkc-E132] " << what
           << "; the body runs [sources]* begin [events]* end [reduces]* "
              "[attachments]* [sinks]*";
  }

  LogicalResult threadError(Operation *op) {
    return op->emitOpError()
           << "[zkc-E133] does not consume the live thread: the chain must "
              "be exactly the block order";
  }

  /// Semantic maps cross the registry/carrier boundary by role. Their exact
  /// structural domain is string -> non-empty string; richer interpretation
  /// belongs to CheckContract and TerminalRule resolution at seal.
  LogicalResult verifyStringMap(Operation *op, DictionaryAttr map,
                                StringRef field) {
    for (NamedAttribute named : map) {
      StringRef role = named.getName().getValue();
      auto value = dyn_cast<StringAttr>(named.getValue());
      if (role.empty() || !value || value.getValue().empty())
        return op->emitOpError()
               << "[zkc-E157] " << field
               << " must be a dictionary from non-empty role names to "
                  "non-empty strings";
    }
    return success();
  }

  /// Role maps are selectors into the check-event namespace. Dictionary keys
  /// make roles unique and values are injective within one owner. Cross-owner
  /// ownership is intentionally not a carrier fact: semantic closure rejects
  /// unrelated reuse and admits only exact producer-output reuse.
  LogicalResult verifyCheckSelection(Operation *op, DictionaryAttr checks,
                                     StringRef ownerKind) {
    if (failed(verifyStringMap(op, checks, "checks")))
      return failure();
    llvm::StringSet<> selectedHere;
    for (NamedAttribute named : checks) {
      StringRef role = named.getName().getValue();
      StringRef selected = cast<StringAttr>(named.getValue()).getValue();
      if (!checkLabels.contains(selected))
        return op->emitOpError()
               << "[zkc-E136] " << ownerKind << " role '" << role
               << "' selects unknown check '" << selected << "'";
      if (!selectedHere.insert(selected).second)
        return op->emitOpError()
               << "[zkc-E155] check '" << selected
               << "' is selected for more than one " << ownerKind << " role";
    }
    return success();
  }

  LogicalResult verifyMembership(Operation *op,
                                 std::optional<Membership> membership) {
    if (!membership)
      return success();
    if (membership->instance.empty() || membership->role.empty() ||
        membership->idx < 0)
      return op->emitOpError()
             << "[zkc-E152] membership needs an instance, a role, and a "
                "non-negative occurrence index";
    if (!reduceLabels.contains(membership->instance))
      return op->emitOpError()
             << "[zkc-E151] membership references unknown reduce instance '"
             << membership->instance << "'";
    return success();
  }

  /// LIN's structural half (kernel.md §4): every claim produced in the
  /// body is consumed exactly once. The type system and the member
  /// interface already restrict who the consumer can be.
  LogicalResult verifyClaimLinearity(Block &body) {
    for (Operation &op : body) {
      for (Value result : op.getResults()) {
        if (!isa<ClaimType>(result.getType()))
          continue;
        if (result.use_empty())
          return op.emitOpError()
                 << "[zkc-E135] claim is never routed: every obligation "
                    "must reach a reduction or a terminal sink";
        if (!result.hasOneUse())
          return op.emitOpError()
                 << "[zkc-E135] claim is consumed more than once";
      }
    }
    return success();
  }

  /// The former class "chal" encoded origin by pretending it was payload
  /// semantics.  It is retired on every producer: challenges carry their
  /// semantic class and their producing op proves fresh-sampling origin.
  LogicalResult reserveClass(Operation *op, StringRef payloadClass) {
    if (payloadClass == "chal")
      return op->emitOpError()
             << "[zkc-E138] payload class 'chal' is retired; name the "
                "semantic payload class";
    return success();
  }

  Phase phase = Phase::Sources;
  Value thread;
  llvm::StringSet<> labels;
  llvm::StringSet<> reduceLabels;
  llvm::StringSet<> checkLabels;
  llvm::SmallPtrSet<Value, 8> boundValues;
  llvm::StringSet<> boundSemanticRefs;
};

} // namespace

LogicalResult ProtocolOp::verify() {
  return BodyVerifier().verify(getOperation(), *getBody().begin());
}

LogicalResult SealedOp::verify() {
  // The id's value is the seal boundary's contract — recomputed and
  // compared fail-closed by the artifact loader; the verifier owns
  // only the shape.
  if (!zkc::encoding::isLowerHex64(getId()))
    return emitOpError() << "[zkc-E137] id must be a 64-lowercase-hex "
                            "SHA-256 digest: one identity, one spelling";
  return BodyVerifier().verify(getOperation(), *getBody().begin());
}

} // namespace pir
} // namespace zkc

#include "zkc/Dialect/Pir/PirInterfaces.cpp.inc"
#include "zkc/Dialect/Pir/PirOpsEnums.cpp.inc"

#define GET_OP_CLASSES
#include "zkc/Dialect/Pir/PirOps.cpp.inc"
