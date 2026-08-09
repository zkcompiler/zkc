//===- PirInterfaces.td - Protocol member interface ---------*- tablegen -*-===//
// The container verifier walks this interface instead of a closed
// TypeSwitch (carrier.md §5): a new member op declares its category
// once, here, and the layout automaton, label namespace, thread chain,
// and membership resolution pick it up without editing the verifier.
// The walk stays fail-closed — an op without this interface is not a
// protocol member (zkc-E131) no matter what dialect it comes from.
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_PIR_INTERFACES_TD
#define ZKC_DIALECT_PIR_INTERFACES_TD

include "mlir/IR/OpBase.td"

def Pir_ProtocolMemberOpInterface
    : OpInterface<"ProtocolMemberOpInterface"> {
  let cppNamespace = "::zkc::pir";
  let description = [{
    The container-verification face of a protocol member: which layout
    phase it belongs to (kernel body layout, carrier.md §4), its label
    (the terminal-selection/membership namespace), its spine threading, whether
    it absorbs into the transcript (membership in the kernel's A), and
    its reduction membership (instance/role/idx — carrier.md §4).
  }];
  let methods = [
    InterfaceMethod<[{
      The layout phase this member occupies:
      [sources]* begin [events]* end [reduces]* [attachments]* [sinks]*.
    }], "::zkc::pir::MemberPhase", "getPhase", (ins)>,
    InterfaceMethod<[{
      The member's label, or empty for unlabeled members (begin, end,
      material bindings, sinks). Non-empty labels share one per-container
      namespace (zkc-E134) that terminal selections and membership references
      resolve in.
    }], "::llvm::StringRef", "getMemberLabel", (ins), /*methodBody=*/"",
                    /*defaultImplementation=*/[{ return ""; }]>,
    InterfaceMethod<[{
      The consumed thread token, or null for unthreaded members.
    }], "::mlir::Value", "getThreadIn", (ins), "",
                    [{ return ::mlir::Value(); }]>,
    InterfaceMethod<[{
      The produced thread token, or null for unthreaded members.
    }], "::mlir::Value", "getThreadOut", (ins), "",
                    [{ return ::mlir::Value(); }]>,
    InterfaceMethod<[{
      Whether this event advances the transcript (kernel A membership).
      The seal battery currently distinguishes prover material by op
      kind (unabsorbed slots are the only non-absorbing material that
      exists); this method is the declared answer a second such op
      kind must route the battery through before it lands.
    }], "bool", "isAbsorbing", (ins), "", [{ return false; }]>,
    InterfaceMethod<[{
      This event's reduction membership, if any props are set. The
      verifier checks the shape (instance and role paired, instance
      resolving to a reduce label) and the one-truth rule (an event
      whose value is a reduce dep operand carries no membership).
    }], "::std::optional<::zkc::pir::Membership>", "getMembership",
                    (ins), "", [{ return ::std::nullopt; }]>,
  ];
}

def Pir_ChallengeCapabilityOpInterface
    : OpInterface<"ChallengeCapabilityOpInterface"> {
  let cppNamespace = "::zkc::pir";
  let description = [{
    The protocol-neutral carrier face of a transcript-derived challenge.
    Consumers ask for the semantic payload class and exact sampling shape
    through this interface instead of recognizing one reserved pseudo-class
    or decoding an operation-specific mode attribute.  Origin remains a fact
    of the producing operation (`pir.chal` is fresh transcript sampling), not
    a payload-class convention.
  }];
  let methods = [
    InterfaceMethod<[{
      The exact SSA capability value produced by this operation. Consumers
      compare a dependency to this value, rather than treating every result of
      a multi-result producer as challenge-origin.
    }], "::mlir::Value", "getChallengeValue", (ins)>,
    InterfaceMethod<[{
      The semantic class of each sampled element.  This is the key into the
      construction profile's codec map; `chal` is not a semantic class.
    }], "::llvm::StringRef", "getChallengePayloadClass", (ins)>,
    InterfaceMethod<[{
      Exact sample multiplicity as a canonical decimal string. Scalar
      sampling returns `1`; a vector capability returns its declared count in
      the shared bounded domain 2 through 2^20.
    }], "::llvm::StringRef", "getChallengeCount", (ins)>,
    InterfaceMethod<[{
      The sampling rule whose semantics justify the declared multiplicity.
    }], "::llvm::StringRef", "getChallengeSamplingRule", (ins)>,
  ];
}

#endif // ZKC_DIALECT_PIR_INTERFACES_TD
