//===- PirTypes.td - Protocol IR types ----------------------*- tablegen -*-===//
// Types of the pir dialect (docs/spec/carrier.md §3–§4). The thread type is
// not defined here: it is the builtin `token`, used directly via the
// upstream `Token` ODS constraint; C++ code obtains it through
// zkc::pir::getThreadType so the choice has a single point of change.
//===----------------------------------------------------------------------===//

#ifndef ZKC_DIALECT_PIR_TYPES_TD
#define ZKC_DIALECT_PIR_TYPES_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Pir/PirDialect.td"

class Pir_Type<string name, string typeMnemonic> : TypeDef<Pir_Dialect, name> {
  let mnemonic = typeMnemonic;
}

def Pir_ValType : Pir_Type<"Val", "val"> {
  let summary = "event value handle";
  let description = [{
    `!pir.val<class>` — the freely-readable (not linear) value handle
    produced by value-bearing spine events and consumed by later events
    and checks. `class` mirrors the event's semantic payload class; challenge
    values carry the class declared by their challenge-capability producer
    (for example `scalar`, `fr`, or `query_index`). It keys into the
    protocol's codec map (`kappa.codecs`). Challenge dependencies (the P_req of
    docs/spec/kernel.md §5) are val operands: SSA dominance makes "depends
    on a later event" unrepresentable, and the seal pass checks
    absorption on top.

    A value may name a **profile** instead of a bare class:
    `!pir.val<profile "table">` resolves a `value_profiles` entry in the
    sealed vocabulary, which supplies the element class and states what the
    value commits to — origin, arity, and binding route. The claim type has
    resolved a descriptor profile from the start; this is the same treatment
    for the other type, and today's bare class is the degenerate case rather
    than a separate thing. The marker is explicit so an unresolved profile
    name is a refusal instead of a class nobody declared: one namespace
    would fail open on a typo.

    The kernel never reads what a profiled value commits to. The profile
    fixes arity, class, and route the way a claim profile fixes anchor
    names, so no-predicate-semantics holds by construction.
  }];
  let parameters = (ins StringRefParameter<"payload class or profile id">
                            :$classOrProfile,
                        DefaultValuedParameter<"bool", "false">:$profiled);
  // Hand-written, because the marker is a keyword's presence rather than a
  // parameter's value and the optional-group form would parse a literal
  // boolean. The two spellings are `<"class">` and `<profile "name">`.
  let hasCustomAssemblyFormat = 1;
  let extraClassDeclaration = [{
    /// The payload class this value carries, or empty when it carries a
    /// profile instead.
    ///
    /// A commitment is not an element of the class its content is drawn
    /// from: a value committing to a thousand scalars answers "no" to "are
    /// you a scalar", and every site asking that question must get that
    /// answer rather than a profile name that happens to spell a class.
    /// The parameter is named `classOrProfile` so that a site reading it
    /// raw is visibly reading two things at once.
    llvm::StringRef bareClass() const {
      return getProfiled() ? llvm::StringRef() : getClassOrProfile();
    }

    /// The value profile this value names, or empty when it carries a bare
    /// payload class. A consumer that means to resolve the profile reads
    /// this, so the two readings never share a spelling.
    llvm::StringRef profileName() const {
      return getProfiled() ? getClassOrProfile() : llvm::StringRef();
    }
  }];
}

def Pir_ClaimType : Pir_Type<"Claim", "claim"> {
  let summary = "proof obligation (linear)";
  let description = [{
    `!pir.claim<profile-id>` — a proof obligation as an SSA value
    (docs/spec/kernel.md §1.3, carrier.md §4). Claim values are linear by
    container verification: every claim is produced exactly once (by a
    source or reduction) and consumed exactly once (by a reduction or a
    terminal sink). Fan-out and drop are representable only as declared
    transformer operations, so "an obligation silently vanished" is a
    verifier error, not a bug class. `profile-id` selects a closed descriptor
    profile in the sealed vocabulary. The profile supplies the claim's coarse
    kind and exact anchor schema, so there is one identity-bearing constructor
    rather than an independently authored kind/profile pair.
  }];
  let parameters = (ins StringRefParameter<"descriptor profile id">:$profile);
  let assemblyFormat = "`<` $profile `>`";
}

#endif // ZKC_DIALECT_PIR_TYPES_TD
