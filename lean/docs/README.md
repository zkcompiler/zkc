# Formal reference

These documents own the independent formal models and their precise claims.
[Native specifications](../../docs/spec/README.md) remain authoritative for the
compiler and runtime. A native export is a connection boundary, not an assertion
that all native behavior already has a Lean model.

- [Architecture](architecture.md): packages, interfaces and proof composition.
- [PIR semantics](spec/semantics.md): typed mathematics, participants, effects,
  observations, termination and exact refinement.
- [Verification](spec/verification.md): explicit intent, contracts, consumers,
  authored targets, candidate generation and receipt semantics.
- [Scalar import](spec/common-source.md): admitted syntax and encoding.
- [Structured import](spec/structured-source.md): checked original protocol-stage
  programs with shared helpers, participants, services, retained contracts,
  protocol applications and repeats.
- [Ring expressions](spec/ring-expressions.md): retained Clean/AIR connection.
- [Multilinear Sumcheck](spec/multilinear-sumcheck.md): independent ordered table,
  endpoint-message and residual/discharge laws.
- [Multilinear interactive security](spec/multilinear-sumcheck-security.md): optional
  ArkLib adapters with complete and residual bounds and honest completeness.
- [Fiat–Shamir construction](spec/fiat-shamir.md): the transform of a validator,
  the checked transcript-construction rule and the compiled Schnorr proof
  Entry's random-oracle knowledge soundness.
- [Participant projection](spec/participant-projection.md): the checked rule
  relating an exported validator to the original program at its role, and its
  composition with transcript construction.
- [Multi-round Fiat–Shamir security](spec/fiat-shamir-security.md): soundness
  over typed query sites with per-site errors and realized decoding laws,
  including proof-of-work-gated and compound sites; as its instance, soundness of
  the transform of any validator from round-by-round soundness, in a random
  oracle on all typed histories, its instance for the imported Sumcheck
  verifier, and its composition with the checked rules for the compiled
  Sumcheck proof Entry.
- [Executable stage](spec/executable.md): the meaning of the validator program
  the runtime admits, the checked lowering rule from the constructed validator
  and the executable Schnorr verifier's knowledge soundness for byte provers.
- [Uniform query service](spec/uniform-query-service.md): a concrete structured
  handler with exact all-state query, pass-through and refusal laws, plus
  general-count Sumcheck process transport and actual imported-root bounds.
- [Support](support.md): theorem scope, assumptions, proved subjects and tested
  boundaries.
- [Dependencies](dependencies.md): exact pins and compatibility decisions.
- [Structured computations](design/structured-computations.md): canonical multi-result
  regions, explicit captures, operation contracts and reference-profile bridges.
- [Structured native import](design/structured-native-import.md): import placement,
  protocol verification targets and evidence boundaries.
- [Logical contexts](design/logical-contexts.md): port-independent mathematical
  binders, transport along port maps and the contract layer as an instance.
- [Checked compiler stages](design/checked-stages.md): the common shape of
  checked stage rules, property-specific relations and their composition, with
  transcript construction and participant projection as instances.
- [Research design](design/protocol-verification.md): questions, choices and
  evaluation criteria for extending the implemented architecture.
- [Native bridge](../bridges/common/README.md): differential and proof-request tests.
