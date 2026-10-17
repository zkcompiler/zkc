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
- [Research design](design/protocol-verification.md): questions, choices and
  evaluation criteria for extending the implemented architecture.
- [Native bridge](../bridges/common/README.md): differential and proof-request tests.
