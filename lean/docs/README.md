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
- [Constructed import](spec/constructed-source.md): actual candidate bodies,
  typed result products, state and primitive interpretations.
- [Constructed realization](spec/constructed-realization.md): fixed scalar and
  ideal transcript meanings, complete denotation and checked normalization.
- [Fiat–Shamir requests](spec/fs-verification.md): selected ideal models,
  actual constructed subjects, security consumers and receipts.
- [Sumcheck restoration](spec/sumcheck-restoration.md): all-prefix knowledge
  predicates and quantitative security experiments.
- [Full-prefix simulation](spec/prefix-simulation.md): shared-cache connection
  to salted restoration, with explicit query accounting.
- [Oracle encoding](spec/oracle-encoding.md): adaptive cached-query and residual-state transport.
- [Ring expressions](spec/ring-expressions.md): retained Clean/AIR connection.
- [Support](support.md): theorem scope, assumptions and tested boundaries.
- [Dependencies](dependencies.md): exact pins and compatibility decisions.
- [Research design](design/protocol-verification.md): questions, choices and
  evaluation criteria for extending the implemented architecture.
- [Native bridge](../bridges/common/README.md): differential and proof-request tests.
- [Construction bridge](../bridges/constructed/README.md): actual participant,
  provider-state and codec controls.
