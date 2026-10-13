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
- [Oracle encoding](spec/oracle-encoding.md): adaptive cached-query and residual-state transport.
- [Ring expressions](spec/ring-expressions.md): retained Clean/AIR connection.
- [Support](support.md): theorem scope, assumptions and tested boundaries.
- [Dependencies](dependencies.md): exact pins and compatibility decisions.
- [Research design](design/protocol-verification.md): questions, choices and
  evaluation criteria for extending the implemented architecture.
- [Native bridge](../bridges/common/README.md): differential and proof-request tests.
