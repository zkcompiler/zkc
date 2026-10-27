# Formal reference

These documents own the independent formal models and their precise claims.
[Native specifications](../../docs/spec/README.md) remain authoritative for the
compiler and runtime. A native export is a connection boundary, not an assertion
that all native behavior already has a Lean model.

- [Architecture](architecture.md): packages, interfaces and proof composition.
- [Typed model transition](semantic-model-transition.md): canonical execution, retained claims and explicit model-change boundaries.
- [Checked components](spec/components.md): shared process bindings, reference mathematics,
  honest execution, adversarial reductions and canonical receipts.
- [Component authoring](development/component-authoring.md): author-owned mathematics,
  representation and connection laws, generated bindings and root proof obligations.
- [PIR semantics](spec/semantics.md): typed mathematics, participants, effects,
  observations, termination and exact refinement.
- [Verification](spec/verification.md): explicit intent, contracts, consumers,
  authored targets, candidate generation and receipt semantics.
- [Scalar import](spec/common-source.md): admitted syntax and encoding.
- [Structured import](spec/structured-source.md): checked original protocol-stage
  programs with shared helpers, participants, services, retained contracts,
  protocol applications and repeats.
- [Exact tables](spec/table-relations.md): complete Boolean membership and indexed-read evaluator laws.
- [Selected data codecs](spec/data-codecs.md): executable partial encoding,
  canonical acceptance, compositional framing and nominal batch payloads.
- [Ring expressions](spec/ring-expressions.md): retained Clean/AIR connection.
- [Multilinear Sumcheck](spec/multilinear-sumcheck.md): independent ordered table,
  endpoint-message and residual/discharge laws.
- [Embedded-table Sumcheck](spec/sumcheck-embedding.md): explicit base-to-extension
  maps, nominal challenges and the mixed KoalaBear/octic client.
- [Multilinear interactive security](spec/multilinear-sumcheck-security.md): optional
  ArkLib adapters with complete and residual bounds and honest completeness.
- [Fiat–Shamir construction](spec/fiat-shamir.md): the transform of a validator,
  the checked transcript-construction rule, typed requests on challenge
  occurrences, the data shape of interaction patterns and the compiled Schnorr
  proof Entry's random-oracle knowledge soundness.
- [Participant projection](spec/participant-projection.md): the checked rule
  relating an exported validator to the original program at its role, and its
  composition with transcript construction.
- [Multi-round Fiat–Shamir security](spec/fiat-shamir-security.md): soundness
  over typed query sites with per-site errors or per-key charges and realized
  decoding laws as law records, including proof-of-work-gated and compound
  sites; raw answers by the last event and the lifting of uniform-sort
  certificates; binding codecs over typed public-value events; as its instance, soundness of
  the transform of any validator from round-by-round soundness, in a random
  oracle on all typed histories, its instances for the imported Sumcheck
  verifier and the plain GKR verifier, and its composition with the checked
  rules for the compiled Sumcheck and GKR proof Entries; the import of ArkLib's
  worst-case round-by-round soundness and its transport to the compiled verifier
  of a guessing fixture; formal readings of the construction obligations, the
  type of provider simulations and its hash-chain instance for the
  construction's byte-level chain model, and the joint experiment of a
  committed opening with its bound for a total straight-line extractor; and the
  bound for verifiers with committed tables, read with roots and openings in
  one random oracle with their hash calls.
- [FRI security](spec/fri-security.md): the verifier of the FRI library's
  low-degree test at the ideal interpretation of its commitments, its
  line-by-line correspondence to the source and ArkLib's FRI analysis, its
  completeness on codewords, its round-by-round soundness certificate with
  explicit errors, also over the verifier's residual processes, its
  Fiat–Shamir transfer with one query-block site, and the same verifier with
  words committed by Merkle trees, bounded for acceptance together with a far
  extraction at a verifier checkpoint.
- [Executable stage](spec/executable.md): the meaning of the validator program
  the runtime admits, with loops and helper calls, the checked lowering rule from
  the constructed validator with checked normalization of pure total
  calculations and helper preparation, completeness at a sufficient budget, the
  executable Schnorr verifier's knowledge soundness, the executable Sumcheck
  verifier's soundness for byte provers and honest-prover completeness, and a
  rescheduled deferred-rounds program.
- [Uniform query service](spec/uniform-query-service.md): a concrete structured
  handler with exact all-state query, pass-through and refusal laws, plus
  general-count Sumcheck process transport and actual imported-root bounds.
- [Assurance reports](spec/assurance-report.md): the `zkc.assurance-report/0`
  format, declaration records, the registry, the claims ledger and the
  generated tables.
- [Selected property adapters](spec/selected-property-adapters.md): scoped KZG evaluation binding, request-fixed finite oracle recovery, and private-producer verifier WP.
- [Support](support.md): theorem scope, assumptions, proved subjects and tested
  boundaries.
- [Dependencies](dependencies.md): exact pins and compatibility decisions.
- [Lean 4.35 adoption](development/lean-4.35-adoption.md): proof interfaces, upstream reuse and measured build choices.
- [Weakest preconditions](spec/weakest-preconditions.md): local proof interpretations, adequacy, cost and honest-execution boundaries.
- [Independent checking](development/independent-checking.md): exported locked statements, the comparator and paranoid checkers.
- [Structured computations](design/structured-computations.md): canonical multi-result
  regions, explicit captures, operation contracts and reference-profile bridges.
- [Structured native import](design/structured-native-import.md): import placement,
  protocol verification targets and evidence boundaries.
- [Logical contexts](design/logical-contexts.md): port-independent mathematical
  binders, transport along port maps and the contract layer as an instance.
- [Checked compiler stages](design/checked-stages.md): the common shape of
  checked stage rules, property-specific relations and their composition, with
  transcript construction, participant projection and executable lowering as
  instances.
- [Research design](design/protocol-verification.md): questions, choices and
  evaluation criteria for extending the implemented architecture.
- [Native bridge](../bridges/common/README.md): differential and proof-request tests.

- [Nominal data and execution boundaries](spec/nominal-data.md)
