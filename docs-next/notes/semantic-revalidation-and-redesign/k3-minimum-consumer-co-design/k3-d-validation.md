# K3-D Validation

> **Document kind:** Temporary bounded-validation record
> **Document state:** Bounded validation complete after iterative adversarial
> review and final cold audit
> **Provisional owner:** `project`, coordinating `pir` and `oir`
> **Authority:** None. This page records finite design evidence and review; it
> establishes no source/target refinement theorem, OIR execution semantics,
> protocol-family coverage, compiler correctness, implementation conformance,
> or cryptographic property.
> **Date:** 2026-08-28
> **Disposition:** Retain until durable absorption, then delete with the K3
> package.

## 1. Bounded validation claim

K3-D closes one static, exact, no-rewrite endpoint-projection profile:

```text
admitted K2 Protocol/Fiat--Shamir
  + admitted K3-B ProtocolInterface
  + exact endpoint purpose
  + admitted K3-B ProverPlan and CheckedPlanRealizes, for the Prover
  -> PIR-owned EndpointSourceView

independently formed target graph
  -> LocalOirValid

EndpointSourceView
  + independently admitted OIR
  + exact K3DProjectionRelationV0
  -> source-relative ProjectedOirCapability
```

The supported positive profile is exactly a Fiat--Shamir Verifier endpoint and
a Fiat--Shamir Plan-specialized Prover endpoint over base, non-Oracle,
non-module P01 semantics. Fresh, generic Prover, Oracle, and every admitted
module-effect case are typed `Unsupported` before any projection proposition
is formed. Unsupported or unanswerable cases produce no partial OIR authority.

This is a bounded constructibility and falsification result. It is not a proof
that the model covers a protocol family or that any projected endpoint has a
cryptographic property.

## 2. Durable closure checked

The selected owners are
[PIR Endpoint Projection Views](../../../pir/endpoint-projection-views.md) and
[OIR Endpoint and Projection Contract](../../../oir/projection-contract.md).
Validation checks that they agree on the following boundary:

- PIR owns an exhaustive five-root read law and one purpose-specific,
  whole-source-provenance-free `EndpointSourceView`;
- source and target independently form the same exact eleven-field
  `EndpointSemanticGraphBody` rather than trusting a producer correspondence
  witness;
- `OirId` authenticates target semantics without whole source IDs, source
  provenance, checker identity, validation limits, capabilities, or runtime
  receipts;
- `LocalOirValid` is source-blind and does not imply source preservation;
- `ProjectionCorrect` checks exact graph equality and returns the complete
  nonempty set of differing top-level fields on a well-formed mismatch;
- `EndpointContractLawV0` derives one nonidentity static contract containing
  static obligations, exact requirements, and the completion interface;
- graph-only value-access closure is a transient least fixed point and cannot
  become an authored identity field or ambient source of values;
- reachable Plan algorithms, recipes, private-material classes, randomness,
  initialization, and state updates enter the Prover quotient, while dead
  declarations, exports, source labels, and concrete suppliers do not;
- all K2 framing coordinates, challenge conditions, namespace recipes,
  state-advance, retry, decode, exhaustion, and construction-global failure
  laws remain exact identity-bearing source and target semantics; and
- graph size, derived-contract size, dependency depth, edge count, and
  evaluation work are bounded and fail atomically.

Dynamic ports and presence, state versions and joins, draw instances and
receipts, decoder results, wire packaging, reached completion, and runtime
outcomes are deliberately not claimed. They require Stage 4B execution
semantics.

## 3. Corrections made under falsification

K3-D did not merely document its first candidate. Review reopened the local
design whenever the candidate promised more than its language could decide:

1. An authored source-read manifest was rejected because a producer could omit
   the fact it failed to preserve.
2. Target-inferred source obligations were rejected because a target cannot
   recover why a source Statement, check, claim, recipe, or failure had to
   exist.
3. The first six-plane correspondence relation was replaced by equality of one
   complete eleven-field graph after cold audit found omitted value, control,
   Fiat--Shamir, claim, and outcome structure.
4. A proposed protected runtime trace was removed from K3-D after review found
   that path-sensitive presence, state, draws, decode results, and wire
   behavior had no closed execution language. The replacement is an exact
   static contract, while the complete runtime question is routed to Stage
   4B.
5. A source-independent endpoint-pair proposition was withdrawn after two
   candidates failed. The source-bound version made Negative vacuous, and the
   target-only version lacked exact canonical normalization, rebasing,
   transport/action duality, mismatch, and pair-local bound laws. K3-D now
   contains only a non-authoritative P01 pressure probe; Stage 4B owns any
   future pair judgment.
6. Interface inadequacy was narrowed to the exact missing required
   counterparty transport occurrence. Malformed or wrong transport edges
   remain Interface nonadmission rather than projection Negative.
7. Prover-private value handling was rechecked against K2. No upstream reopen
   was needed because K2 public-coin eligibility already rejects invoked FS
   sinks with verifier-private predecessors, and K3-D separately rejects such
   retained target inputs.

The resulting scope correction preserves strong static Fiat--Shamir
obligations; it does not downgrade them to optional metadata.

## 4. Research and independent review

The selection was rechecked against four distinct assurance models:

- MLIR dialect conversion separates target legality and conversion coverage;
- Alive2 performs source/target translation validation with explicit
  unsupported scope;
- CompCert can state whole-program semantic preservation because its source and
  target behavior languages are complete; and
- Wizard-IOP/Arcane demonstrates that ZK protocol compilation can change
  queries, coins, and commitment structure across semantic levels.

These sources support the selected separation between local target admission,
exact bounded projection, later nonidentity Protocol transformations, and
future execution-level refinement. They do not prove the zkc contract.

Independent read-only schema and executable audits found and drove the graph,
static-contract, value-access, and pairing corrections above. The final
post-repair cold audits reported no blocking or major semantic contradiction
and no reason to reopen K1, K2, or K3-B. That is review evidence, not proof of
completeness.

## 5. Finite instrument

[`evaluation/k3-oir-projection/`](../../../../evaluation/k3-oir-projection/)
has three deliberately separate lanes:

1. source extraction derives the exact PIR graph from admitted future-owner
   Protocol, Construction, Interface, and optional Plan surfaces;
2. target construction independently walks those owners and produces an
   unauthoritative OIR candidate, followed by source-blind local admission;
3. projection validation compares the independently formed graphs and derived
   static contracts under the exact relation profile.

The 70 cases freeze both P01 roles and pressure source and target formation,
all eleven graph fields, local admission, graph mismatch partition, static
contract derivation, value-access closure, K2 Fiat--Shamir coordinates,
Interface adequacy, claims/reductions/terminals, Plan reachability and
resources, identity exclusions, limits, qualified outcomes, support reasons,
and the non-authoritative endpoint-pair probe.

The instrument uses deterministic JSON identities and shallow Python carrier
reflection as explicit surrogates. It neither implements K1 canonical bytes
for these new subjects nor round-trips a final recursive owner grammar or OIR
carrier.

## 6. Final gates

This table records the pre-K3-E K3-D checkpoint. K3-E later rotated the
Foundation regime, repaired the K3-D profiled-identity and host-fault
boundaries, and reclosed the expanded K3-D instrument at 94/94. The K3-E
integration record owns the current result.

| Gate | Result |
|---|---:|
| K1 executable foundations | 116/116 passed |
| K2 Protocol/Fiat--Shamir | 57/57 passed |
| K3-B dependent surfaces | 29/29 passed |
| K3-C Analysis closure | 100/100 passed |
| K3-D OIR projection | 70/70 passed |
| P01 Schnorr/Sigma regression | 69/69 passed |
| P01 source-bound artifact rebuild and replay | passed |
| repository `lit` suite | 171/171 passed |
| repository C++ unit suites | 50/50 passed |
| K3-D Ruff format and lint | passed |
| whitespace/error-marker audit | passed |
| durable documentation manifest | 42/42, no duplicate, missing, or extra entry |
| `docs-next/` local Markdown links | 145 pages and 1,405 links, no missing target or checked heading fragment |
| temporary-note parent inventory | 103/103 non-root pages routed |
| public-tree guard | passed |

The repository-wide test target initially could not create multiprocessing
workers inside the filesystem sandbox. The same unchanged target was rerun
with process-spawn permission and passed; this was an environment restriction,
not a test failure.

## 7. Closure and residual obligations

Bounded K3-D is complete at this recorded scope. At that checkpoint K3-E owned
the next joined K1/K2/K3-B/K3-C/K3-D identity, view, dependency, and no-
backflow audit; the later K3-E record now owns its completed disposition.

The following remain open by construction:

- complete OIR grammar, carrier, execution, and optimization semantics;
- dynamic endpoint traces, state, draw, codec-result, wire, and outcome laws;
- authoritative target-only endpoint pairing and its normalization and duality
  language;
- Fresh, Oracle, module-effect, and generic-Prover endpoint support;
- nonidentity source/target refinement profiles;
- exact K1 canonical-byte parity for new PIR/OIR bodies;
- current implementation correspondence and migration;
- protocol-family coverage, including native FRI/IOR and recursive cases;
- any theorem truth, soundness, knowledge, zero-knowledge, or concrete-hash
  claim; and
- semantic-kernel freeze, normative cutover, and Stage 4B activation.

Any later counterexample showing that an exact endpoint fact cannot be derived
without ambient state, that the eleven-field graph omits static source meaning,
or that a supported endpoint requires a new verifier-observable Core fact
reopens only the smallest affected K3-D, K3-B, or K2 cone under the recorded
reopen discipline.
