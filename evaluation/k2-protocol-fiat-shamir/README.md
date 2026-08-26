# K2 Protocol/Fiat--Shamir reference instrument

This bounded package exercises selected K2 Protocol/Fiat--Shamir contracts and
behavioral shapes. It is research evidence, not current zkc authority, a
compiler implementation, protocol conformance, or a cryptographic proof.

`reference_model.py` imports K1's canonical `Datum` and typed content-identity
machinery directly. It does not reproduce a second foundation. On top of that
fixed basis it implements a fixture-exact finite model with:

- an exact finite total interaction schedule with explicit nested scope opens;
- first-class statements, public context and parameters, and optional
  verifier-private inputs;
- causal prover generation through a prefix-only `ProverView`, separately from
  completed-record replay;
- transitive dependency-derived public-coin eligibility over every represented
  public activity (`ProverMessage`, `VerifierMessage`, `Challenge`,
  `OraclePublish`, `OracleQuery`, `OracleAnswer`, `Check`, and `Terminal`), with
  private guards included and no authored `publicly_recomputable` escape hatch;
- refusal of authored `ProverMessage` dependencies, because that field is not
  present in the target Core carrier;
- exact whole-prefix comparison before every challenge draw, plus an exported
  required-influence ordered-subtrace audit view covering challenge conditions,
  reduction-required publications, and challenge draws;
- one fully specified fixture transcript initialization, framing, absorption,
  squeeze, state advance, bounded rejection-sampling, and typed-exhaustion
  behavior;
- a Core-scoped transcript-construction identity, with explicit Core,
  construction-self, and application-domain initialization headers;
- the same literal Core under Fresh and Fiat--Shamir challenge interpretations,
  while Fresh records carry no FS construction, transcript, or namespace;
- a standard finite native-oracle publication/query/answer extension;
- fixture-bounded reduction declarations, publication-to-challenge
  obligations, linear claim-consumer uses, a Last-Challenge falsifier, and
  terminal closure;
- checked Fresh/Fiat--Shamir structural correspondence.

Two narrow contract-vector families are target-exact rather than merely
fixture-shaped. They are built and admitted through K1 directly:

- `GuardOutcome` false and true bodies contain the exact K1 `MF` and `MT`
  Boolean datums, not a generic `MetaVariant`;
- `OracleAnswer` absent and present bodies carry the exact lookup-result sum
  `V(0, Unit) | V(1, element)`, admitted at the derived result type rather than
  at the bare element type.

Run the finite gate from the repository root:

```sh
python3 -B evaluation/k2-protocol-fiat-shamir/run.py --check
```

The tests include the two exact contract-vector families above, positive
Schnorr and native-oracle fixtures, and negative mutations for statement
binding, exact prefixes, duplicate or reversed influence, mandatory public
activity influence, challenge-condition framing, nontrivial guard framing,
private-guard public-coin failure, per-draw namespaces, transitive
dependency-sensitive public-coin eligibility, authored prover dependencies,
causal future reads, scope-local input visibility, sampling
retries/exhaustion, typed and scope-correct oracle indices, oracle lifecycle
and answers, extension refusal, schedule identity, nested-scope continuity,
grinding separation, claim linearity, reduction-required Last-Challenge
ordering, and terminal closure. The frozen gate runs 54 tests.

## Evidence boundary

Passing the gate demonstrates only these finite executable cases. Except for
the two K1-backed contract-vector families identified above, the carrier and
execution results are fixture-exact or behavioral-shape evidence, not exact
Appendix-A conformance. The fixture predicates stand in for already admitted
K1 portable Bool algorithms; the instrument does not build `AlgorithmUse`, run
the K1 resolver/evaluator/evaluation-contract path, or provide a second general
evaluator. Its squeeze, advance, accept, and decode helpers likewise exercise
the selected behavior without claiming the durable algorithm ABI.

The model does not establish protocol soundness, Fiat--Shamir theorem
applicability, ROM/QROM security, extractor correctness, cryptographic
primitive correctness, complete IOP/PIOP/FRI coverage, unbounded recursion,
implementation conformance, or production readiness. Strategy generation
establishes causality only relative to a restricted Python API and the concrete
strategies exercised here; it does not implement a non-serializable causal
capability. Replay intentionally makes no strategy-existence claim.

Public-coin eligibility is checked over this fixture's represented sinks and
dependency graph, not the durable model's complete `PCNode`/module graph. The
runtime does not represent verifier-only Oracle visibility; it uses
vector-indexed native oracles and exercises present answers. The exact
absent/present contract vectors demonstrate that both target answer bodies are
formable, not that the runtime executes sparse absent lookups.
Reduction applications are declarations anchored at schedule coordinates
rather than first-class executable reduction effects, and claim identifiers
carry no theorem semantics beyond the checked linear-use ledger.

This finite instrument also selects one challenge value per occurrence,
unconditional scope openings, one closing terminal, linear claims only, and
fixture-equivalent bounded predicates. It does not implement the durable
model's complete raw carrier and channel laws, joint draws, opaque oracle
bindings, guarded early terminals, reusable or shared claims, or complete
reduction semantics.
Its Schnorr control accepts according to the modular equation implemented by
this instrument; that equation is a positive behavioral control, not an
independently admitted K1 check algorithm or a proof of Schnorr soundness.
