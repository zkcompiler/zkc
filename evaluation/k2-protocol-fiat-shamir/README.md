# K2 Protocol/Fiat--Shamir reference instrument

This bounded package exercises the selected K2 Protocol/Fiat--Shamir model. It
is research evidence, not current zkc authority, a compiler implementation, or
a cryptographic proof.

`reference_model.py` imports K1's canonical `Datum` and typed content-identity
machinery directly. It does not reproduce a second foundation. On top of that
fixed basis it implements:

- an exact finite total interaction schedule with explicit nested scope opens;
- first-class statements, public context and parameters, and optional
  verifier-private inputs;
- causal prover generation through a prefix-only `ProverView`, separately from
  completed-record replay;
- transitive dependency-derived public-coin eligibility, with no authored
  `publicly_recomputable` escape hatch;
- explicit finite `InfluenceAtom` extraction and required-versus-observed
  comparison, including challenge conditions and reduction-required
  publications;
- one exact transcript initialization, framing, absorption, squeeze, state
  advance, bounded rejection-sampling, and typed-exhaustion ABI;
- a Core-scoped transcript-construction identity, with explicit Core,
  construction-self, and application-domain initialization headers;
- the same literal Core under Fresh and Fiat--Shamir challenge interpretations,
  while Fresh records carry no FS construction, transcript, or namespace;
- a standard finite native-oracle publication/query/answer extension;
- exact bounded reduction declarations, publication-to-challenge obligations,
  linear claim-consumer uses, a Last-Challenge falsifier, and terminal closure;
- checked Fresh/Fiat--Shamir structural correspondence.

Run the finite gate from the repository root:

```sh
python3 -B evaluation/k2-protocol-fiat-shamir/run.py --check
```

The tests include positive Schnorr and native-oracle fixtures and negative
mutations for statement binding, exact prefixes, duplicate frames, mandatory
prover influence, challenge-condition framing, nontrivial guard framing,
per-draw namespaces, transitive dependency-sensitive public-coin
eligibility, causal future reads, scope-local input visibility, sampling
retries/exhaustion, typed and scope-correct oracle indices, oracle lifecycle and
answers, extension refusal, schedule
identity, nested-scope continuity, grinding separation, claim linearity,
reduction-required Last-Challenge ordering, and terminal closure. The frozen
gate runs 48 tests.

## Evidence boundary

Passing the gate demonstrates only these finite executable cases. The fixture
predicates stand in for already admitted K1 portable Bool algorithms; they are
not a second general evaluator. The model does not establish protocol
soundness, Fiat--Shamir theorem applicability, ROM/QROM security, extractor
correctness, cryptographic primitive correctness, complete IOP/PIOP/FRI
coverage, unbounded recursion, implementation conformance, or production
readiness. Strategy generation establishes causality only relative to the
restricted API and concrete strategies exercised here; replay intentionally
makes no strategy-existence claim. This finite instrument also selects one
challenge draw per occurrence, vector-indexed native oracles, unconditional
scope openings, one closing terminal, linear claims only, and fixture-equivalent
bounded predicates. It does not implement the durable model's complete raw
carrier, joint-draw laws, opaque oracle bindings, guarded early terminals,
reusable claims, or actual K1 portable-algorithm resolver path.
Reduction applications are declarations anchored at schedule coordinates in
this instrument rather than first-class executable reduction effects, and its
claim identifiers carry no theorem semantics beyond the checked linear-use
ledger.
