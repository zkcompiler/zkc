# M2 Mechanized Portable-Term Calculus and Schnorr Denotation

> **State:** `CannotAnswer/M2-C-TERM-EVALUATION-ORACLE-ABSENT`; Stages 1, 3,
> 4, and 5 pass, while the required independent Stage 2 oracle evidence does
> not exist
> **Authority:** None. This experiment neither edits nor publishes Foundation,
> PIR, Analysis, or profile identities.
> **Executable evidence:**
> [`evaluation/formal-kernel-mechanization-m0`](../../../../evaluation/formal-kernel-mechanization-m0/README.md)

## 1. Question and answer

M2 asks whether core-only Lean 4 can transcribe the K1 portable-term and
evaluation boundary, strictly decode and elaborate the two R1B algorithm
preimages, reproduce all available independent K1 term-evaluation goldens and
all 83 finite R1B evaluations, and prove deterministic replay monotonicity and
the finite Schnorr equation.

The mechanization and R1B parts are affirmative. Lean strictly decodes and
exactly re-encodes both preimages, independently reconstructs both terms,
agrees with the Python evaluator on all 81 check and two guard completion bytes
and four-dimensional charge records, and checks all three requested theorems
without `sorry` or nonstandard axioms.

The aggregate is nevertheless `CannotAnswer`. The K1 independent oracle has
24 requests and no `evaluate` or `evaluate_encoded` operation. Its operations
are exactly `content_id`, `decode`, `encode`, `prior_meta_id`, and `verify_id`.
K1's package README says directly that term evaluation has one Python
implementation. The 83 source rows therefore remain single-implementation
Python-to-Lean differential evidence, not independent oracle evidence.

## 2. Exact source and authority boundary

M2 reads the portable carrier and laws from
`docs-next/foundation/executable-foundations.md` Sections 5, 7, 8 and Appendix
A.3. It reads the operational model from
`evaluation/k1-executable-foundations/reference_model.py`. The two R1B term
preimages come only from `finite_schnorr_algorithm` and
`boolean_identity_algorithm` in
`evaluation/formal-source-target-core-f1r1b/reference_model.py`.

The package keeps the existing owner handoff:

```text
authenticated Foundation term and primitive references
  -> exact portable algorithm preimage
  -> admitted deterministic evaluator and request limits
  -> completed ABI value or operational noncompletion
  -> PIR Check/guard consumer
```

The Lean files are definition and proof text under measurement. They are not a
new owner, a published Foundation body, or evidence that compiler or provider
code realizes the same denotation.

## 3. Stage 1: portable terms and typing

`M0/Term.lean` adds the nine finite schema forms while retaining each exact
value-domain coordinate. It transcribes all fifteen Appendix A.3 term tags:
literal, variable, let, record construction, projection, injection, case,
sequence construction, sequence length, typed failure, strict index, bounded
append, exact primitive call, bounded iteration, and conditional.

`termOfDatum` accepts only the exact tag and payload shape. `algorithmOfDatum`
requires fields 0--3 and therefore retains the syntax-derived direct primitive
sequence. `termDatum` and `algorithmDatum` provide the reverse direction used
for byte equality.

`HasType` is a relation parameterized by an exact-reference primitive ABI
judgment. It tracks the success type and ordered failure contributions through
binders, structural operators, primitives, and iteration. The package also
names all nine K1 fixture ABI families, but names and versions never select a
primitive denotation.

## 4. Stage 2: evaluator and the missing oracle

`M0/Eval.lean` is a total fuelled function over admitted terms. The fuel is a
host totality guard above K1's authenticated depth bound, not a fifth request
limit. Evaluation is strict and left-to-right. Primitive semantics is supplied
as a deterministic exact-reference-qualified function; the R1B run installs
only the check's exact `nat.lt` reference.

The request envelope carries the four Foundation coordinates: term steps,
iteration items, primitive work, and completion bytes. `enforce` performs the
maximum-completion preflight and accepts a completed run only when all four
charges fit. It represents all eight Section 8 noncompletion classes.

Two exact findings prevent Stage 2 from passing:

1. `M2-C-S2-K1-TERM-EVALUATION-ORACLE-ABSENT`: the frozen independent oracle
   contains zero term-evaluation requests. There is therefore no independent
   completion or refusal vector to reproduce.
2. `M2-C-S2-NONCOMPLETION-BYTES-UNDEFINED`: Foundation Section 8 lines
   1615--1619 explicitly says that Foundation does not define one universal
   Result, payload enum, diagnostic vocabulary, or multi-domain precedence.
   M2 cannot encode refusals byte-for-byte without inventing owner law.

The second item is an intentional authority boundary, not a proposed owner-page
repair. M2 records no Proposed delta.

## 5. Stage 3: exact R1B preimages and finite evaluations

The source exporter freezes the complete preimages rather than a printer AST:

| Algorithm | Preimage bytes | SHA-256 |
|---|---:|---|
| finite Schnorr check | 179,147 | `4a89ff48f38c213b93cacd4f31819804de7f898b7b836b9cf12b3776e219abbd` |
| Boolean guard | 766 | `0ea838ec2c6a5e58d9237c57622ebd7de59ca1c6d4d9386ab8c1044567744521` |

The guard size and digest above are frozen by `m2-term-calculus.json`; the
runner rejects any regeneration drift. Lean applies the retained M0 strict
decoder to both exact byte strings, elaborates their datum trees as terms, and
requires re-encoding equality with the original bytes.

The check term is also rebuilt independently from `switch3`, `responseTest`,
and all 27 `(y,a,c)` branch constants. Its `termDatum` equals the decoded term.
The guard equals exact de Bruijn variable zero at root Boolean type.

For every `(y,a,c,z) in Fin(3)^4`, Lean and Python agree on the exact completed
datum bytes and all four charges. The guard agrees on false and true. The check
rows exercise variables, literals, conditionals, and exact `nat.lt`; they do
not exercise the rest of the calculus.

## 6. Stage 4: determinism and larger-limit replay

`evaluation_deterministic` proves that fixed primitive semantics, failure
mapping, fuel, term, environment, completion bound, and limits have one result.

`evaluation_completed_mono` proves the replay property in the direction the
owner page uses: if evaluation under `L` completed with value and charge, then
evaluation under any componentwise larger `L'` completes with the same value
and charge. The proof factors through `Charge.fits_mono`; it does not claim
that a previously noncompleted request will complete under a larger limit.

`#print axioms` reports:

| Theorem | Axioms |
|---|---|
| `evaluation_deterministic` | `propext` |
| `evaluation_completed_mono` | `propext` |
| `schnorr_denotation_eq_closed_form` | `propext`, `Quot.sound` |

There is no `sorryAx`, declared axiom, or native-decision axiom.

## 7. Stage 5: the Schnorr denotation

`schnorrDenotation` is defined by evaluating `finiteSchnorrTerm` with the
exact-reference `nat.lt` denotation. The theorem exhausts four `Fin 3` inputs
inside Lean and proves:

```text
schnorrDenotation(y, a, c, z)
  = decide(z = (a + c*y) mod 3).
```

This closes the first F2-O0 operational gap for the bounded R1B term. It does
not supply the missing relation, witness, honest-prover, sampling, transcript,
or theorem-applicability premises, and it is not a Schnorr security proof.

## 8. Cost ledger and remaining underdetermination

The first warm package run recorded 83.656 seconds total. Regenerating the 83
Python rows dominated at 74.305 seconds; warm Lean build was 0.412 seconds,
compiled execution 4.948 seconds, and axiom reporting 0.506 seconds. The runner
emits these measurements, all source line counts, theorem closures, and stage
booleans on every run.

`M2-C-S6-SECTION8-NO-UNIVERSAL-RESULT-BYTES` is the only new owner-text
underdetermination. Sections 5 and 7 determine the exact R1B term, completed
ABI envelope, order, and abstract charges used here. Section 8 deliberately
leaves privacy-safe diagnostic payloads to the owning evaluator, so M2 records
the outcome partition without manufacturing canonical refusal bytes.

## 9. Nonclaims and next evidence

The 54 frozen findings contain 41 `Affirmative` and 13 `CannotAnswer` outcomes.
They retain every M0/M1 result. They do not establish an affirmative M2
aggregate, general K1 evaluator conformance, all-constructor execution,
primitive-provider correctness, exact partial charges for every limit refusal,
Foundation publication, arbitrary algorithm correctness, compiler/backend
correspondence, theorem applicability, protocol soundness, Fiat--Shamir,
random-oracle, concrete-hash or QROM security, or production readiness.

The direct reversal condition for the aggregate is an independently
implemented K1 term-evaluation oracle with frozen completion and refusal rows
covering the requested evaluation surface. Adding only more rows from the same
Python evaluator does not satisfy that condition.

## Handoff

- Branch: `lane/m2-term-calculus`.
- Commit hash: unavailable in this run because the managed filesystem exposes
  this clone's `.git` directory read-only; real `git add -A` exits 128 while
  creating `.git/index.lock`. The final checks used a complete temporary Git
  index and object store, so lifecycle inventory saw exactly the intended
  staged tree without changing the branch.
- Verification: package runner `--json` exited 0 in 83.656 s;
  `python3 -B checks/run.py validate` exited 0 in 0.04 s;
  `python3 -B checks/run.py run --tier developer` exited 0 in 0.84 s (7/7);
  `python3 -B checks/run.py run --check research.kernel-mechanization-feasibility`
  exited 0 in 85.23 s (runner time 85.175 s). These measurements preceded the
  final Handoff-only note edit and are rerun after restaging that edit.
- Aggregate: `CannotAnswer/M2-C-TERM-EVALUATION-ORACLE-ABSENT` (41 Affirmative,
  13 CannotAnswer findings).
- Non-claims: no owner publication, independent term-evaluation conformance,
  general evaluator correctness, compiler/provider correspondence, theorem
  applicability, protocol or cryptographic security, QROM, or production
  claim.
- Surprises: the independent K1 oracle contains no term-evaluation operation;
  exact R1B regeneration is dominated by repeated Python authentication of the
  179,147-byte term; Section 8 intentionally provides no universal refusal
  bytes; the developer tier needed its already-locked virtual environment
  copied from the read-only primary checkout because the default `uv` cache is
  also read-only and network resolution is unavailable.
- Where this brief was wrong: it presupposed K1 term-evaluation oracle vectors
  that do not exist, requested byte-for-byte refusal encoding despite Section
  8 lines 1615--1619 declining to define such a universal carrier, and required
  a commit to contain its own literal hash, which Git content addressing makes
  impossible. Local `AGENTS.md` and `.claude/CLAUDE.md` were also absent from
  this lane clone, so their read-only primary-checkout copies supplied those
  instructions.
