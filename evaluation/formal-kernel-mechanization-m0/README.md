# M2 mechanized portable-term calculus and Schnorr denotation

This package extends M0 and M1 in place and answers one exact question:

> Can core-only Lean 4 transcribe the K1 portable-term carrier, typing and
> deterministic evaluation boundary; strictly decode and exactly elaborate
> the R1B finite-Schnorr check and Boolean guard preimages; reproduce every
> available independent K1 term-evaluation oracle vector plus the Python K1
> evaluator's 81 check and two guard results byte-for-byte; and prove
> evaluation determinism, completion monotonicity, and equality of the decoded
> check denotation with `z = a + c*y (mod 3)`?

Run from the repository root:

```sh
python3 -B evaluation/formal-kernel-mechanization-m0/run.py --check
```

The frozen aggregate is
`CannotAnswer/M2-C-TERM-EVALUATION-ORACLE-ABSENT`. Stages 1, 3, 4, and 5 pass,
but Stage 2 cannot pass: the K1 independent oracle's 24 requests have only
`content_id`, `decode`, `encode`, `prior_meta_id`, and `verify_id` operations.
There is no `evaluate` or `evaluate_encoded` vector to reproduce. K1's own
README also states that term evaluation has one Python implementation. Missing
independent evidence is not converted into an affirmative aggregate.

## Authority and toolchain

Nothing in this package is normative. The owner text is
`docs-next/foundation/executable-foundations.md` Sections 5, 7, 8 and Appendix
A.3. The R1B source term comes from
`evaluation/formal-source-target-core-f1r1b/reference_model.py`. No owner page
is edited by M2.

`lean/lean-toolchain` pins `leanprover/lean4:v4.33.1`. Kernel modules import
only package modules and Lean core; there is no Mathlib, Batteries, Std,
VCVio, ArkLib, `sorry`, declared axiom, or Lake dependency. JSON transport is
isolated in `Transport.lean`. If that installed toolchain is unavailable,
Lean-dependent findings become `Unsupported/M0-U-LEAN-TOOLCHAIN` and the
frozen gate fails.

## M2 stages

| Stage | Frozen result |
|---|---|
| 1. Term and typing | `Term.lean` carries all fifteen Appendix A.3 tags, exact value-type/domain carriers, typed failures, algorithm bodies, all nine K1 fixture primitive ABI families, and a relational success/failure typing judgment. |
| 2. Evaluation and K1 oracle | `Eval.lean` carries strict deterministic evaluation, four limits/charges, result preflight, completed ABI envelopes, and all eight noncompletion classes. `CannotAnswer`: the independent oracle has zero term-evaluation vectors, and Section 8 defines no universal noncompletion byte encoding. |
| 3. R1B terms and finite inputs | The M0 decoder accepts the 179,147-byte check preimage and guard preimage; re-encoding is exact. Independently built Lean terms equal both decoded terms. Completion bytes and all four charge coordinates equal the Python evaluator on 81 check and two guard inputs. |
| 4. Proofs | `evaluation_deterministic` proves functional uniqueness. `evaluation_completed_mono` proves that a completion under limits `L` is unchanged under any componentwise larger limits. Both are `sorry`-free. |
| 5. Schnorr equation | `schnorrDenotation` evaluates the finite term. Exhaustion of the four `Fin 3` inputs proves it equals `response = (commitment + challenge*y) % 3`. |
| 6. Cost and underdetermination | The runner records export, build, executable, axiom-report, and total wall time plus line counts. Section 8 lines 1615--1619 deliberately leave domain result payloads and diagnostics to their owners, so refusal bytes cannot be invented here. |

## Exact R1B transport

`export_m2_vectors.py` imports the F1R1B source model and regenerates:

- the complete check and guard `PortableAlgorithmBody` bytes and digests;
- the check's exact `nat.lt` `SemanticPrimitiveRef` carrier;
- 81 check inputs and two guard inputs;
- each Python K1 completion in JSON datum transport and canonical hexadecimal;
- each exact `steps`, `iteration_items`, `primitive_work`, and `result_bytes`
  record; and
- the independent-oracle request inventory proving the absence of term
  evaluation vectors.

The committed `vectors/m2-term-calculus.json` is compared byte-for-byte with a
fresh export on every run. Lean starts from each complete preimage's exact
octets, invokes the retained M0 strict decoder, elaborates the resulting datum
as `Algorithm`/`Term`, and re-encodes it. The source algorithm's diagnostic
name is never used to select denotation.

## Mechanized boundary

`Term.lean` retains exact domain coordinates while exposing the nine finite
schema constructors. `HasType` is parameterized by an exact-reference
primitive ABI relation. This reflects the Foundation split: primitive names
and versions are diagnostic; an authenticated exact reference selects its
type rule and denotation.

`Eval.lean` takes an exact-reference-qualified deterministic primitive
function. M2 instantiates only `nat.lt`, the sole primitive reachable from the
R1B term. This is enough to evaluate the check without pretending that core
Lean supplies SHA-256 or every module-owned primitive provider. The theorem
about larger limits is over a fixed admitted term, environment, primitive
denotation, failure-ordinal map, completion bound, and fuel.

The exact theorem closures printed by `Axioms.lean` are:

- `evaluation_deterministic`: `propext`;
- `evaluation_completed_mono`: `propext`; and
- `schnorr_denotation_eq_closed_form`: `propext`, `Quot.sound`.

These are within the package's pre-existing standard Lean allowance of
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or
native-decision axiom.

## Frozen vectors

| File | Role |
|---|---|
| `m2-term-calculus.json` | Exact R1B preimages, direct primitive carrier, 83 Python K1 evaluation rows, charge records, and K1 oracle inventory. |
| `k1-encoding-vectors.json` | Retained M0 canonical K1 oracle bodies and malformed cases. |
| `structural-negatives.json` | Retained M0 malformed encodings. |
| `body-digests.json` | Retained M1 D1 body digests. |
| `pcgraph-construction.json` | Retained M1 Core/module inputs and finite graph outputs. |

## CannotAnswer findings

- `M2-C-S2-K1-TERM-EVALUATION-ORACLE-ABSENT`: there are zero independent K1
  term-evaluation requests. The 83 R1B rows are exported from the same Python
  K1 implementation whose result is being compared, so they are bounded
  cross-language differential evidence, not independent oracle evidence.
- `M2-C-S2-NONCOMPLETION-BYTES-UNDEFINED` and
  `M2-C-S6-SECTION8-NO-UNIVERSAL-RESULT-BYTES`: Foundation Section 8 lines
  1615--1619 explicitly declines to define one universal Result payload,
  diagnostic vocabulary, or domain-wide precedence. M2 represents all eight
  classes but does not invent canonical refusal bytes.
- `M2-C-NO-GENERAL-K1-EVALUATOR-CONFORMANCE`: the R1B term uses only variables,
  literals, conditionals, and `nat.lt`. Its 83 rows do not validate all term
  constructors, primitive formulas, typed failures, or limit-refusal charge
  prefixes.

The retained five M1 Section 11 wording findings and three M0 non-claims remain
frozen. M2 found no basis for a Foundation owner-page change, so it proposes no
owner delta.

## Cost ledger

Every run emits machine-readable values under `metrics.timings`,
`metrics.lean_line_counts`, `metrics.axioms`, and `metrics.m2`. In the first
warm M2 run, the complete gate took 83.656 seconds: 74.305 seconds regenerated
the 83 Python rows, 0.412 seconds built Lean, 4.948 seconds ran the compiled
executable, and 0.506 seconds printed axioms. These are measurements from that
run, not stable performance claims.

## What the frozen check does and does not establish

The frozen check establishes only that, under the pinned toolchain:

- all retained M0/M1 checks still pass;
- the exact R1B preimages decode, elaborate, and re-encode in Lean;
- the 83 exact R1B rows agree with the current Python K1 evaluator in
  completion bytes and abstract charges; and
- the three named M2 statements elaborate without `sorry` and with only the
  reported standard axioms.

It does not establish the affirmative M2 aggregate, independent K1
term-evaluation conformance, universal evaluator correctness, owner-page
normativity, compiler/backend correspondence, arbitrary primitive-provider
conformance, constant-time behavior, protocol soundness, Fiat--Shamir or
random-oracle security, QROM applicability, production readiness, or a
decision to adopt Lean as a durable reference twin.
