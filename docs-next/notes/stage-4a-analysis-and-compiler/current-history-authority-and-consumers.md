# Current history, executable authority, and consumers

> **Document kind:** Temporary Stage 4A reconstruction supplement
> **Document state:** Complete for Stage 4A.1; target-neutral
> **Authority:** None. This page records current implementation history,
> executable-authority placement, consumer behavior, and assurance limits. It
> does not elevate code over current specifications, select a target, establish
> independent assurance, or authorize implementation or migration.
> **Reconstructed:** 2026-08-22
> **Disposition:** Absorb relevant current-to-target gaps and trust distinctions
> into durable owners and convergence; delete this page with the temporary
> package.

## 1. Re-checking and independent-correspondence scope

The current system has three different assurance mechanisms that must not be
called by one name.

`zkc-derive --check` reloads an admitted artifact, a checker-supplied signature,
and the recorded request and plan, re-runs the native evaluator, and compares
the recomputed judgment digest. It is cross-process proof-object replay that
does not trust the producer's recorded conclusion, but it reuses the native
checker implementation. The tool's ingress, derivation, witness production,
and check branches are visible in
[`tools/zkc-derive/zkc-derive.cpp`](../../../tools/zkc-derive/zkc-derive.cpp).

The Python oracle is an implementation-diverse but deliberately partial twin.
It independently reconstructs canonical signature content and the structural
and typing skeleton of derivations: sites, bindings, premise edges, subjects,
indices, resources, and inherited hypotheses. It stops before numeric bound
composition by design, as stated by
[`reference/oracle/derive.py`](../../../reference/oracle/derive.py) and tested
by the [derivation-skeleton parity
suite](../../../test/Soundness/derive-skeleton-sync.test). Signature and
skeleton parity therefore establish exact agreement at those boundaries, not a
second full `DERIVE` implementation, numeric-bound validation, theorem truth,
model adequacy, or cryptographic security.

Compiler `DECIDE` is a third mechanism. It freshly recomputes producer outputs
under the same configured artifact semantics, domain providers, transform
families, Soundness context and evaluator, objective semantics, and arithmetic.
It distrusts submitted domains, candidates, bounds, scores, eligibility, and
selection, but it is not implementation-independent checking or common-mode-
bug elimination. The current specification states this limit in its
[`DECIDE` and trust-boundary
sections](../../../docs/spec/compiler.md#10-decision-checking).

```text
native witness replay
  != partial independent signature/skeleton parity
  != implementation-independent full Analysis checking
  != theorem or model truth

fresh Compiler recomputation under identical semantic authorities
  != an independent implementation of those authorities
```

## 2. Current executable authority and live-value boundary

| Surface | Current executable authority | Exact limit |
|---|---|---|
| Admitted artifact ingress | `AdmittedPirArtifact` or exact Compiler `ArtifactSemantics` reconstructs the owned semantic view before evaluation | An ID, payload, or view-shaped value does not authenticate itself |
| Soundness evaluation | Immutable `SoundnessCatalog`/`SoundnessContext`, closed rule bodies, bindings, projections, machine deciders, and `DERIVE` determine the evaluator result | Cryptographic meaning still assumes rule truth and encoding, binding faithfulness, hypotheses, notion/game definitions, and Protocol-to-concrete-model correspondence |
| Analysis products | `SecurityJudgment` and `DerivationResult` are owned public values returned by the evaluator and re-checkable from exact inputs | Their data shape is not an opaque live capability and does not itself prove evaluator provenance |
| Compiler evaluation | Configured artifact semantics, transform and derivation-domain providers, transform families, Soundness evaluator, objective profiles, and comparison logic jointly determine the decision | `DECIDE` reuses these semantic authorities; it checks producer output, not the correctness or independence of their implementations |
| Compiler products | `CompilerResult` is selected ordinal or none; `DecisionVerdict` reports equality with fresh recomputation | Neither value is an independently interpretable candidate, durable replay object, or opaque decision capability |

The relevant public value shapes are visible in
[`SoundnessRuntime.h`](../../../include/zkc/Soundness/SoundnessRuntime.h),
[`SoundnessEvaluator.h`](../../../include/zkc/Soundness/SoundnessEvaluator.h),
and [`CompilerCore.h`](../../../include/zkc/Compiler/CompilerCore.h). Current
Soundness residual trust is stated normatively in [what the kernel
establishes](../../../docs/spec/soundness.md#8-what-the-kernel-establishes).

The target must preserve the distinction between a semantic value, a checked
occurrence that produced or rechecked it, and the process-local capability a
later consumer may rely on. Serialization may carry the value and replay
inputs; it cannot carry live authority.

## 3. Evolution and accumulated design pressure

The current model did not arrive as one frozen design.

| Commit | Current-model pressure introduced or tightened |
|---|---|
| `9d335e9` (2026-08-10) | Baseline Soundness and Compiler architecture |
| `3f9f8b9` | Bound and refusal behavior in loaders and passes |
| `02e28b8`, `bb78717` | Relation contract, correspondence, and authored-instance surfaces |
| `1a4e5fc` | Process boundary, fact declaration, and documentation-claim scope |
| `b6d0e0d` | Identity-bearing security quantification |
| `44174d4`, `ef0ae7d` | Composition kernel and corrected interleaving-decision placement |
| `47ff6fa` | Full family artifact judgment through Fiat--Shamir |
| `9e6a5ff`, `c44712e`, `3b8e247`, `6cea581` | Value-profile, lookup, consumed-claim, and transcript-material refinements |

This history explains several pressures without deciding the target. The
Soundness view and rule vocabulary accumulated responsibilities as new
families arrived; quantification and artifact-global coverage appeared after
the normative core shape; and Compiler implementation and tests moved with
shared Soundness and value-profile changes while
[`docs/spec/compiler.md`](../../../docs/spec/compiler.md) itself retains only
the baseline file history.

The lesson is not that later code is preferable. It is that candidate study
must test extension locality, source-owned read closure, and whether a new
property or transform family changes one profile or the semantic center.

## 4. Current consumers, persistence, and outcome collapse

| Consumer or surface | Current use | What it does not establish |
|---|---|---|
| `zkc-derive` | Produces a persisted derivation witness and, in check mode, re-runs the native derivation under the checker-supplied signature and compares digests | An independent full checker, theorem truth, model adequacy, or authority carried by the witness bytes |
| `zkc-registry-lint` | Validates and emits canonical Soundness signature content, declaration revisions, and digest | A rule application or property judgment |
| Python oracle | Checks signature bytes and selected structural/typing parity boundaries | Numeric bound composition or full `DERIVE` parity |
| `zkc-relation` | Reuses `SealedSoundnessView` while producing current relation-correspondence reports | Relation satisfaction or a justification for making the Soundness view a general cross-domain fact root |
| Compiler library and test passes | Reuses `DERIVE` during in-memory candidate assessment and decision recomputation | A production Compiler command, persisted request/decision schema, or cold decision replay |

The exact tool surfaces are the [`zkc-derive`](../../../tools/zkc-derive/),
[`zkc-registry-lint`](../../../tools/zkc-registry-lint/), and
[`zkc-relation`](../../../tools/zkc-relation/) sources. The tools build list and
`zkc-opt` registration show no production Compiler command; current Compiler
behavior is exposed through its library and test passes.

The current Analysis operational outcome is one conditional judgment or one
typed refusal carrying phase, code, location, and detail. Those diagnostics
are useful, but they do not constitute semantic `Negative`, `Unsupported`,
`CannotAnswer`, `Malformed`, or `CheckerFailure` results.

Compiler compresses further. A refused candidate derivation and an unavailable
exact proof-codec width are converted to one internal `CandidateIneligible`
marker; other errors abort the whole compilation. Selection discards per-
candidate reasons, and the public record retains only an ordinal or
`no_selection`. Current `no_selection` therefore means that no member survived
the current assessment pipeline in the exact domain. It does not say that
every candidate's requested semantic property was negatively decided, nor
distinguish missing basis, unsupported analysis, and an affirmative constraint
failure.

## 5. Reconstruction consequence

The target must make these distinctions explicit:

- same-checker replay versus implementation-diverse correspondence;
- semantic value versus checked occurrence versus live capability;
- direct target re-analysis versus property-specific transport;
- semantic negative versus refused, unavailable, unsupported, malformed, or
  failed checking;
- candidate-local assessment facts versus a whole-decision failure; and
- a selected or no-selection fact versus the complete basis needed for cold
  replay.

No full Soundness test rerun is needed to reconstruct those current meanings.
The detailed reconstruction explicitly reports inspected rather than newly
executed Soundness coverage, while the current Compiler test result remains a
separately bounded live observation.
