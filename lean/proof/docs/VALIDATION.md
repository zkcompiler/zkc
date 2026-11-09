# Packages 1 and 2 validation

Current combined unit, 9 November 2026. Lean is pinned to 4.35.0.

| Gate | Result and scope |
|---|---|
| Complete proof package | `lake build` from `lean/proof` passed (2,815 jobs including cached dependencies). Public core and every model/control module compiled with strict implicit arguments and warnings-as-errors. |
| Exhaustive axiom audit | After strengthening private-data coverage, `lake build ProtocolProofChecks` passed for 1,912 owned declarations, including private/generated declarations. Only `propext`, `Classical.choice`, `Quot.sound` are allowed transitively. The coverage guard rejects importing public module data alone. |
| Shared program | Full shared package build passed; original generic declarations are preserved exactly apart from imports/module paths. Focused concrete Region/derivation/compatibility/context consumers passed in the extraction worker. |
| Package boundaries | Program/core/proof closure and import check passed for 1,596 modules; Lake ownership passed 23 provider checks. Eight package/reproduction controls passed. Exhaustive audit-import maintenance checks ten files. |
| Claim preservation | The existing `lean/checks/claims.lock.json` is byte-identical to the pre-extraction base. No fresh concrete-security claim capture is asserted. |
| Model scope | Arbitrary adaptive/nested finite checks, frozen oracle sampling, shared state/challenge, total decoding including malformed failure, all five stops, initial mixtures, property access and upper/lower transfer refusals. |

The first combined invocation accidentally selected the root default Lean 4.34.1 and
failed in dependencies. That run is excluded. The passing combined build and subsequent
private-data audit used the package's pinned Lean 4.35.0. Reproduction commands must run
from the package directory or specify the toolchain explicitly.

The final independent source review and its disposition are recorded in REVIEW.md.
Worker evidence below is retained as historical scope, not substituted for this combined
gate. No actual imported protocol, compiler/native pipeline, fresh security reports or
independent-kernel replay was part of these bounded framework packages.

---

# Process-facing proof-core validation

Date: 9 November 2026. Scope: `lean/proof`, consuming the shared `ZkcProgram`
foundation at `../program`. This validates the proof-owned Process migration;
cross-package wiring, Package 2 and actual protocol integration remain separate.

## Final package gate

From `lean/proof`:

```sh
lake +leanprover/lean4:v4.35.0 build
```

Passed with `autoImplicit = false` and `warningAsError = true`, including the public
library, all seven example/control modules and `ProtocolProofChecks`. The transitive
all-declaration audit checked **1,542 package declarations**, including generated and
private declarations, allowing only `propext`, `Classical.choice` and `Quot.sound`.
All **43 local Lean modules** are reachable from the three package roots. No Lean
source changed after this gate. The incremental command took 30.02 seconds and Lake
reported 2,808 jobs, including cached dependencies; this is not a build benchmark.

The local build log is `.lake/process-proof-final-build.log`; the exact Lean source
fingerprints are in `.lake/process-proof-final-sources.json`. Focused module checks
preceded the final gate. The package build itself ran the standard-axiom audit, so
no second audit command or broader production suite is implied.

## Checked semantic boundaries

| Boundary | Evidence |
| --- | --- |
| Full shared semantics | `Internal.complete_execution` covers every lawful monadic handler, full outcome, reached state and ordered events, including an existing prefix. `Internal.encode_bind` preserves failure-aware bind. |
| One probability interpretation | `System.runFrom`, `run`, and `experiment` use the same upstream kernel interpretation. `runFrom_done`, `runFrom_halt`, `runFrom_call`, and `runFrom_bind` expose its complete equations. |
| Normalization and deterministic agreement | `runFrom_mass_one`, `run_mass_one`, Markov instances, `runFrom_eq_dirac`, `run_eq_dirac`, and `experiment_eq_dirac`; no stopped path loses mass. |
| Measurable quantitative semantics | `wpFold_eq_lintegral_runFrom` and whole-initial-law expectation/indicator equations; arbitrary measurable states, events and final results. Countable replies and measurable rewards remain explicit premises. |
| Checked contracts and root reuse | Process upper/lower rules and adequacy reuse `Internal.Contract`; both public roots reuse `Internal.Closure`. `Installation` transports exact complete outcomes and whole initial measures. |
| Resources | `Internal.bound_eq_charge` equates the structural Process bound with upstream `OpSpec.charge` on the stop-aware encoding. This counts abstract calls, not runtime. |
| Complete models | `AdaptiveChecks` retains adaptive strategies, arbitrary nested rounds, exact bounds and honest completeness. `SharedState` retains persistent challenge/counters, audit erasure, adaptive replies, whole initial coverage and Process inlining. |
| Property meanings | Existing extraction, simulation, promise-gap, half-abort, receipt, admission and resource controls pass. No existing model/profile declaration was dropped; the old connection is named installation. |
| Stop controls | `ExecutionControls` checks all five reasons, failed-call state and log preservation, skipped continuations, ordinary-bind failure, and mixed returned/stopped initial laws. `ContractControls` closes complete stopped events through both roots and adequacy directions and refutes omission of either stopped-bind obligation. |

A source/import audit found strict module headers throughout, no concrete IR imports,
no public FreeM algorithm carrier, no compatibility aliases, and no `sorry`, new axiom,
`native_decide`, blanket exposure section or warning suppression. Tracked changes are
confined to `lean/proof`; tracked `lean/program` sources are unchanged. The proof manifest
records the relative shared-package dependency already required by its Lake file.

## Dependency and validation scope

| Dependency | Verified revision |
| --- | --- |
| Lean | `v4.35.0` |
| VCVio | `96754a37e739270ac5bb8fe7deaeafef6964b688` |
| PolyFun | `a5edfe2dd24d9d76f9a13cc1f131b220617ad534` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The three upstream worktrees were verified clean. Individual dependency symlinks reuse
existing caches; the proof and shared-program build directories are local directories,
not links to a shared writable build directory. No upstream source or revision changed.

The shared-state inlining theorem is for arbitrary Process clients under its deterministic
component implementation. It does not supply the generic differing-interface probability
composition API planned for Package 2. No native/compiler tests, concrete-subject build,
security-package integration, construction engine, external protocol adoption, PPT/runtime
adequacy or independent review of this migration is claimed. Historical review and build
records below apply to their named earlier checkpoints.

---

# Historical property-interface validation

Date: 9 November 2026. Scope: the independent `lean/framework` package. This is not a
production migration, source/IR correspondence result, or complete cryptographic client.
The original standalone checkpoint remains preserved at `276b6314647b8ba63b2b71a5ec5c46d68eaed749`.

## Current gate

The final incremental `lake build` passed with `autoImplicit = false` and
`warningAsError = true`, including all five example/control modules and `ProtocolProofChecks`.
The transitive axiom audit covered **1,109 package declarations**, allowing only `propext`,
`Classical.choice` and `Quot.sound`. All 29 owned modules, including the three package roots,
are reachable from the audit root. No proof source changed after this passing gate.

The passing command took **23.75 seconds** wall time, with **1,461,936 KiB** maximum resident
memory. Lake reported 2,789 jobs, including cached dependencies. This is one incremental gate
measurement, not a cold-build benchmark or a speedup claim. An earlier gate found a tactic
failure in the new adaptive-cost control; the correction reran only its dependency cone and
reused the already-passing core modules. Focused checks preceded the final gate.

The actual dependency worktrees were clean and matched the manifest exactly:

| Dependency | Revision |
| --- | --- |
| Lean | `v4.35.0` |
| VCVio | `96754a37e739270ac5bb8fe7deaeafef6964b688` |
| PolyFun | `a5edfe2dd24d9d76f9a13cc1f131b220617ad534` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

Local dependency caches were shared with the existing proof-foundation workspace. The package
manifest contains pinned git dependencies, not those local paths; no upstream source or pin
was changed. No new independent external review was available. The current central review and
its fixes are recorded in [REVIEW.md](REVIEW.md); the earlier independent review is historical.

## Current acceptance evidence

| Schema or boundary | Positive evidence | Refused mutation or diagnostic |
| --- | --- | --- |
| Promise soundness | `ClaimBoundaries.soundness_receipt`; both migrated complete clients | Negative and adaptive statements; promise gap explicitly separate |
| Honest completeness | `ClaimBoundaries.completeness_receipt`; both migrated complete clients | Perfect acceptance refused for the half-abort client |
| Fixed recovery | `ClaimBoundaries.recovery_receipt` | Wrong recovery with an existing valid witness |
| Fixed bounded extraction | `PropertyProfiles.extraction_receipt` | Wrong extractor, wrong public target, zero call budget, zero success above a useful threshold |
| Statistical simulation | `PropertyProfiles.statistical_receipt` | Witness-leaking real view |
| Selected-observer simulation | `PropertyProfiles.distinguishing_receipt` | The same leak observed by an admitted identity test |
| Resources | One-call and adaptive two-call bounds using upstream charge | Zero-call request refused; finite/infinite assessments separate |
| Complete observations | `ClaimBoundaries.observed_abort_preserved` | Abort mass cannot establish perfect completeness |
| Receipts | Direct wrapper and explicitly discharged premise | Impossible premise does not yield a closed false claim |
| Classification/admission | Custom meaning stays custom; witnessed population and useful error examples | Empty-admission theorem explicitly marked vacuous; unchecked diagnostics remain available |

The framework now has 21 core modules (1,855 lines) and five example/control modules
(1,353 lines), including comments. Some new modules split previously colocated definitions;
there is one current definition of each meaning. These inventory figures do not measure
production authoring cost or automatic proof construction.

Reproduce from this directory with `lake build`. Focused development can use, for example,
`lake build +ProtocolProofExamples.ClaimBoundaries`. Production builds, imported protocol
reports, alternative kernels, fresh dependency rebuilds and runtime benchmarks were not run.
The archive `framework-claims-2026-11-09` contains the exact source/config hashes and final log.

---

# Original checkpoint validation (`276b63146`)

Scope: the independent protocol-proof framework and complete model clients. No production zkc
source, compiler, runtime, imported protocol, or existing formal pipeline was rebuilt or claimed
verified by this unit.

## Reproduction

From `lean/framework`, run:

```sh
lake build
```

The default targets include the framework, all three example/control modules, and
`ProtocolProofChecks`, which audits every package-owned declaration, including private and
generated declarations. Dependency axioms are followed transitively. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. The ordinary build checks every proof with
the Lean kernel; the separate audit does not replace that check.

The package pins Lean 4.35.0 and the exact VCVio, PolyFun, Mathlib and inherited library versions
in its manifest. There are no path dependencies or imports from an existing zkc Lean package.
`autoImplicit = false` and `warningAsError = true` are enabled.

## Original performed checks

The complete incremental package build passed on 9 November 2026. It includes the changed
examples, both root closure theorems, operation-to-program adequacy, state representation,
hierarchical installation, all negative controls and the all-declaration audit.

The audit inspected **549 declarations**, with only the standard axioms above. The successful
gate took **18.81 seconds** wall time and reported **1,410,800 KiB** maximum resident memory
for the timed command. Dependencies and previously checked unchanged modules were cached.
This is an incremental gate measurement, not a cold build or an imported-protocol benchmark;
Lake's 2,766 job count includes cached dependencies. Two earlier audit-harness elaboration
mistakes (a counter type and quoted namespace syntax) were fixed before this passing gate.
They did not require changes to the proof statements.

The independent `gpt-6.1-sol` / `xhigh` integrated review accepted this bounded package with
no blocking mathematical, semantic or architectural finding. Its sole actionable finding was
a documentation-only countability correction, now applied in `INTERFACES.md`. See
[REVIEW.md](REVIEW.md). No Lean source changed after the reviewed, passing build; its results
were reused rather than repeated.

## Complete clients

| Client | Checked top-level claims | Structural evidence |
| --- | --- | --- |
| Adaptive finite checks | `adaptive_soundness`, `honest_completeness`, `false_acceptance_eq`, `nested_false_acceptance_eq` | arbitrary history-dependent strategies, arbitrary finite rounds, nested batches, common `iterate` rules and common evidence roots |
| Shared-state components | `shared_soundness`, `shared_completeness`, `matching_probability` | two primitive calls per installed component, adaptive caller, persistent state, a noninjective representation, common roots and upstream `freeHandler` |

For a false residual, the adaptive model's acceptance probability is exactly `(1/2)^n`; two
batches of three rounds give `(1/2)^6`. True residuals with the specified honest strategy accept
with probability one. Choosing the guess after revealing the challenge instead succeeds with
probability one and refutes the requested half bound.

The shared-state model retains a single fair private bit. Two identical guesses both succeed
with probability one half, not one quarter. The concrete and model services differ by an
unobserved audit counter, whose erasure satisfies every local joint-law equation. A different
counter is observable and cannot be reset. The honest revelation client accepts with probability
one. These are intentionally distinct complete model games, not production-protocol theorems.

## Refusal and non-vacuity controls

| Defect or boundary | Checked theorem |
| --- | --- |
| Always accepting a false statement with a zero requested error | `BoundaryControls.acceptingFalse_refused` |
| Always rejecting in a perfect-completeness request | `BoundaryControls.rejectingHonest_refused` |
| A fixed recovery function returns the wrong witness | `BoundaryControls.wrongRecovery_refused` |
| Replacing recovery changes the request rather than proving the old one | `BoundaryControls.differentRecovery_has_different_meaning` |
| A witness-dependent leaked view differs from the one fixed public simulator | `BoundaryControls.leakingView_refused` |
| Zero output mass masquerades as a complete probability experiment | `BoundaryControls.zero_law_not_normalized` |
| An empty initial relation hides uncovered actual initial states | `BoundaryControls.empty_initial_relation_refused` |
| Challenge chosen before the guess loses the prediction bound | `AdaptiveChecks.revealed_bound_refused` |
| Shared randomness incorrectly multiplied as independent checks | `SharedState.multiplying_check_probabilities_invalid` |
| Resetting retained observable state | `SharedState.resetting_counter_invalid` |

`controls_admit_environment` checks that the canonical negative controls admit concrete
environments. The adaptive examples include nonconstant strategies and explicit zero-round
behavior, while the shared-state bound has an admitted matching strategy achieving it.

## Generality and limits of this evidence

The common adequacy and installation theorems quantify over interfaces and clients; they do
not dispatch on the example names. The examples exercise structural axes, while the protocol
matrix in [DESIGN.md](DESIGN.md) checks the intended mathematical decomposition for Sumcheck,
FRI, GKR, Sigma conjunction, folding and stateful oracles. That matrix is analysis, not another
set of checked protocol proofs.

The core has 9 modules and 1,191 lines including comments; the three complete example/control
modules have 954 lines. These counts describe the package, not a measured reduction in zkc
protocol-authoring cost. The examples contain their model definitions, mathematical proofs,
explicit evidence assembly, and attacks/refusal theorems. There is no per-client `FreeM`
interpreter or structural induction, but theorem selection and invariant authoring remain
explicit Lean work. Production author cost and checking cost require the later adapter gate.

Full knowledge extraction and computational zero knowledge are not inferred from unary bounds.
`RecoveryRequest` and the then-named view request tested fixed semantic boundaries. The current
property interfaces and their additional evidence are recorded above.
The package provides statistical upper game transfer with explicit losses, not an unproved
computational reduction or Fiat–Shamir/Merkle realization theorem.

## Next review gate

Review this framework's interfaces before integrating existing code. The later adapter must
bind the fixed actual IR subject to this execution/observation meaning, retain all failure
outcomes and adversary access, and use one construction path for at least actual multi-round
Sumcheck and FRI. Its evidence must distinguish a mathematical representation law from
mechanical source traversal. Reusing this package alone does not establish that adapter.
