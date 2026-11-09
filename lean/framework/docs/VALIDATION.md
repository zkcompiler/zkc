# Standalone validation record

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

## Performed checks

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
`RecoveryRequest` and `ViewRequest` test fixed semantic boundaries, as explained in the design.
The package provides statistical upper game transfer with explicit losses, not an unproved
computational reduction or Fiat–Shamir/Merkle realization theorem.

## Next review gate

Review this framework's interfaces before integrating existing code. The later adapter must
bind the fixed actual IR subject to this execution/observation meaning, retain all failure
outcomes and adversary access, and use one construction path for at least actual multi-round
Sumcheck and FRI. Its evidence must distinguish a mathematical representation law from
mechanical source traversal. Reusing this package alone does not establish that adapter.
