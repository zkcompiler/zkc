# Framework-first package plan

The accepted architecture separates the shared program foundation, proof core, reusable
mathematics and concrete IR integration. Complete the framework before attaching imported
Sumcheck, FRI or another production protocol.

## Packages 1 and 2: current unit

1. Extract the existing generic Region/Process substrate once into `zkc_program`, with
   Std-only dependencies. Move the proof package to `lean/proof`; preserve exact shared
   declarations without forwarding aliases. Integrate import/ownership/audit tooling.
2. Make all public execution, contract, access and property profiles Process-facing.
   Interpret full outcome/state/log records through one upstream probability backend.
   Prove normalization, full monadic correspondence and deterministic Dirac agreement.
3. Supply exact same-interface installation, differing-interface representation and
   substitution, contextual composition and property-specific security transfer.
4. Validate complete adaptive/nested, shared-state, oracle/proximity and decoder clients,
   including refused malformed inputs, stopped mass, wrong observations and false
   independence assumptions. Audit all owned declarations and review the frozen unit.

These are proof and program foundation packages. They do not connect actual protocol
artifacts or implement the proof search/construction engine.

## Package 3: common construction and companion path

Build a typed derivation with a soundness theorem against the shared Region meaning,
then one proposer/constructor over that interface. Companion inputs are mathematical
component laws, representation relations, invariants and explicit premises. Instantiation
is keyed by canonical identity; it is never proof by name matching. Missing inputs remain
typed obligations. Reuse checked template declarations instead of duplicating their proof
at every call. Measure author input and Lean checking cost on complete model clients.

This package requires a separate implementation decision after reviewing Packages 1–2.

## Package 4: mathematical library and concrete integration ownership

Consolidate reusable mathematics and provider adapters against these interfaces. Concrete
readers, artifact/stage correspondence and actual subject bindings remain integration-owned.
Retire replaced routes as their full statements migrate; do not preserve a permanent legacy
fallback. Only afterwards plan real imported protocol adoption with fixed target claims,
stages, assumptions and measured author cost.

## Validation discipline

Use changed-module checks during development and the affected package/audit gate at a
stable boundary. Reuse valid evidence. Expensive existing security/native/reproduction
runs are not substitutes for the bounded framework gates and are not repeated for these
independent model changes. Report exact checked scope and outstanding later packages.
