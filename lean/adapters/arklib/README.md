# Optional ArkLib adapters

The `zkc_arklib` Lake package owns `Zkc.Adapters.ArkLib`,
`Zkc.Tools.ArkLib` and `Zkc.Tests.ArkLib`. It depends on Protocol and pinned
upstream mathematics. Actual IR clients and the report registry are owned by
`Zkc.Applications.ArkLib` in the downstream Applications package.
[Shared pins](../../docs/dependencies.md) are unchanged. Import module paths
and declaration namespaces are distinct; existing theorem names are preserved.

`ZkcArkLib.Sumcheck` connects the deterministic zkc verifier to ArkLib and
preserves arbitrary causal strategies and complete executions.
`Sumcheck.Multilinear.Causal` owns stop-aware joint phases and their bounds,
independently of authored source syntax. `ZkcArkLibExamples.CausalSumcheck`
connects these laws to the maintained admitted programs, including the exact
round-count refusal behavior and residual observations.

`ZkcArkLib.Fri` and `ZkcArkLib.Gkr` adapt the upstream family theorems.
`ZkcArkLib.Stark` adapts the proved STIR list-collision and quotienting results,
with exact polynomial equalities, a two-word affine-line proximity theorem, and
a many-word power-batch distance bound for a common target code. The latter uses
the proved capacity bound below its generalized Johnson radius and includes
typed common-degree quotient words and an explicit ENNReal error.
The [STARK component contracts](../../docs/spec/stark-components.md) identify the
admitted dependency of general upstream combination, which these adapters avoid.
`ZkcArkLib.FiatShamir.Upstream` imports ArkLib's round-by-round security;
actual-verifier realization and its dependent clients live in Applications.
The Applications `Subjects.Guess` and `Subjects.Sumcheck` modules keep their artifact,
contract, evidence and claim files together. `Zkc.Applications.ArkLib.Registry` owns the `ZkcArkLib.Registry` declarations and registers
optional schemas; record readers combine it with `ZkcSecurity.Claims.Registry` and
reject collisions. Protocol and Verification do not depend on this adapter.

From the repository root:

```sh
python3 scripts/develop.py fetch-lean --package arklib
python3 scripts/develop.py lean --package arklib
python3 common/tests/run.py lean-integration
nix build .#arklib
```

All maintained modules, examples, compatibility clients and audits are default
targets. `checks/check_library.py --package arklib` selects Program and Protocol
before this package and checks actual package providers, pin consistency and
imports. Declaration audits inspect stored types, bodies and transitive axiom
closures. These are model-specific results; [formal support](../../docs/support.md)
states their premises and open implementation links.

The [selected property adapters](../../docs/spec/selected-property-adapters.md)
include `ZkcArkLib.Kzg.EvaluationBinding` and its concrete group/field
`OpeningClient`, plus `ZkcArkLib.Knowledge.FiniteRecovery`. KZG bounds use the
pinned intermediate reduction results with explicit admissibility closure;
they do not invoke the upstream all-functions hardness assumption. Finite
straight-line recovery has its own request and exact two-cell access. Neither
adapter supplies native bytes or a compiled KZG knowledge receipt.
