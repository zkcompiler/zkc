# Optional ArkLib adapters

The `zkc_arklib` Lake package owns the adapter library and its tests. It depends
on Protocol and pinned upstream mathematics. The previous source-specific
Applications registry and generated IR clients are retired.
[Shared pins](../../docs/dependencies.md) are unchanged. Import module paths
and declaration namespaces are distinct; existing theorem names are preserved.

`ZkcArkLib.Sumcheck` connects the deterministic zkc verifier to ArkLib and
preserves arbitrary causal strategies and complete executions.
`Sumcheck.Multilinear.Causal` owns stop-aware joint phases and their bounds,
independently of authored source syntax. Their previous generated actual-source
connections are retired; new installations must supply that association.

`ZkcArkLib.Fri` and `ZkcArkLib.Gkr` adapt the upstream family theorems.
`ZkcArkLib.Stark` adapts the proved STIR list-collision and quotienting results,
with exact polynomial equalities, a two-word affine-line proximity theorem, and
a many-word power-batch distance bound for a common target code. The latter uses
the proved capacity bound below its generalized Johnson radius and includes
typed common-degree quotient words and an explicit ENNReal error.
The [STARK component contracts](../../docs/spec/stark-components.md) identify the
admitted dependency of general upstream combination, which these adapters avoid.
`ZkcArkLib.FiatShamir.Upstream` imports ArkLib's round-by-round security;
the concrete verifier installations and Applications registry from the previous
route are retired. This adapter retains independent mathematics and downstream
consumer checks. Protocol and Verification do not depend on ArkLib. The
Verification-owned registry contains only maintained generic schemas; optional
adapter results do not imply a compiled endpoint.

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
include `Zkc.Adapters.ArkLib.Kzg.EvaluationBinding` and its concrete group/field
`OpeningClient`, plus `ZkcArkLib.Knowledge.FiniteRecovery`. KZG bounds use the
pinned intermediate reduction results with explicit admissibility closure;
they do not invoke the upstream all-functions hardness assumption. Finite
straight-line recovery has its own request and exact two-cell access. Neither
adapter supplies native bytes or a compiled KZG knowledge receipt.
