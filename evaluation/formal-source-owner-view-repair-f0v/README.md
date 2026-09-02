# F0-V1 owner-view publication-topology feasibility

This package tests one proposed repair for the PIR owner-view source gap found
by F1-R1C0. Its aggregate result is
`Affirmative/F0V1-A-PUBLICATION-TOPOLOGY`: the existing semantic-profile
publication mechanism can express the selected ownership, declaration,
dependency, source-routing, and identity-rotation topology.

The package changes no target source or manifest. It constructs exact
in-memory overrides, compiles them, and then discards them.

Run the gate from the repository root:

```sh
python3 -B evaluation/formal-source-owner-view-repair-f0v/run.py --check
```

Use `--json` for profile identities, declaration inventories, source routes,
and mutation diagnostics.

## Candidate tested

The synthetic candidate makes six coordinated profile-local changes:

1. Interaction publishes `pir.static-view-schema` entries for the five Core
   views and Protocol `ExecutionView`, in one fixed order.
2. Static-view issuance reaches all six declarations; every entry names an
   exact owner, topology-only body compiler, derivation-law dependencies,
   schema-resolution law, and four local authority-envelope compilers.
3. Interaction publishes separate common compilers for the consumer and
   purpose role bodies already present in its authenticated source.
4. Interaction and the five profiles that used its catch-all compiler each
   publish local compilers for binding payload, capability requirement,
   no-policy, and policy closure.
5. The six locally changed synthetic profiles advance to revision 1.
6. Both publication compilers reconstruct all eighteen profiles and derive
   the same sixteen-profile rotation cone; `analysis-kernel` and
   `oir-endpoint-graph` remain exactly stable.

The five directly repaired dependents are canonical-framed Fiat--Shamir,
duplex-sponge Fiat--Shamir, public setup, Interface/Plan, and endpoint source
view. Canonical-framed and duplex view-schema catalogs are still future
profile-local work; F0-V1 repairs only their authority-envelope routing.

## Independent evidence and mutations

[`model.py`](model.py) forms the candidate and compiles it with the
Foundation-backed publication implementation. [`independent.py`](independent.py)
repeats the expected inventory without importing that model and compiles the
same bytes with the cold publication implementation. The two paths agree on
every profile body digest, profile reference, direct import, declaration
ordinal, route, revision, and rotation result.

The 18 frozen findings include six affirmative topology observations, two
intentional `CannotAnswer` boundaries, and ten dual-path refusals:

- missing or extra owner schemas;
- Core/Protocol owner substitution;
- derivation-law substitution;
- common role compiler used for a family payload;
- unreachable schema declaration;
- absent authenticated selector;
- retained revision after local source change;
- imported compiler used for a dependent family payload; and
- consumer/purpose role swap.

## Exact limit

The synthetic `static-view-body-v0` and schema selectors describe publication
topology only. They are deliberately not the canonical grammar for the six
views, coordinates, paths, boundaries, manifests, or authority values. The
gate also does not define the constructor-specific dependency graph required
for proper-subset projections.

Accordingly, F0-V1 does not repair the target, publish new identities, admit a
Core, derive a view, establish Q1 correspondence, validate a provider, prove a
theorem, or verify implementation code. F0-V2 must author and review the exact
grammar and perform the real profile migration. F1-R1C1 may then test complete
owner views; F1-R1C2 remains the separate proper-subset closure gate.
