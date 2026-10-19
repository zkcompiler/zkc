# Source libraries

Libraries own reusable operations and protocols. [Example projects](../examples/projects/README.md)
select concrete domains, relation assets, constructions, Entries and inputs.

```text
libraries/
  core/
    primitives/{collections,algebra,polynomial,cryptography}/
    traversal/
    {collections,algebra,polynomial,encoding,services}/
  protocols/
    sigma/{schnorr,compositions}/
    polynomial/{sumcheck,gkr,fri}/
  relations/air/
  commitments/kzg/
  arguments/
    stark/{configurations,sampling,single_table,whole_bundle}/
    bulletproofs/weighted_inner_product/
  constructions/
    spongefish/
    monero/bulletproofs_plus/
    ethereum/eip4844/
```

The hierarchy describes responsibility and dependency direction. Each leaf
`zkc.toml` owns its sources exactly once and can be checked independently.
Directory indexes do not introduce source modules or capture optional children.
Public source names, physical folders, capture packages and native capabilities
are separate choices. For example, `zkc::vector` is the convenient facade, while
`zkc::primitives::vector` owns its native representation and direct operations.

| Layer | Responsibility and guide |
|---|---|
| [Core](core/README.md) | Native ports, traversal, checked mathematical views and local convenience operations |
| Protocols | [Schnorr](protocols/sigma/schnorr/README.md), [Sigma compositions](protocols/sigma/compositions/README.md), [Sumcheck](protocols/polynomial/sumcheck/README.md), [GKR](protocols/polynomial/gkr/README.md), [FRI](protocols/polynomial/fri/README.md) |
| Relations and commitments | [AIR interpretation](relations/air/README.md), [generic KZG algebra](commitments/kzg/README.md) |
| Arguments | [STARK profiles](arguments/stark/README.md), [weighted inner products](arguments/bulletproofs/README.md) |
| Concrete constructions | [Spongefish](constructions/spongefish/README.md), [Monero Bulletproofs+](constructions/monero/bulletproofs_plus/README.md), [Ethereum EIP-4844](constructions/ethereum/eip4844/README.md) |

## Consume a package

For a project at `examples/projects/my-project`:

```toml
format = "zkc.project/0"
[modules]
example = "main.zkc"
[workspace]
path = "../../../zkc.workspace.toml"
[dependencies]
sumcheck = { workspace = "protocols.polynomial.sumcheck" }
```

```text
use sumcheck::{Reduce, check};
```

The [local catalog](../zkc.workspace.toml) selects individual leaf packages.
Catalog locations use the catalog's visible parent; the workspace path uses
the declaring manifest's visible parent. A path dependency such as
`sumcheck = "../../../libraries/protocols/polynomial/sumcheck"` works independently
of a catalog. Installed sources retain this layout under `share/zkc`.
Labels and catalog keys do not rename source
modules. Dependencies load once; conflicting providers and cycles refuse.
The loader captures the selected closure, including private modules. It adds
no registry, download or implicit global import.

Declare every directly used package, including a facade. A facade can expose a
lower declaration without requiring its consumer to declare the implementation
package. Importing that lower module directly requires its owner explicitly.
Primitives never depend on traversal or facades; traversal depends on primitives;
higher layers may depend on the same or lower layers. Concrete constructions
select transcript transitions and wire encodings explicitly.
Every package under `libraries/` must belong to a classified layer; an unknown
location refuses rather than inheriting the application policy.

`zkc check --api --project=...` reports the compact public export graph, completed
contracts and checked provider references, alongside manifest ownership. These
are diagnostic views; they do not alter capture or artifact identities. Public
authored functions freeze requirements with `where` and local effects with
`effects`. Native bindings retain their installed catalog contracts. The
[package checks](../common/tests/protocol/test_library_packages.py) enforce
ownership, direct dependencies, layers and authored boundaries from those views.

## Extend a family

Place code at the lowest layer that owns its policy. Keep native bindings under
primitives, shared traversal separate, relation interpretation under relations,
round schedules under protocols or arguments, and selected encodings under
constructions. A new preset owns its required aliases and capabilities without
capturing unrelated presets. Use interfaces where implementations actually vary.
A convenience facade reexports deliberate declarations and notation; it does
not create another implementation or a compatibility namespace.

Preserve role ownership, received values, explicit randomness, message order,
callback effects and residual obligations. A reduction is not acceptance, and a
checked view or successful row authentication is not a security certificate.
Validate reusable APIs with independent arithmetic, malformed inputs, constructor
authority controls and external byte vectors where promised. Update consuming
manifests, examples and docs in the same change. See the
[test guide](../common/tests/README.md#selecting-checks) for affected checks and
the compact family smoke lane.
