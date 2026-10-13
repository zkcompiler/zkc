# Libraries

Libraries are ordinary `.zkc` modules built and tested with the compiler. Their
public functions, records and child protocols are composed using the existing
language. Applications select concrete statements, inputs and Entries. A library
may capture its own mathematical assets through its manifest.

## Layers

| Layer | Responsibility | Examples |
|---|---|---|
| [Common operations](zkc/README.md) | Collections, algebra, polynomial representations, encoding and local commitment operations | `zkc::vector`, `zkc::multilinear`, `zkc::coset`, `zkc::oracle` |
| Protocol families | Reusable equations, interaction and returned obligations | [Sumcheck](sumcheck/README.md), [FRI](fri/lib.zkc), [AIR](air/README.md), [STARK](stark/README.md), [Bulletproofs+](bulletproofs/README.md) |
| Concrete constructions | Selected transcript transitions and wire encodings | [Spongefish](spongefish/README.md), Monero Bulletproofs+ |
| [Projects](../examples/projects/README.md) | Domains, captured relations, complete compositions and Entries | Schnorr, composed Sumcheck, AIR and machine clients |

A reduction can return a point and claimed value for its parent to check.
A complete protocol combines all its required checks into an acceptance result.
Neither an ordinary record nor a successful row authentication is a security
certificate. Keep the actual participant's received values and explicit random
services when composing protocols.

The [Schnorr module](schnorr/lib.zkc) provides the discrete-log relation and
three-message protocol. It is generic over the group; the client chooses the
field/group implementation and construction. The library implementations and
small example parameters provide execution evidence, not general security proofs.

## Select a family

```toml
format = "zkc.project/0"

[modules]
example = "main.zkc"

[dependencies]
sumcheck = "../../../libraries/sumcheck"
```

Then use its public declarations:

```text
use sumcheck::{Reduce, check};
```

Each family owns a `zkc.toml` with its sources and local dependencies. The loader
captures all listed sources, including private implementation modules. Dependency
labels do not rename source modules. Shared dependencies load once; conflicting
providers and cycles refuse. Paths are relative to the declaring manifest.
All captured modules share one namespace, including transitive dependencies.
Declare a directly used family explicitly so its availability does not depend
on another family's implementation dependencies.
There is no registry, download or global implicit import. Explicit compiler
module maps and SDK byte captures remain available.

Run `zkc check --project=libraries/zkc/zkc.toml` to check the common family.
See the [walkthrough](../docs/getting-started.md) for compiling and executing a
project, and [input files](../docs/language/README.md#project-inputs) for Entry inputs.

## Design and maintenance

- Put shared local mathematical operations under `zkc`; keep relation
  interpretation, round algorithms and acceptance conditions in their families.
- Expose the smallest useful composition boundary. Return the prover residual
  when a parent needs it; preserve the verifier's own point and statement.
- Select concrete carriers, commitments and transcript constructions explicitly.
  A generic signature promises only the installed capabilities it requires.
- Use an interface when implementations actually vary, such as AIR interaction
  reductions. Do not duplicate native domain contracts in a wrapper interface.
- Keep demos in projects. A library has no application Entry or bundled witness.
- Validate new APIs with independent clients and negative controls, including
  shape, degree, authority, message order and exact external bytes where promised.

With built tools, select the affected checks from the
[test guide](../common/tests/README.md#selecting-checks). Library changes update
clients and manifests together; they add no compatibility module or version bump.
