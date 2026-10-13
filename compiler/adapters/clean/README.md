# Clean to native relations

This optional adapter turns extracted [Clean](https://github.com/Verified-zkEVM/clean)
constraints into the ordinary [relation Bundle](../../../docs/spec/domains/relation-bundles.md)
used by `.zkc` libraries. Clean is pinned in the
[Lake package](../../../lean/integrations/clean/lakefile.toml). Running the checked-in
examples requires the native tools; Lean is needed only to regenerate their sources.

## Boundary

[NativeExport.lean](../../../lean/integrations/clean/ZkcClean/NativeExport.lean)
extracts expressions, cell assignments, operation scopes and interaction metadata
from actual Clean definitions. Typed helpers derive lookup/channel names and
arities from those definitions. `inductiveTable` couples an inductive transition
with public state boundaries whose width comes from `ProvableType`. Clients
choose lookup interpretations and any other public bindings explicitly.
[adapter.py](adapter.py) compiles this static plan to a Bundle and configuration;
instance encoding and witness preparation use the resulting immutable layout.
The compiler and runtime consume these normal carriers. No VM operation or
protocol implementation is installed by the adapter.

| Source | Native representation |
|---|---|
| `TableOperation`: boundary, every row, every row except last | Scoped assertions with finite active windows; the Lean producer allocates disjoint auxiliary columns per operation |
| One `Air.Flat.Component` | Row assertions and signed field-balance channels with declared arity |
| Explicit public bindings | Initial/final cells equated to ordered public scalars |
| Fixed indexed lookup | Configured `(address,value)` rows pinned to the selected data, with witness multiplicities |
| Witness indexed lookup | Witness `(address,value,multiplicity)` rows; addresses constrained to row indices |

The static `source.json` plan uses `zkc.clean-export/0`. It declares the field,
table and its origin, public size and cell bindings, lookup interpretations, and
channels. Each lookup/channel registration records `{definition, name, arity}`
and its native interpretation. The separate `inputs.json` uses
`zkc.clean-inputs/0` for public values, trace and witness tables. Optional
`reference.json` is test evidence, not a compilation input. [schema.py](schema.py)
validates JSON and cross-references once at each boundary and produces immutable
typed expressions and operations. Unknown fields and unsupported operations refuse
with an error code and source/input location. The Lean source constructor requires a `PrimePresentation` and derives the
modulus from it; field constants use canonical naturals. The native admitted
field is KoalaBear. Heights are fixed and
nonzero; the adapter never pads programs, memory or executions implicitly.
The STARK library separately admits its power-of-two heights and degree bounds.
Extracted field values are JSON integers in `[0, p)`; native carriers use scalar
strings. Expression trees have at most 256 nested arithmetic operations per path;
deeper expressions refuse before recursive compilation or evaluation.

Lookup interpretations and channel registration are **trusted author declarations**. A Clean table name
does not identify its arbitrary Lean `Contains` predicate. These clients register
the pinned indexed program and immutable-memory definitions explicitly; this is
not a generic importer for every `Table` with the same name. Adding a new lookup
requires reviewing its predicate and choosing or implementing its native meaning.
Likewise, a channel name and arity do not identify its Lean requirement and
guarantee predicates. `assumeGuarantees` is retained in the source plan but
does not enter Bundle balance. Source plan metadata is not a proof certificate
and is not covered by the native Bundle identity. Sources with the same native
algebra can share a Bundle even if their origins or guarantee modes differ.

A component is treated as a closed, one-component ensemble without a verifier
row: its declared channels must balance within that table. Lookup tables are
added separately for explicitly registered indexed lookups.

Lookup requests have weight minus one on active rows. Partially active operations
use a witness selector constrained to their scope; all-row requests need no
selector. Cyclic evaluation leaves inactive tuples defined without adding a lookup.
Table multiplicities are field
values. Address constraints prevent substituting another row's value or using
duplicate addresses. The total number of emitted records per channel, including
zero weights, must be below the characteristic. For flat channels this retains
Clean's balance premise; for lookups it is the native membership encoding's
non-cancellation requirement. No range proof for these field weights is implied.

Fixed program values are pinned by interval assertions, one per equal run.
This keeps the selected program part of the Bundle's meaning. Prover work for
these pins grows with the run count times the evaluation-domain size, so this
profile targets small fixed programs. A scalable parameterized or committed
program needs a separate source contract.

## Compile and prepare data

With `compiler/adapters` on `PYTHONPATH`, the Python API separates three stages:

```python
from clean.adapter import compile_relation

compiled = compile_relation(source)
bundle = compiled.bundle
configuration = compiled.configuration
instance = compiled.encode_instance(public_values)
witness = compiled.prepare_witness(trace, witness_tables)
```

Compilation needs no execution inputs. Public size comes from the declaration;
lookup heights and fixed program values are static. The same compiled layout can
prepare multiple executions without accumulating lookup counts. Returned carriers
are independent JSON values, so modifying one cannot change the compiled identity.
`export(source, inputs)` composes these stages for small clients and regeneration.

The trace has exactly the declared height and width. State/input columns come
first, followed by a separate auxiliary block for each operation in declaration
order. Within a window, auxiliaries occupy its last row (`window - 1`); other
cells retain their extracted row offsets. Clean's `witnessesWithData` supplies
this layout for a single transition constraint. Clients combining operations
must arrange these blocks themselves; the adapter does not schedule witnesses.
Boundary rows use nonnegative indices from the start and `-i-1` for row `i`
from the end. Only the producer's flattened operations are admitted.

Witness preparation checks shape, canonical field values and indexed lookup
membership, then computes selectors and multiplicities. It does not generate a
Clean trace or check every relation assertion. Clean's witness generator (or
another producer) supplies the trace; native relation evaluation checks the
resulting constraints. Algebraic balance alone does not establish a channel's
Lean requirements/guarantees, including a premise marked by
`assume_guarantees = true`. Similarly, inductive compilation does not prove a
Clean specification's initial-state premise. Declaration names document the trusted choice of
interpretation; they are not authenticated definition identities.

## Reproduce

After `just fetch-lean clean`, run from the repository root:

```sh
just test-lean-clean
```

That check builds the optional package, extracts the clients and compares every
committed native fixture with fresh output. To inspect a fresh export directly:

```sh
cd lean/integrations/clean
lake env lean --run CleanExamples.lean /tmp/clean-sources
cd ../../..
python3 compiler/adapters/clean/regenerate.py check /tmp/clean-sources compiler/adapters/clean/fixtures
```

Use `write` with a new destination to inspect proposed fixture changes.
[Fibonacci](../../../examples/projects/fibonacci/README.md) compares locally authored
Clean and Plonky3 constraints. [FemtoCairo](../../../examples/projects/femtocairo/README.md) uses Clean's
VM constraints, witness generator and separate bounded-execution reference.
The flat-channel control exports upstream `pushBytes` with signed weights.

## Evidence and next extensions

[Native tests](../../../common/tests/protocol/test_clean_adapter.py) compare C++
and Rust relation evaluation, independent recurrence/reference execution,
mutated memory/program/boundary data, reusable compilation, malformed inputs,
and end-to-end STARK prove/verify of the example projects. The wider
[STARK controls](../../../libraries/stark/README.md#evidence-and-limits) exercise
malicious prover paths. These are bounded checks, not a proved translation or
a cryptographic security theorem. The existing
[Lean correspondence](../../../lean/integrations/clean/README.md) covers a smaller,
channel-free flat fragment and does not cover this native adapter.

Full flat ensembles need shared channel registration and the verifier's single
public row, including its constraints, interactions and contribution to the
cardinality bound. This adapter currently accepts one component and refuses
ensemble input. Arbitrary lookup predicates, general witness scheduling, other
fields and a proof of native translation are further extensions. Such a proof
must connect low-level constraints through Clean's assumptions to its
specification; inductive-table adequacy is an implication, not a general
if-and-only-if statement.
