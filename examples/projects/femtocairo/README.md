# Clean FemtoCairo

This example proves a seven-step execution of Clean's FemtoCairo over KoalaBear.
The transition constraints and witness generator come from the pinned Clean package.
The initial `(pc,ap,fp)` is `(0,0,0)` and the final state is `(28,0,0)`.
The selected program exercises arithmetic, state operations and repeated reads
of immutable memory.
The client instantiates the pinned sample program in KoalaBear and explicitly
binds the initial and final states, mirroring Clean's inductive-table boundaries.
Its memory input lists values; the adapter assigns and constrains their addresses
to the row indices.

The [adapter](../../../compiler/adapters/clean/README.md) creates three tables:

| Table | Height | Meaning |
|---|---:|---|
| CPU | 8 | Initial state and seven transitions, with Clean's auxiliary witnesses |
| Program | 32 | Fixed indexed program data and lookup multiplicities |
| Memory | 8 | Indexed immutable values and lookup multiplicities |

The `.zkc` client calls the general
[`ThreeTableArgument`](../../../libraries/arguments/stark/README.md#whole-bundle-argument)
with LogUp. The compiler and runtime contain no FemtoCairo execution path.
Program values and initial/final states are public. Memory values and CPU
auxiliaries are witness inputs; the proof is **nonhiding**, so this is an
execution-proof example, not a zero-knowledge implementation.

With built tools on `PATH`, run here:

```sh
zkc check
zkc prove
zkc verify
```

`prepare.py` regenerates the committed input maps from the native relation
carriers; `prepare.py --check` checks their agreement. To change the program or
execution, change the Clean client and regenerate the relation and witnesses
using the adapter's documented commands. This profile has fixed table heights;
it neither adds HALT padding nor extends memory implicitly.
Program-value pins target small fixed programs; their cost is described at the
adapter boundary.

The tests compare Clean's separate bounded-execution reference with the final
state, check the native Bundle in both implementations, produce and verify a
proof, and reject modified transition, program, address, selector, multiplicity
and public-boundary data. They do not establish a general translation theorem
or security of the full STARK composition. Parameters are deliberately small
for tests; the proof encoding is zkc's own.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc prove Proof
zkc verify Proof
```

Inputs: inputs/example.Proof/{public,witness}.json; prepare.py regenerates the maps in a checkout.

Profile: The octic whole-bundle profile has exactly three tables: CPU, program and immutable memory.

Expected negative control: Changed transition, lookup multiplicity, memory address or final state refuses acceptance.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
