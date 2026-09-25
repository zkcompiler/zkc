# Finite local control in the portable tools

The portable ordinary and generic source adapters admit isolated local `if` and
half-open unit-step `for` regions, ending in `yield`. Both branches and every loop
body are formed before execution, including dormant branches and zero-trip loops.
Helper specialization and expansion preserve those regions. The checker admits
and compares the actual candidate's complete local body at logical and physical
stages; representation conversions and admitted storage releases remain explicit.

[`FiniteControl`](../Zkc/Source/FiniteControl.lean) supplies a family of existing
typed `Region.branch` and `Region.iterate` computations. Each runtime bound is a
natural decoded from a valid index; `Bounds.admit` checks **both magnitudes**
against 1,048,576. Its count is `upper - lower`, with natural subtraction, so
inverted and equal bounds produce zero trips. The adapters construct the admitted
`Bounds` before passing its count to the finite typed iteration combinator. The
accumulator contains the current induction index and ordered carried values.
Neither branch selection nor iteration eagerly executes an unselected body.

Theorems give count admission, zero trips, reconstruction of the upper bound,
induction-index containment, exact selected iteration denotation, and a uniform
semantic call bound from the existing `Region.denote_within` theorem. The latter
assumes a bound on each interpreted primitive and counts semantic interface
calls. It is not a bound on native time, allocated bytes, or backend work.

The raw structured tree is independently checked, but is not a new intrinsic
`Program` constructor. Straight-line locals retain their existing stored typed
region. Controlled locals use the finite typed combinators during execution.
There is no theorem of raw decoder/elaborator adequacy, native refinement,
allocator correctness, group primitive correctness, or protocol security here.
Existing phase, renaming and transformation theorems apply to their typed terms
under their stated premises; successful portable admission does not discharge a
missing raw-to-typed correspondence premise.

The logical interactive and artifact references independently evaluate arithmetic,
control, reached guards and resources, using existing trusted group/cryptographic
primitive boundaries. They retain their separate logical work-admission policy.
Common protocol loops and local loops share a cumulative 100,000-iteration
counter. Branch and loop origins append `if/site/then-or-else` and
`for/site/actual-index`, respectively. Artifact construction refuses controlled
local bodies with affine boundary or nested primitive ports, and selected draws
inside controlled functions. These construction limits do not restrict ordinary
interactive local execution.

`--physical-local-reference` supports a single root participant with one local
call followed by return. That local body can contain nested branches and loops.
Each entered region has a child frame, retains its explicit inputs, releases all
its live and ghost charges on return or failure, and transfers yielded values to
the enclosing region. Loop carries pass directly to the next iteration; zero-trip
outputs are retained once in the parent. Instructions, retained values/bytes,
cumulative bytes and active frame counts follow the scoped native accounting
profile. Scalar indices retain the existing conservative **512-byte** backend
charge. Supported vector and group-sequence charges use exact-length backing;
tables use supplied input capacity and exact-capacity successful fresh allocation.
The physical command does not cover arbitrary participant graphs, external
primitive caches, diagonal-view execution or allocation failure refinement.

Reproduce from `formal/`:

```sh
lake build Zkc ZkcTests interactive-protocol artifact-reference
python3 checks/local_control_cli.py
```

[`Tests.LocalControl`](../Tests/LocalControl.lean) covers selected finite execution,
zero/inverted bounds, reached failure paths, affine reuse and capture refusal,
malformed dormant branches, candidate mutations and artifact reference arithmetic.
The executable Python controls add generic specialization, nested helpers, both
candidate stages, physical lifetimes/accounting and recursive artifact identity.
Main and Rust own the joined native differential fixtures outside `formal/`.

## Finite local variants

The [local-variant profile](../../docs/spec/profiles/compiler/local-variants.md)
adds nominal tagged values and exhaustive isolated `match` regions to the same
portable adapter. `Tools.Interactive.VariantDescriptor` owns independent canonical
descriptor parsing; `Bindings` checks every logical payload and conservative
copy/drop permission. `TypedLocal` retains the checked match, and the logical and
physical interpreters enter only the selected arm with its payload and captures.
Nested resources keep their issuance, generation and authorized view. No variant
wire codec or protocol-level scheduling branch is introduced.

All branches, including inactive alternatives, participate in candidate checking.
A stopped arm yields nothing; `ExceptT` over the existing state monad retains the
reached state while bypassing its continuation. The small
`Tests.Variant.stop_bypasses_continuation` theorem states that monadic law. It is
not a compiler refinement or security theorem. The physical interpreter uses the
variant storage charge defined by the profile, including the retained descriptor
and only the active payload.

`Tests.Variant` exercises formation, active payloads, ownership, stopped execution
and logical/physical correspondence. `checks/variant_cli.py` exercises the actual
executable independently. The joined native tests in
[`local_variants.rs`](../../crates/zkc-tools/tests/local_variants.rs) compare actual
source compilation, complete Rust/Lean outcomes, resource state, ordered requests,
allocation steps and frame cleanup. Host Groth16/PCS ingress validation remains a
native adapter boundary; these tests do not prove its codecs or cryptographic
assumptions.
