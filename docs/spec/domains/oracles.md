# Authenticated finite tables

A vector commitment authenticates coordinates of an ordered finite table. It
does not assert polynomial degree, relation satisfaction, an extraction theorem
or hiding. A protocol can use this domain without using AIR, FRI or polynomials.

## Contract

`VectorCommitment(C)` associates a nominal scheme `C` with `C.ValueField`.
The table is a flat, row-major field vector with positive width and height.
This capability is separate from `MultilinearOpening`.

| Operation | Meaning |
|---|---|
| `oracle.commit<C>(values,width)` | Commit one rectangular table; return public root and private immutable opening state |
| `oracle.open<C>(state,index)` | Return the complete selected row and ordered authentication path |
| `oracle.check<C>(root,width,height,index,row,path)` | Check exactly the caller's expected shape and coordinate; return Boolean |
| `commitments.empty/append/at/length<C>` | Persistent public root sequence, with checked lookup |
| `opening_states.empty/append/at/length<C>` | Persistent private state sequence, with checked lookup |

Indices are checked unsigned naturals, not field elements. The verifier supplies
the expected shape; a received path cannot choose it. The Boolean is not an
implicit acceptance: the authored verifier must consume it in a guard or expose
it through an explicitly selected caller acceptance result. A public
root cannot manufacture private opening state. Opening states and their
collections have no public wire decoder or transcript codec.

Publication occurrence and interaction order belong to source execution. A
received root or row is a distinct adversarial value, even when source analysis
identifies its authored sender. Repeated coordinates remain repeated logical
queries; an encoding optimization must preserve rejection of inconsistent
responses before it can share authentication work.

## Installed binary Merkle schemes

The installed schemes are `rows.merkle-keccak256.koala-bear/1` and
`rows.merkle-keccak256.koala-bear.ext8-binomial3/1`. Both use Plonky3 0.5.1's
binary single-root tree with Keccak-256, one rectangular matrix and cap height
zero. Leaf hashing binds a fixed leaf tag, field/basis codec, width, height
and canonical coordinates. Node hashing uses a distinct tag and two 32-byte
digests. Missing bottom-layer leaves use upstream zero-digest padding.

Non-power-of-two heights are allowed. Checking requires exact row width,
`index < height` and path length `ceil(log2(height))` before upstream hashing.
Shape, byte and element limits apply before allocation. Authentication failure
returns false; malformed shapes and resource exhaustion refuse execution.
These schemes are nonhiding and do not require an external setup key. Setup
policy is selected by nominal scheme, never by the words `commitment` or `proof`
alone. The [structured proof contract](../profiles/compiler/structured-proof-messages.md)
fixes public codec admission.

## Publication, queries and acceptance

A protocol that claims authenticated sampling must bind the actual received root,
expected shape, coordinate and response to its verifier's check. Publication
order, query order and exact sampling are different conditions: a coordinate can
depend on a random draw without being that draw or having its distribution.
A sampled bound must have the intended relationship to the table height.

A transcript construction must observe the required public context before its
derived query. Observing a statistic, a different received copy or another
provider's history is not automatically observation of the checked root. Neither
source ordering nor a matching dependency label proves an injective encoding or
sampling law. Repeated coordinates remain repeated logical occurrences.

The verifier's selected acceptance result must entail the required authentication
checks. An unused Boolean result does not do so. Component ordering and global
ordering have different scopes; sequentially composing two query protocols does
not justify treating them as one simultaneous query experiment.

These are semantic obligations for the authored protocol and its selected
experiment. The native implementation provides general oracle kernels and
[composed mathematical clients](../../compiler/mathematical-composition.md).
It does not provide a complete FRI application or a BCS/Fiat–Shamir security
theorem. Automatic lowering of an
arbitrary ideal-oracle IOP remains separate work.
