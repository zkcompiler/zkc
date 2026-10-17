# Authenticated finite tables

Native oracle operations use these commitment, query and opening obligations.
This chapter states shared laws; a native implementation claim needs its
actual instance and evidence. Independent formal examples retain their own
[model scope](../../../lean/docs/README.md).

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
| `oracle.open_many<C>(state,positions)` | With `MultiOpening(C)`: return the rows at the positions, in order, and one proof |
| `oracle.check_many<C>(root,width,height,positions,rows,proof)` | With `MultiOpening(C)`: check every position against one proof; return Boolean |
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

The Keccak schemes are `rows.merkle-keccak256.koala-bear/0` and
`rows.merkle-keccak256.koala-bear.ext8-binomial3/0`. Both use Plonky3 0.8.0's
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
alone. The [structured proof contract](../formats/messages.md)
fixes public codec admission.

## Digest-generic Merkle schemes

A digest-generic scheme is one installed instance of a family of binary Merkle
commitments that differ only in their leaf hash `H`, two-to-one compression `C`,
value field and digest encoding. Every instance shares the operations above,
the carriers below and the frames of the [message format](../formats/messages.md);
installing a byte hash such as SHA-256 or BLAKE2s, or another field permutation,
adds an instance and its nominal identity. Digests are values of a fixed width
`w` bytes in the instance's canonical encoding; nothing in the tree, the
openings or the proof layout depends on what a digest denotes. The physical
representations are `plonky3.merkle-digest/0` (root), `plonky3.merkle-proof/0`
(proof), `plonky3.merkle-tree/0` (private opening state),
`plonky3.merkle-digests/0` and `plonky3.merkle-trees/0`.

### Tree

A committed table has width `m >= 1`, height `h >= 1` and row-major rows
`r_0 … r_{h-1}`, each a sequence of `m` value-field elements. With the zero
digest `0` (every word zero; it is never a hash output):

- Layer `L_0` has `L_0[i] = H(r_i)` for `i < h`. A layer is padded: when its
  length is odd and greater than one, `0` is appended.
- While `|L_j| > 1`: `L_{j+1}[k] = C(L_j[2k], L_j[2k+1])` for `k < |L_j|/2`,
  then `L_{j+1}` is padded the same way.
- The root is the single digest of the last layer. The depth is
  `d = ceil(log2 h)`, the number of compression layers.

A position is an index `i < h`. Padding positions are never leaves a verifier
may request. The root encodes neither `m` nor `h`: the verifier's expected
shape fixes the leaf input length `m` and the geometry `d`. Two tables whose
heights have the same depth authenticate the same rows below the smaller
height; a protocol that relies on the exact height uses it as a verifier-known
parameter.

### Openings and the pruned proof

`oracle.open_many(state, Q)` takes a nonempty position list `Q = (q_1 … q_n)`
in the caller's order, duplicates allowed, with every `q_t < h`. It returns the
rows `r_{q_1} … r_{q_n}` concatenated in that order, and one proof for the set
`S` of distinct positions. The proof is the sequence of boundary digests:

1. Let `N_0 = S`.
2. For `j = 0 … d-1`: let `P_j = { n div 2 : n in N_j }`. For each `p` in `P_j`
   in ascending order, and for each child `c` in `(2p, 2p+1)` in that order with
   `c` not in `N_j`, append `L_j[c]`. Then `N_{j+1} = P_j`.

The proof is exactly this list: level 0 first, parents ascending, missing
children ascending. It carries no positions, count of levels or other
metadata; for a single position it is the complete authentication path
`L_j[(q >> j) xor 1]` for `j = 0 … d-1`, which is what `oracle.open` returns.
A child that is a padding digest is still sent when it is a boundary.

`oracle.check_many(root, m, h, Q, rows, proof)` recomputes the root from the
verifier's own `m`, `h` and `Q`; nothing about the shape or the positions comes
from the proof. It returns true exactly when all of the following hold:

1. `rows` has exactly `n * m` elements; duplicate positions carry equal rows.
2. `proof` has exactly the number of digests that step 2 above produces for
   `S`, `h` and `d`, consumed in that order.
3. Starting from `H(r_q)` for each `q` in `S` (one leaf hash per distinct
   position) and replaying step 2 with the supplied boundary digests, one
   compression per parent, the last layer equals `root`.

An empty `Q` refuses with `oracle-positions` rather than accepting vacuously;
a position at or above `h`, a zero width, or a shape over the element ceiling
refuses as an invalid verifier request. A wrong row count, digest count,
noncanonical digest, inconsistent duplicate or mismatching root returns false.
`oracle.check` is `oracle.check_many` with one position. The verifier makes
exactly `|S|` leaf-hash computations and one compression per parent node
visited; these are the hash calls an extraction argument over this scheme
observes. The Boolean is not acceptance until the authored verifier consumes it.

### Poseidon2 instance

`rows.merkle-poseidon2-16.koala-bear/0` commits `koala-bear` rows and holds
`VectorCommitment` and `MultiOpening`. `P` is the
[width-16 Poseidon2 permutation](permutations.md) with Plonky3 0.8.0's default
KoalaBear parameters, and a digest is eight `koala-bear` elements, encoded as
eight canonical four-byte little-endian words (`w = 32`).

- `H(r)`: start from the all-zero 16-element state. For each consecutive block
  of at most eight elements of `r`, overwrite the first positions of the state
  with the block, leaving the other positions unchanged, and apply `P` once.
  The digest is the first eight state elements. A row of `m` elements costs
  `ceil(m/8)` permutation calls. There is no length padding: the verifier's
  width fixes the input length.
- `C(a, b)`: apply `P` once to `a || b` and keep the first eight elements.

These are exactly Plonky3 0.8.0's `PaddingFreeSponge<Perm16, 16, 8, 8>` and
`TruncatedPermutation<Perm16, 2, 8, 16>` in `MerkleTreeMmcs` with cap height
zero, and the proof is its `PrunedMerklePaths` sibling list. Table, digest and
proof limits are the oracle limits above; these kernels charge no external
work. Hashing and the tree are delegated to that pinned implementation, and the
adapter checks shape, positions, widths and digest encodings before calling it.

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
[composed mathematical clients](../../compiler/mathematics.md).
It does not provide a complete FRI application or a BCS/Fiat–Shamir security
theorem. Automatic lowering of an
arbitrary ideal-oracle IOP remains separate work.
