# Shared ring expressions

`zkc.ring/0` is a closed, typed expression arena shared by relation and polynomial
consumers. It describes formal ring substitution independently of AIR windows,
protocol randomness and physical storage. Its consumer supplies a closed mapping
from declared inputs to the mathematical objects being substituted.

## Carrier and formation

The exact array form is:

```text
["zkc.ring/0", inputs, nodes, outputs]
input = field_identity
node = ["constant", field_identity, canonical_natural_string]
     | ["input", input_index]
     | ["add", left_node, right_node]
     | ["mul", left_node, right_node]
     | ["neg", operand_node]
     | ["embed", target_field_identity, operand_node]
outputs = [node_index, ...]
```

Fields must have the installed `Field` fact. A literal is a canonical decimal
natural strictly below the field characteristic and denotes its prime-subfield
embedding. Arbitrary extension-field constants use explicitly bound degree-zero
inputs with their own canonical representation. They are not coerced to natural
literals or serialized as an upstream library's internal residues.

Every node edge points strictly backward. Addition and multiplication require the
same field. Embedding requires the target's installed `ExtensionField` fact and
exact `BaseField` association; equal characteristics alone do not justify a cast.
Degree analysis accepts a separate vector of input weights. Negation and embedding
preserve degree; addition takes the maximum, multiplication adds degrees, and
constants have degree zero. Formation records unit-weight degrees saturated at
1,048,577; that sentinel means the bound was exceeded, not an exact degree or
upper bound. It does not restrict admission. A closed view derives the weights
for its selected substitution; its degree analysis refuses bounds above
1,048,576. All nodes must be reachable from an
output. Unused declared inputs are permitted; their binding obligations belong to
the consumer. The ordered output list may contain repeated nodes. Empty outputs are permitted
when the node list is empty, including a relation with no assertions.

The arena admits at most 65,536 nodes and inputs, 4,096 outputs, depth 1,024,
and 8 MiB of canonical encoding. Text ingress checks bytes and
nesting before JSON parsing and rejects duplicate keys, malformed Unicode and
noncanonical numeric tokens. Exact row arities reject unknown fields. Structural
identity is SHA-256 of the canonical encoding, including input sorts and ordered outputs. Equality of meanings is a separate claim.

## Substitution

For each declared field choose an algebra, a field homomorphism into that algebra,
and an immutable assignment to input slots. Interpret constants, addition,
multiplication and negation through those operations. An explicit embedding uses
the admitted field map and compatible algebra interpretations. This permits scalar,
packed-row and coefficient-polynomial evaluation of the same arena.

Input degree bounds are premises of the selected polynomial substitution, owned
by the closed view and excluded from arena identity.
Scalar interpretation alone does not establish them. A coefficient provider must
check the supplied degrees and preserve every resulting coefficient. Truncating
nonzero high-degree terms is not an implementation of this contract.

A caller can select output **positions**. Only nodes and inputs needed by those
outputs are evaluated, and each used input is fetched once. Values must describe
one immutable assignment. A closed AIR view must establish that each selected
read is defined on its assertion scope before arithmetic simplification; an
unused output does not require its reads. Range checks and source authority are
properties of that view, not facts supplied by this arena.

The installed bulk kernels evaluate all outputs. A selected subexpression must
be admitted as its own asset for use through those kernels.

Products remain products after substitution. In particular, the product of two
multilinear extensions is generally different away from the Boolean cube from
the multilinear extension of their pointwise product.

The arena's formation limits do not bound all interpreter allocations, coefficient
work or trace size. Each evaluator provider has additional explicit limits and
failure behavior. Admission or a reference interpreter does not prove native
backend correspondence or the security of a consuming protocol.

## Structural sharing

A sharing map from an admitted arena `A` to an admitted arena `B` is a function
`m` from the node indices of `A` to the node indices of `B` such that:

- `B` declares exactly the inputs of `A`, in the same order and with the same
  fields, including inputs no output uses;
- each node `A[i]` and its image `B[m(i)]` have the same kind, field, literal
  and input slot;
- the operands of `B[m(i)]` are the images of the operands of `A[i]`, in the
  same operand order;
- the output list of `B` is the image of the output list of `A` position by
  position, so it has the same length and repeats where `A` repeats.

Nothing else is required; in particular `B` need not have fewer nodes, and no
node of `B` outside the image is constrained beyond `B`'s own admission.

Under a sharing map every node of `A` denotes the same formal expression as its
image, because both unfold to the same tree. Consequently the field fact of each
node, its degree under every vector of input weights, the inputs used by each
output position, and every substitution of the selected outputs agree between
`A` and `B`, and each used input is still fetched once. The map is syntactic:
`x * 0` is not related to `0`, `1 + 2` is not related to `3`, `a + b` is not
related to `b + a`, equal literals of different fields are different nodes, and
a declared input cannot disappear or change position. A relation's definedness
obligations are therefore the same before and after sharing.

The shared form of `A` walks its nodes in index order and reuses the first node
with the same kind, field, literal, input slot and already-shared operands,
recording the reuse in `m`. It is a sharing map whose target contains no two
identical nodes; it depends only on the node order, costs one ordered lookup
per node within the formation limits, and sharing a shared arena returns the
identity map. When any node is reused the shared form has a different canonical
encoding and therefore a different structural identity. A consumer that
replaces an arena by its shared form refers to that new identity; the sharing
map itself is an in-process value and not part of any exchanged format.

A sharing judgment checks the four conditions above directly against the two
arenas and the map, without reproducing the walk, and refuses on the first
condition that fails. The compiler's `ring::shareExpression` produces the shared
form with its map, and `ring::checkSharing` is that judgment, with refusals
`ring-sharing-inputs`, `ring-sharing-map`, `ring-sharing-node` and
`ring-sharing-outputs`.

## Native bulk substitution

Four ordered algebra kernels use one SHA-256 asset parameter and the installed
`plonky3` provider over KoalaBear or its degree-eight binomial extension. The
parameter is exactly 64 lowercase hexadecimal digits. It is part of the program;
the Host separately admits the referenced arena into an immutable registry.
No proof message installs or changes an evaluator.

The current compiler checks the operation contract and digest reference; the
Host admits the referenced arena. The digest does not expose an arithmetic body
to MLIR optimization. Rewriting or lowering inside an arena would require the
compiler to retain and admit its contents, derive the resulting identity and
check the changed interpretation. Bulk evaluation and protocol compilation are
implemented; compiler transformations of external arena bodies are not.

| Contract | Data operands | Result layout |
|---|---|---|
| `ring.point<F>` | One vector with an entry per arena input | One value per ordered output |
| `ring.rows<F>` | Row-major input vector, row count | Row-major vector with one column per output |
| `ring.coefficients<F>` | Slot-major coefficients, common coefficient width | Output-major coefficients, ascending degree |
| `ring.affine_sum<F>` | Low and high row-major assignments, row count | Coefficients of the sum over rows, output-major |

The input slot count and output column count come from the admitted arena.
The explicit row count also handles constant expressions and empty output lists.
Shape products are checked before evaluation. A vector's storage order does not
choose a polynomial: that meaning comes from the operation and its closed view.

For `ring.coefficients`, each slot supplies a polynomial of degree at most
`width - 1`. The result width is one plus the largest derived output degree;
each output is padded to that width. Widths must be between 1 and 65, and the
derived output degree must be at most 64. These are provider limits, not limits
on formal ring expressions. For `ring.affine_sum`, the polynomial is exactly
`sum_i P(low_i + (high_i - low_i) X)`, componentwise over ordered outputs.
It reuses one coefficient scratch allocation across all rows.

KoalaBear inputs and constants can be interpreted in Ext8 or Ext8 polynomials.
In that interpretation, an input originally declared over KoalaBear may hold an
extension value after polynomial substitution. An explicit KoalaBear-to-Ext8
embedding becomes the compatible map into the selected algebra. The converse
interpretation, Ext8 in KoalaBear, refuses. Arbitrary field identities and
uninstalled embeddings refuse even if their characteristics agree.

The row provider gathers SIMD lanes from the same row-major assignments as the
scalar reference and preserves output order. Both charge the same logical work:
`(rows + 1) * (nodes + inputs + outputs + 1)`, including preparation even when
there are no rows. Coefficient work includes input/output
cells, all node coefficient storage and every convolution term. Affine sums
charge that work once for preparation and for each row, plus the affine-input construction. These are
deterministic accounting units, not measured CPU cycles. Full work is charged
before numerical execution; budget refusal does not reset earlier work.

Each native backend starts with a ring-work allowance of `2^28` units, retained
across proof attempts. Hosts may lower it; invocation reports expose consumed
work and the allowance. The ordinary value and collection limits also apply
to inputs, outputs and scratch. Sharing an asset or input cannot remove an
arithmetic work charge. The asset registry separately bounds canonical bytes
plus decoded metadata to 32 MiB; one arena is at most 8 MiB.

A source Entry carries its arenas in the authenticated package's
[`assets` member](../formats/entry.md#published-entry-package), as canonical
text under the digests its program references. The named Hosts admit those
bodies into the registry and check every reachable reference
[before any invocation](../runtime/entries.md#packaged-expression-assets); the
Entry CLI accepts no separate evaluator manifest. Direct native programs supply
a registry through the native Host and backend constructors. Either way the
registry authenticates arena content only. Relation authority, input binding
and polynomial degree premises remain the responsibility of the closed
consuming view.

## Maintained clients and formal laws

The [expression Sumcheck library](../../../libraries/sumcheck/expression.zkc)
uses a statically selected component for round coefficients and terminal
evaluation. Its [source client](../../../examples/projects/expression-sumcheck/README.md)
binds a product arena and supports KoalaBear input tables promoted to Ext8,
or Ext8 tables directly. Both use extension-field challenges. The verifier
folds its public tables, checks received coefficient counts and round sums,
and checks the terminal expression. No compiler branch recognizes Sumcheck.
This is a public-table execution client; it does not supply a PCS or a security
theorem. Existing BLS polynomial-recipe realization is a separate path.

The [imported AIR client](../../../examples/projects/imported-air/README.md)
binds an arena exported by the [Plonky3 AIR adapter](../../../compiler/adapters/plonky3/README.md)
and substitutes it by `ring.rows` over KoalaBear and Ext8 and by
`ring.coefficients`. The adapter's closed view prepares every assignment from an
authorized instance and a trace; the source program checks shapes and the arena
identity, not that an assignment is such a view.

`Zkc.Algebra.RingExpression` states tree substitution, homomorphism and exact
polynomial evaluation/degree laws. `Zkc.Algebra.RingExpression.Sharing` proves
that a label-preserving node map between untyped arenas unfolds every node and
every ordered output to the same tree, which is the law behind the sharing
judgment; field identities and embeddings are outside that model.
`Zkc.Relation.AIR.RingExpression` preserves
finite-AIR expression evaluation and its public/read degree weights. Those
independent models do not yet prove the native DAG decoder, the native sharing
checker or the provider correct.
