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

## Native bulk substitution

Four ordered algebra kernels use one SHA-256 asset parameter and the installed
`plonky3` provider over KoalaBear or its degree-eight binomial extension. The
parameter is exactly 64 lowercase hexadecimal digits. It is part of the program;
the Host separately admits the referenced arena into an immutable registry.
No proof message installs or changes an evaluator.

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

The Entry CLI accepts `--evaluators=PATH` for `run`, `prove`, and `verify`:

```text
["zkc.ring-assets/0", [["expected_sha256", "path/to/arena.json"], ...]]
```

Paths are resolved from the invocation's working directory. The manifest is at
most 64 KiB with at most 256 entries. Each asset must match its expected digest;
duplicates and missing references refuse. Configuration files are protected
against output publication to the same path. This registry authenticates arena
content. Relation authority, input binding and polynomial degree premises remain
the responsibility of the closed consuming view.

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

`Zkc.Algebra.RingExpression` states tree substitution, homomorphism and exact
polynomial evaluation/degree laws. `Zkc.Relation.AIR.RingExpression` preserves
finite-AIR expression evaluation and its public/read degree weights. Those
independent models do not yet prove the native DAG decoder or provider correct.
