# Numerical source primitives

The structured reader admits forty additional fixed source bindings. The
first twenty are the scalar FRI source vocabulary: `bool.and`, `bool.not`,
`bool.or`, `field.constant`, `field.inverse`, `field.mul`, `indices.append`,
`indices.at`, `indices.empty`, `indices.length`, `poly.coefficients`,
`poly.coset_interpolate`, `poly.domain_point`, `poly.domain_root`,
`poly.even_odd_fold`, `poly.from_coefficients`, `poly.univariate_evaluate`,
`vector.concat`, `vector.fill`, and `vector.get`.

The other twenty cover the STARK numerical vocabulary: `field.add`,
`field.sub`, `poly.domain_points`, `poly.coset_evaluate_batch`,
`poly.coset_evaluate_at`, `poly.coset_extend`, `poly.opening_quotient_sum`,
`vector.add`, `vector.sub`, `vector.mul`, `vector.scale`, `vector.inverse`,
`vector.geometric`, `vector.slice`, `vector.transpose`, `vector.embed`,
`vector.rotate`, `vector.bit_reverse_rows`, `vector.prefix_sum`, and
`vector.prefix_product`.

Admission selects exact contract names, static roots, capabilities and ordered
ports. Existing scalar arithmetic and binary Boolean operations reuse `Op`.
The new fixed `Numerical` enum supplies the remaining equations through
`Primitive.evaluateOn`, `PIR.Outcome`, and the existing region/process meaning.
There is no evaluator selected by an unknown contract or catalogue tag.
`Primitive.evaluate` is precisely the specialization at `ringFieldModel`.

## Polynomial values

`Ty.polynomial d` differs nominally from `Ty.vector d` and from a polynomial
over any other identity. Coefficients are ascending; normalization removes
only trailing zeros, with `[]` representing zero. `PolynomialValue` contains
an explicit zero witness, the coefficient list, and its canonicality proof.
This permits `Carriers.Value` to stay independent of algebra instances. The
tradeoff is that a polynomial belongs to a selected zero witness: numerical
consumers reject a witness unequal to that model's zero. No ring is silently
chosen on a bare carrier. Products and sequences retain this nominal leaf.

Normalization is canonical, idempotent, length nonincreasing, and the identity
on already canonical lists. Repeated zero normalizes to empty, and converting
a polynomial's coefficients back with the same zero gives the same value.
`NumericalLaws` proves that normalization preserves evaluations and the
mathlib `Polynomial.ofCoeffList` meaning. It also relates Horner evaluation
to mathlib evaluation and proves the coefficient add, scale and multiply
identities. The executable evaluator uses computable lists; the mathlib
noncomputable constructor occurs only in proofs.

Polynomial values remain local. Protocol ports containing them have singleton
scopes; exchange, assembly and statement transport refuse them. The tooling's
bounded polynomial arrays are readable values of its explicit test model,
not a native common-value codec. Native codecs and executable adequacy are
separate obligations.

## Literal and capability admission

Field constants retain the exact wire parameter:

```text
["field_literal", exact_field, "natural", canonical_decimal]
["field_literal", exact_binary_field, "bits", canonical_lowercase_hex]
```

The selected binding fixes the field before decoding the internal value.
Natural literals must be strictly below the catalogue characteristic; they
are prime-subfield values, including in extensions. Binary naturals are thus
only 0 and 1. Other binary values require `bits`, a canonical lowercase `0x`
pattern greater than one, below `2^64` or `2^192` for the two installed binary
presentations. No modular reduction, extension-coordinate packing by decimal,
leading zero, nominal-field substitution or dropped high bit is admitted.
Lean and Python validate these boundaries independently.

A model may have no inverse, ordered roots or binary basis. Operations that
need absent data refuse. A ring-only model therefore remains meaningful and
has proved inverse/root refusal equations. Empty branches that do not use a
capability can still return, as specified below.

`NumericalDomainLaws` keeps the original conditional inverse law and separately
requires a present inverse for each enabled inverse capability. The same
explicit completeness requirement applies to enabled root and binary data.
`OrderedRootLaw` constrains stored data to independently pinned base-field
literals, exact primitive orders, adjacent squaring, and the existing
embedding's ring-hom laws. `BinaryPresentationLaw` constrains the ascending
basis to the installed polynomial presentation and requires faithful bit
interpretation. These are laws about data, never arbitrary numerical-operation
functions.

For KoalaBear and its quartic/octic extensions, roots come from the base field
of characteristic 2130706433, with two-adicity 24. Coordinate five is
`0x0a28f031`, embedded into the selected operation field. The extension's
larger two-adicity does not change this ordering or bound. `KoalaBearRoots`
proves the literal bounds, all 25 exact primitive orders, and adjacent
squaring in `ZMod 2130706433`. Constructing a lawful concrete octic carrier,
its embedding and inverse remains separate from these prime-field proofs.
Other installed root families remain optional and are not inferred merely
from `TwoAdicField`.

## Fixed numerical equations

All index ingress is checked against `2^64`. List lengths and computed output
lengths are checked; unrepresentable collection sizes stop `exhausted`, while
invalid scalar ranges, shapes and semantic premises stop `refused`. These
are full abstract `PIR.Outcome` stops. Native diagnostic codes and allocation
state are not identified with this abstraction.

Scalar inverse requires nonzero and a supplied inverse. Index collections
preserve order and repetitions. Polynomial evaluation uses Horner's equation;
interpolation computes the direct coefficient-level Lagrange sum on the
ordered coset, refusing zero denominators or absent inverse/root data.
It never assumes native FFT correctness.

Vector arithmetic requires equal lengths. Inversion rejects any zero;
empty inversion returns empty. Geometric, fill and inclusive prefixes allow
empty results, using identities 1, 0 and 1 respectively. Slice requires
`start <= length` and checked `start + count <= length`; the endpoint with
count zero is valid. Transpose checks `length = rows*cols`, with
`output[c*rows+r] = input[r*cols+c]`, and returns immediately for zero product.
Embedding maps the exact admitted `BaseField` port. Rotation requires
`k < length`, with no modular reduction. Row bit reversal requires positive
width and positive power-of-two height; columns within each row keep order.

A coset of size `n` requires positive power-of-two size in the stored base-root
family, then nonzero shift. Its points are `s*g_n^i` in natural order. Point
lookup additionally requires `i<n`. Interpolation refuses empty input but
admits size one. A fold requires size at least two and characteristic not two:

```text
fold[i] = (v[i] + v[i+n/2])/2
        + beta * (v[i] - v[i+n/2])/(2*s*g_n^i)
```

The resulting domain has half the size, squared shift, and squared root.
Root ordering and squaring are explicit law obligations.

Batches are column-major, with checked input shape `length = width*height`
and checked output products. Coefficient evaluation permits arbitrary height,
including zero. Any coefficient at degree at least the output domain size
must be zero; coefficients are never silently truncated. Evaluation at a point
interpolates each input column and permits on-domain points. Extension
interpolates at the input coset and evaluates at the output coset, applying
the same high-coefficient refusal when shrinking.

Opening quotient sum validates equal descriptor lengths and initial length,
then, for every descriptor, its column and off-domain point, including when
its weight is zero. It preserves repetitions and computes

```text
result[i] = initial[i] + sum_j weights[j]
          * (values[columns[j]*height+i] - claims[j])/(s*g_height^i-points[j])
```

Claims are arbitrary values here; the operation does not authenticate them.
Width zero skips unused batch domains after shape and ingress checks. An empty
opening descriptor list returns initial after shape checks, without inspecting
an unused domain or shift. These exceptions do not erase argument evaluation.

## Validation scope

`Tests.StructuredNumerics` checks fixed numerical successes and refusals,
normalization, exact literal boundaries, nominal ports and empty cases.
`bridges/structured/numerical_tests.py` checks all forty ordered signatures,
mutations, exact literals and rendering. Existing primitive equations and
model transfer checks cover reuse of the shared evaluator. The tools retain
separate conservative size/work limits for these equations; those limits do
not constitute native resource adequacy.

## Mathematical correspondence

The security package's `Algebra.SourcePolynomial` interprets canonical source
coefficients as Mathlib polynomials and proves evaluation, addition,
multiplication, normalization and exact canonical-length laws.
`Algebra.SourceInterpolation` proves constructive success and uniqueness of the
actual interpolation evaluator. Its premises fix the model's compatible field
structure, ordered distinct nodes and supplied inverse operation with its law.
The concrete KoalaBear bridge instantiates the checked coset roundtrip for the
prime, quartic and octic carriers, including zero and trailing coefficients.

The optional ArkLib integration's `Fri.SourceFold` relates the actual ordered
fold operation to ArkLib's binary fold. `Fri.SourceTerminal` derives code
membership from the source's exact transmitted coefficient length `2^t`;
a weaker degree bound does not discharge that source equality guard. These
operation equations are reusable inputs to complete source correspondence.
They do not establish native FFT correctness or an actual FRI/STARK security
receipt.


The independent reader stores literal parameters in `PrimitiveParameter`, retaining
field identity, encoding and canonical digits as typed constructor data. The JSON
boundary is decoded once. Binding resolution then checks the nominal field and range
without reparsing text, so an exact helper-body certificate can reduce literal admission
inside the Lean kernel. The constructor renderer uses the same tagged data; native
wire rows and retained source identities do not change.
