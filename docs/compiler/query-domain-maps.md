# Total query-position maps

Virtual oracle mathematics computes candidate positions. It does not certify
that a position belongs to an oracle's actual domain. The ordered query checks
that domain at the reached occurrence. Keeping these judgments separate permits
ordinary total mathematics without moving a source failure across authentication.

The selected foundation is a small total unsigned-word vocabulary on the
existing `ui64` index carrier. FRI pairing is library mathematics over that
vocabulary. Checked `index.add`, `index.sub`, `index.div` and `index.mod` keep
their stopping behavior and remain outside total virtual query functions.

## Arithmetic contract

All operands and results are unsigned 64-bit words. The selected operations are
wrapping addition and subtraction modulo `2^64`, bitwise conjunction, and logical
right shift. A shift count at least 64 returns zero. Ordinary selection chooses
one of two indices. These definitions cover every input; there are no overflow
flags, implicit shape premises or poison values.

The existing data dialect owns these operations because the logical carrier is
`ui64`. Upstream integer arithmetic uses signless integer operands; raw oversized
shifts and division by zero do not have the required all-input meaning. A later
represented arithmetic lowering may use standard `arith` operations with the
necessary guards, but an unchecked cast or unqualified arithmetic admission is
not that lowering. See the [MLIR Arith specification](https://mlir.llvm.org/docs/Dialects/ArithOps/).

The shared catalog names each exact mathematical identity, source intrinsic and
selected execution contract. Normal recipe production, independent reading and
native accounting apply. A catalog declaration does not manufacture a kernel,
a proof or a claim that an external formal reader supports the operation.

## Power-of-two pairing

For an actual captured row count `n` and candidate position `i`, define:

```text
h    = logical_shift_right(n, 1)
low  = bit_and(i, wrapping_sub(h, 1))
high = wrapping_add(low, h)
```

For `n >= 2` a power of two, these are exactly `i % h` and `i % h + h`.
Both are below `n`; when `i < n`, one member of the pair is `i`. The largest
representable power-of-two row count is `2^63`.

Outside those premises the expressions still have defined word results. At
`n = 0` or `n = 1`, both outputs equal `i`. At `n = 6`, the outputs are not the
modulo-three pairing. No invalid shape thereby becomes a valid FRI domain.
The source profile performs its ordered configuration checks and retains the
mathematical premises separately.

For natural multiplicative coset order, the additional law `g^h = -1` makes the
paired points opposites. Nonzero shift, characteristic unequal to two, generator
order, inverse laws and successive domain squaring remain separate assumptions.
An even array length proves none of them. The [FRI paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14)
provides the low-degree testing construction; its proximity theorem is not a
consequence of native arithmetic tests.

## Actual shape association

Read the row count from the exact source handle before virtual instantiation:

```text
n = oracle.rows(source)
h = logical_shift_right(n, 1)
folded = Fold(source, n, h, other_captures...)
```

The result shape selects `h` through the definition's named `shape_arguments`.
The independent source comparison checks actual source handles, dimension reads,
capture operands and helper bodies. Admissibility retains the equality between
captured source rows and the source data extent; `shape_arguments` alone does
not prove that equality. A maximum is a resource bound, not an actual extent.

A general virtual definition may accept arbitrary ordinary captures and remain
total. Its FRI interpretation still requires its admissibility premises. Two
anchors with equal row counts may use the same numerical map; authentication
and observation correspondence continue to depend on the actual queried anchor.
No descriptor repeating anchor identity and shape supplies extra authority.

## Alternatives reviewed

| Alternative | Decision |
| --- | --- |
| Treat checked index operations as total after a written `requires` | Rejected: writing a premise does not restrict the helper's argument space or remove native failures. |
| Closed positive/even shape value with restricted formation | Sound with a complete formation/use checker; unnecessary for all-input word mathematics. |
| Total piecewise modulo map for every even domain | Sound if the divisor is sanitized before remainder; not needed by the selected power-of-two FRI profile. |
| General total word operations with library pairing | Selected: one existing carrier, explicit all-input semantics and reusable mathematical operations. |
| Migrate every index consumer to signless `i64` in this unit | Deferred: broader than this requirement and not justified solely by avoiding four data operations. |

The earlier checked-arithmetic domain-map probe remains evidence about that
library and its explicit premises. It is not the production foundation selected
here. The previous joint IR/Lean installation gate no longer applies: native
implementation and exported meanings are owned here; formal support is reported
independently and never inferred from successful native execution.

## Validation boundary

Check zero, one, odd and even nonpower shapes, powers through `2^63`, maximum
words, and shift counts `0`, `1`, `63`, `64`, and maximum. Exhaustive small valid
domains compare library pairing with independent modulo formulas. Mutations
must change actual captured shape, handle, predicate, query order or helper body
and be rejected by the relevant independent reader.

The complete source virtual definition, checked realization and maintained
FRI/STARK callers remain the integration boundary. An arithmetic probe does not
complete that boundary. The [contract register](../spec/contracts.md#shared-oracle-stack-acceptance-boundary)
separates frontend, IR, runtime and formal evidence.
