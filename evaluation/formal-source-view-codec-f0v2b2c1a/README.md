# F0-V2B2C1A exact owner-view value codec

This package supplies the canonical-value and collection-order prerequisite
for B2C1 owner projection. It interprets the constructor-complete B2B schemas
as exact K1 `MetaValueV0` bodies through recursive and independently organized
iterative codecs.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-view-codec-f0v2b2c1a/run.py --check
```

The scoped result is
`Affirmative/F0V2B2C1A-A-EXACT-VIEW-VALUE-CODEC`. It does not close B2C1:
the 21 isolated admission/projection families and target publication remain
`CannotAnswer`.

## Why this checkpoint is necessary

B2B used deterministic JSON to test structural inhabitance. That was valid for
single-element diagnostic sequences, but JSON is not the target ordering
oracle. The smallest discriminator is a sorted-unique `PCNode` sequence with
case 2 and case 10:

```text
exact K1 PCNodeBody order:  [2, 10]
diagnostic JSON order:      [10, 2]
```

The old diagnostic validator accepts the second order and rejects the first.
Both codecs in this package do the reverse. B2C1 must therefore compare and
sort collections by recursively compiled target bodies, never by JSON, host
record order, labels, or tuple order.

The checkpoint also catches a second prototype-only mismatch. B1 represented
an identifier atom with raw `ContentRefV0` bytes. An enclosing MetaValue body
requires `MetaBytes(ContentRefV0(id))`; raw reference bytes are not one
complete datum. Both codecs reject the old representation and accept the
correct wrapper.

## Method and boundary

The reference codec recursively compiles records, variants, sequences, and
semantic atoms. The cold codec uses an explicit postorder worklist. Both:

- consume the same independently compiled B2B schema value;
- cover all 22 candidate leaf-body compilers and three exact profile laws;
- frame a module effect as one opaque module/declaration/payload atom;
- encode all 302 B2B branch inhabitants across the six view roots;
- fully decode and byte-identically re-encode every result; and
- enforce `SortedUnique` using exact encoded child bodies.

The module-effect witness authenticates a codec-only module declaration, but
does not claim that its effect semantics pass Core admission. Exact module
effect admission remains a B2C1 family obligation.

Negative controls cover compiler, law, and profile substitution; malformed or
trailing atom bodies; missing records and unknown variants; duplicate and
misordered target sets; and a malformed opaque module payload.

This package is an executable research codec. It does not derive a value from
an admitted Core or Protocol, establish owner/source correspondence, admit an
Oracle, reduction, or module effect, validate an integrated `PCGraph`, publish
a profile, verify the current implementation, prove a theorem, establish a
cryptographic property, or close Q1.
