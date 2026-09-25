# Codecs and receive effects

A codec connects a logical value with an external representation. A receive
operation additionally changes the state of an input stream and can emit
observable effects. These are separate contracts even when they use the same
decoding algorithm.

## Codec domains

Let `Byte = Fin 256` and `Bytes = List Byte`. A byte codec selects a logical
domain `D`, an input language `L ⊆ Bytes`, and functions:

```text
encode : D → Bytes
decode : Bytes → Except Error (D × Bytes)
```

The [error result type](../conventions.md#mathematical-notation) has disjoint
`ok x` and `error e` constructors. The second component of a successful result
is the unconsumed suffix. `D` can be a refined domain, such as integers less
than a selected modulus. A codec using a
larger host value type states the predicate restricting its logical domain.
Error values distinguish the failures relevant to that codec; the interface
does not require every parser to use the same error vocabulary.

An accepted input is a `b ∈ L` for which `decode b = ok (v, t)` for some
`v, t`. Merely declaring `L` does not establish that every member is accepted.
A complete-packet profile can instead require a successful result with `t = []`.
Prefix decoding and full-packet acceptance therefore have different languages.

An intermediate representation codec can replace `Bytes` by a specified syntax
type. The [direct profile](../profiles/compiler/direct-plan.md#format-parameters) uses
JSON values and an error-returning decoder. It separately specifies parsing
text into those values. An encode/decode pair alone asserts no inverse,
faithfulness, injectivity or canonical serialization law.

## Round trip and faithful decoding

An honest prefix round trip on `D`, for a declared set `T` of allowed tails, is:

```text
∀ v : D, ∀ t ∈ T,
  encode v ++ t ∈ L ∧ decode (encode v ++ t) = ok (v, t).
```

Faithful decoding is a property of every successful input in the claimed
language, including inputs not constructed by the encoder:

```text
∀ b ∈ L, ∀ v t,
  decode b = ok (v, t) → b = encode v ++ t.
```

When a host type represents `D`, the conclusion also requires the decoded
value to satisfy `D`'s predicate. These equations bind the actual remainder,
not just an equal decoded value. A format deliberately accepting multiple
representations can replace exact re-encoding by a specified normalization
relation; it then claims that relation rather than the displayed equality.

The encoder is injective on `D` when:

```text
∀ u v : D, encode u = encode v → u = v.
```

An honest round trip with the empty tail implies injectivity: decode the common
encoding and equate the returned values. A claim about equivalence classes
instead states that quotient explicitly. A digest of an encoding has neither
of these properties merely because the underlying encoding is injective.

## Complete receive results

A receive contract specifies a transition from an actual input state to a
complete result. It fixes the interpretation of successful values, failure
categories, residual bytes or provider, cursor movement and ordered events.
It can use the common [complete execution](../core/execution.md#complete-results)
or a separately interpreted machine-exit record. In either case the result
retains its final state and events on failure.

An effectful adapter MUST establish the selected
[complete-result relation](representations.md#related-complete-results) on
every input and initial state in its claimed domain. A value-only projection
is insufficient when it erases failed consumption or effects. An adapter can
claim a smaller honest-wire domain, but that domain must be explicit in the
judgment and cannot establish arbitrary-wire preservation.

A reference construction may evaluate a pure decoder more than once. An
effectful receive happens once: evaluating it again is a second transition of
the input state and is not covered by the same correspondence.

## Input boundaries and capacity

An implementation MUST distinguish its accepted format from its available
decoding capacity. A byte limit, nesting limit or work limit can refuse a
mathematically well-formed object. The refusal is not a proof of ill-formedness.
Conversely, passing a size check does not establish a valid constructor,
domain value or reference.

A byte-facing text profile fixes the text encoding, invalid-text behavior,
whole-document consumption and subsequent syntax decoder. A claim of canonical
bytes additionally fixes whitespace, escaping and numeric spellings, or another
exact serialization rule. Equality of decoded JSON values does not supply such
a rule. The [direct format](../profiles/compiler/direct-plan.md#text-parsing-and-limits)
specifies its own noncanonical text boundary and decoder limits.

## Selected scalar codec

The [scalar-byte profile](../profiles/realization/scalar-bytes.md) fixes the width,
modulus, decoding and failed-consumption behavior of that selected codec.
