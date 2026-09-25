# Fixed-width scalar bytes

This profile selects a scalar prefix codec and its effectful read transitions.
`Byte` and `Bytes` have the common [codec domains](../../realization/codecs.md#codec-domains);
pure decoding and complete receive execution have separate results.

## Fixed-width scalar codec

For a width `w`, let `be w n` be the `w` big-endian base-256 digits of natural
`n`, and let `valueBE` evaluate a byte list in that order. Then:

```text
length (be w n) = w
n < 256^w → valueBE (be w n) = n
be (length b) (valueBE b) = b.
```

The selected scalar-bytecode codec uses width eight and modulus
`p = 2305843009213697249`, with domain `0 ≤ v < p`. Its encoding is `be 8 v`.
This codec definition requires `p < 256^8`; it makes no primality claim.
For any byte list `b`, its decoder is:

```text
front = take 8 b
v     = valueBE front

readScalar b =
  if length front = 8 ∧ v < p ∧ be 8 v = front
  then some (v, drop 8 b)
  else none.
```

The re-encoding guard follows from the fixed-width byte law but is part of the
selected decoder. Every domain value round-trips with every tail. Every
successful arbitrary input decomposes exactly as `be 8 v ++ tail`, with
`v < p` and `tail = drop 8 b`.

For a list of scalars, define `wire xs = concat (map (be 8) xs)`.
`readWords 0 b = some ([], b)`; `readWords (n + 1) b` reads one scalar and
then `n` more from the returned tail, propagating `none`. Successful decoding
returns exactly `n` domain values and a tail satisfying `b = wire xs ++ tail`.
Every domain-valued list round-trips with every tail. Failure of a later scalar
returns `none`; that pure result does not describe any input already consumed
by an effectful implementation.

## Scalar receive effects

A scalar-bytecode read with bound `bnd` has these primitive
effects, where `front = take 8 rest` and `v = valueBE front`:

| Condition | Reply | Consumed bytes | Read-event payload |
|---|---|---|---|
| `length front < 8` | reject `abi_decode_failure:underrun` | `0` | `(0, front)` |
| `length front = 8` and `v ≥ bnd` | reject `abi_decode_failure:noncanonical` | `8` | `(v, front)` |
| `length front = 8` and `v < bnd` | return `v` | `8` | `(v, front)` |

Each event also retains the actual site, read operation and label. The primitive
read leaves the other core state unchanged. Cursor execution increases the
offset by the consumed count; tail execution drops that count. The enclosing
instruction writes its destination only after a successful read. The
value-only projection agrees with `readScalar` when `bnd = p`; it forgets the
state and event difference between the two failures.

A separate end-of-packet operation accepts only an empty tail. Its
`proof_trailing_data` failure consumes no bytes and retains its own event.
Thus the scalar prefix decoder can accept a value whose enclosing packet is
rejected for trailing data.
