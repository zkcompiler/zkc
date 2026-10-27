# GKR

The [library](lib.zkc) implements the GKR interactive proof for layered
arithmetic circuits with public wiring. V checks that public `outputs` are the
outputs of the circuit on public `inputs`.

## Circuits

A circuit has `layers` layers of `2^width` gates each. Layer 0 is the output
layer and layer `layers` is the input layer. Gate `z` of layer `i < layers`
adds or multiplies two gates `x`, `y` of layer `i + 1`:

```text
W_i(z) = sum over x, y of add_i(z, x, y) (W_{i+1}(x) + W_{i+1}(y))
                        + mul_i(z, x, y) W_{i+1}(x) W_{i+1}(y)
```

The wiring tables `add_i` and `mul_i` have `3 * width` variables in MSB-first
order `(z, x, y)`; a table entry is normally 0 or 1. The tables of all layers
are stacked into one `add` and one `mul` vector of `2^(selector + 3 * width)`
entries: block `i` of the leading `selector` coordinates holds `add_i`. This
requires `layers <= 2^selector`; later blocks are padding and are never read.
A layer with fewer gates is padded with gates that have no wiring entries; their
value is zero, and so must be the claimed output of an unwired output gate.

| Declaration | Contract |
|---|---|
| `Gkr<F, MaxLayers, MaxWidth>` | Complete protocol: V returns whether `outputs` are the circuit's outputs on `inputs` |
| `Rounds<F, Max>` | Degree-two Sumcheck rounds over the leading variables of a layer's gate polynomial; consumes and returns V's sealed four-factor pending claim |
| `Pending<F>`, `pending` | Linear four-factor residual and scalar admission at V |
| `LayerClaim<F>`, `Input<F>` | Separate layer evaluation obligation and consuming input terminal |
| `Gates<F>` | P's four factor tables of a gate polynomial over `(x, y)`: wiring `add`, `mul` and the values `W(x)`, `W(y)` |
| `select_block` | The block of a stacked table at the MSB-first bits of a position |
| `evaluate`, `evaluate_wiring` | Multilinear extension of a public table at a point, or at `(z, x, y)` |
| `evaluate_coefficients` | A univariate polynomial from its coefficients, constant term first |
| `line_point` | The point `(1 - t) start + t end` |

`layers`, `selector` and `width` must agree between P and V. `layers` is
bounded by `MaxLayers` and `width` by `MaxWidth`. Before drawing any challenge,
V checks both bounds, exact input/output lengths, both complete wiring-table
lengths and selector capacity. These checks also run when `layers` or `width`
is zero. The combined wiring dimension must be below 64; checked index
arithmetic and allocation retain their ordinary refusal and exhaustion behavior.

## Protocol

1. V draws the output point `r_0` (`width` challenges) and sets its claim to the
   multilinear extension of `outputs` at `r_0`.
2. For each layer `i`, with claim `m_i` about `W_i` at point `r_i`:
   - two `Rounds` applications run `2 * width` Sumcheck rounds on
     `f(x, y) = add_i(r_i, x, y) (W_{i+1}(x) + W_{i+1}(y)) + mul_i(r_i, x, y) W_{i+1}(x) W_{i+1}(y)`.
     Each round P sends the coefficients `(c0, c1, c2)` of the round
     polynomial; V checks `2 c0 + c1 + c2` against its claim before drawing the
     round challenge. The rounds end at the point `(b, c)`;
   - P sends the `width + 1` coefficients of the line polynomial
     `q(t) = W_{i+1}((1 - t) b + t c)`;
   - V evaluates the wiring tables at `(r_i, b, c)` and checks the final round
     claim against `add (q(0) + q(1)) + mul q(0) q(1)`;
   - V draws `t` and continues with claim `q(t)` at `r_{i+1} = (1 - t) b + t c`.
3. V accepts when the multilinear extension of `inputs` at `r_layers` equals the
   final claim.

Malformed degree messages cannot occur: each round receives exactly three
coefficients and each line exactly `width + 1`. Received round checks precede
their challenges. A wrong round sum or a failed wiring check stops V with
`reject`; a wrong input evaluation returns `false`. Malformed public tables
are rejected by the initial shape checks, including unused wiring blocks.

P evaluates the circuit itself, recomputing the values of the layer below each
layer from the inputs, and builds its round and line polynomials from dense
tables. V's work is dominated by the dense wiring evaluations,
`O(2^(3 * width))` field operations per layer; there is no succinct wiring
representation, commitment or zero-knowledge claim.

## Residual and layer relations

`Rounds` takes and returns `Pending<F>` at V. Its `Residual<F>` relation fixes
all four original reference vectors and states the exact sum after separately
restricting `add`, `mul`, `left` and `right` at the accumulated prefix:

```text
sum_y add(prefix,y) (left(prefix,y) + right(prefix,y))
      + mul(prefix,y) left(prefix,y) right(prefix,y) = claim
```

The source selects the registered `gkr.rounds/0`, `residual`, revision `0`
meaning with its exact nominal field argument. The registry requires exact
Boolean-cube decoding and a prefix no longer than the cube dimension; malformed
arguments make the relation false. It does not truncate a four-way zip or rely
on a caller precondition to make a Math function total. The checked
`residual_restricted` law identifies this meaning with the sum of the four
separately restricted factors. `Shape` states equal factor lengths separately.
The degree-two active-variable condition remains the family's mathematical
applicability obligation. An arbitrary four-factor input can have degree three;
the actual GKR layout is what supplies the stronger degree-two condition.
Neither shape nor that degree condition is replaced by a true placeholder.

P's working factors and returned point remain ordinary data. The left call's
pending result moves directly into the right call. V's sealed prefix then
contains both points; the owning module separates them for the existing wiring
and line checks. Empty points remain valid when width is zero. The two calls
must use one original mathematical factor reference, even though the right
call's runtime operand is P's restricted table. Caller-side reference
instantiation is independent of that working table and grants V no table access.

A gate residual is not a multilinear evaluation of Boolean product values:
extension of a product generally differs from the product of extensions.
`LayerClaim<F>` therefore has its own `LayerEvaluation<F>` relation against a
fixed mathematical layer table. Output selection creates the first layer
claim. Each layer consumes it, converts to the gate sum, consumes the final
gate residual in the wiring/line check and creates the next layer claim.
`Input` consumes the final layer claim and returns the existing input equality
as acceptance. A stopped guard has no successor; every normal return consumes
or transfers its pending values. No pending claim crosses an Entry.

The wire protocol remains degree two with exactly three coefficients per
round, the existing output-coordinate draws, line coefficient messages, line
challenge/delivery and input terminal. The new terminal protocol has no wire
effects. Source bodies, helper identities and receipts still change.

### Circuit identity boundary

The independent circuit evaluator, layer-to-factor identity, output selection,
line-combination law and input adequacy remain separate obligations. A layer's
reference cannot be chosen by treating P's working factors as authoritative.
`LayerEvaluation` is a defined table relation; it does not by itself identify
that table with circuit evaluation.

The root selects two registered `gkr.circuit/0` relations, revision `0`:
`shape`, specialized by the nominal field and both static bounds, and `outputs`,
specialized by the field. Their ordered operands retain the input, complete
wiring, dimensions and output vectors. The registered `CircuitEncoding.Outputs`
meaning requires valid shape and compares the output vector with independent
mathematical circuit evaluation. Evidence cannot choose another predicate or
replace this evaluation with P's computation. Malformed shape and a changed
output have explicit refusal theorems. Connecting each inner layer's reference
to that circuit remains a separate library law.

## Lean

The [multi-round security chapter](../../../../lean/docs/spec/fiat-shamir-security.md#the-plain-gkr-verifier)
gives the plain verifier a round-by-round certificate with error
`max(2, width) / |F|` per challenge and bounds its Fiat–Shamir transform. For
the retained compiled `example::Proof` Entry of the GKR project, Lean reads the exported
validator's instructions as that plain verifier on well-formed statements and
transfers the bound for that exact body
([compiled Entry](../../../../lean/docs/spec/fiat-shamir-security.md#the-compiled-gkr-proof-entry)).

Source changes require regenerated body bindings and new canonical receipts.
The retained artifacts do not certify the changed source.

## Participant code

Local helpers keep scalar field arithmetic in mathematical helpers and select
table blocks by splitting rather than by indexed reads. The whole unit, P's
helpers included, stays within the [structured import](../../../../docs/spec/formats/structured-source.md)
profile, so its original verifier can be imported by the independent Lean
models.

The [GKR project](../../../../examples/projects/gkr/README.md) selects BLS12-381 Fr
and exercises interactive and noninteractive Entries.
