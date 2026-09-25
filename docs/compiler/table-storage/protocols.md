# Protocol representation traces

The current gate
also requires a small complete Sumcheck path and an ordered Merkle operation.
The `Protocols` namespace in [Model.lean](Model.lean) supplies both through the
same generic source, elaborator, direct plan and retained-source checker.
It extends the [table vocabulary](source.md) by interpreted operations; it does
not add a protocol constructor to the common language.

## Additional interpreted operations

Base operations keep their previous types and effects. `lift` embeds their
actual effect trees into the protocol handler interface. New operations are:

| Operation | Signature | Complete behavior |
|---|---|---|
| `send` | `scalar(seven),scalar(seven) → boolean` | Append the ordered pair to the stored message list, emit `sent(a,b)`, return `true` |
| `draw` | `() → scalar(seven)` | Consume the first challenge and emit `drawn(r)`; an empty tape stops `exhausted` with unchanged state and no own event |
| `linear` | `scalar(seven)³ → scalar(seven)` | Return `(1-r)a+rb` without state change/event |
| `point` | `scalar(seven) → point(seven)` | Return the singleton list `[r]` without state change/event |
| `endpointPoint(atOne)` | `() → point(seven)` | Return literal `[1]` when `atOne`, otherwise `[0]`; no state change/event |
| `equal` | `scalar(seven),scalar(seven) → boolean` | Return exact field equality without state change/event |
| `parent(left)` | `digest,digest → digest` | Compress `(sibling,value)` when `left`, otherwise `(value,sibling)`; no state change/event |
| `digestEqual` | `digest,digest → boolean` | Return exact natural equality without state change/event |

The protocol world consists of the previous mutable world, stored ordered
messages and residual challenge tape. Its event type retains base write events
and adds sends/draws. Base calls frame messages and tape; send frames base state
and tape; draw frames base state and messages. Stops preserve these actual frames.
`protocol_direct_preserves` establishes direct lowering equality for every
program, binding and initial state in this extended interpretation.

## One-variable Sumcheck with an actual original-table terminal

The selected table `[2,5]` over `F₇` denotes `f(X)=2+3X`. Its Boolean sum is
`0` in the field. In one ordinary degree-one Sumcheck round, the prover sends
`u=f`. Here the message represents `u` by ordered endpoint values `(u(0),u(1))`;
this uniquely determines the affine polynomial, including in characteristic two.
It is not the quadratic coefficient codec used by another existing profile.

The actual `sumSource` performs:

1. Construct literal endpoint points, form a view of the captured original
   table, and evaluate it at `[0]` and `[1]`.
2. Send those two values. Compare their field sum with the input claim.
3. If the boundary fails, stop `reject` before drawing.
4. Draw the next challenge `r` and calculate the updated claim `(1-r)u(0)+r*u(1)`.
5. Form `[r]`, evaluate the retained original table at that point, and return
   equality with the updated claim.

Only the table and initial claim are supplied inputs. The endpoint points are
resolved literal operations in the retained source; naming a caller-supplied
point "zero" or "one" would not establish its value. The Merkle trace likewise
uses actual ordered named input binding for its leaf, siblings and expected root.

With input claim `0` and tape `[3]`, the plan returns `true`, stores `(2,5)`,
emits exactly `sent(2,5),drawn(3)`, and leaves an empty tape. Both the updated
claim and original terminal are `4`. With claim `1` it stops after the send
and leaves the challenge untouched. An empty tape stops `exhausted` after the
send. Tape `[3,6]` leaves `[6]`; this invocation consumes one coordinate and
does not claim a whole-tape exact-consumption policy.

`affine_original` proves the relevant original-table identity for **all**
one-dimensional tables over any commutative ring and all challenge points.
The finite complete-outcome controls exercise the selected protocol source;
its direct checker additionally accepts the exact lowered plan.

This is a closed honest prover/verifier trace with the original table available
under a shared-table policy. It is not a mechanized projection into separate
adversarial participants, a wire protocol, or a fresh random challenger. The
challenge handler here is deterministic tape consumption. An actual challenge provider must join the
actual prover/challenger/terminal and property argument, including repeated
factors and its selected degree-two message profile. The existing
[Sumcheck source](../../../formal/Zkc/Protocols/Sumcheck/Source.lean) and
[table-source adequacy](../../../formal/Zkc/Protocols/Sumcheck/TableSource.lean)
remain the maintained basis for that wider join.

## Ordered Merkle path

`merkleSource` folds a leaf through two siblings and compares the result to the
supplied root. The first direction is an operation descriptor; the second
places the sibling on the right. With leaf `2` and siblings `5,9`, its root is
`compress(compress(2,5),9)`. Changing the first direction computes
`compress(compress(5,2),9)`.

The concrete compression interpretation is `Nat.pair`, matching this client's
natural-valued `digest`. Correct direction returns `true`; reversal returns
`false` against the original root. Both sources form, but replacing the first
direction fails checking against the unchanged retained source. The directly
lowered original passes the same checker as the Sumcheck trace.

This instantiates an ordered Merkle path computation with a mathematical
compression kernel. It does not claim collision resistance, bounded hash output,
authenticated leaf admission, an opening codec or an actual hash suite.
A selected cryptographic suite must supply its own digest representation and
compression interpretation. The actual shared pass must be applied while retaining
reads and readiness checks; these two direct computations are no cache or
optimization result.
