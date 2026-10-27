# Sumcheck

The pair-valued [multilinear protocol](lib.zkc) and coefficient-valued
[expression protocol](expression.zkc) use different round messages. Their
residual relations are different mathematical statements.

| Declaration | Contract |
|---|---|
| `Pending<F>` | Sealed linear obligation held at V, containing an MSB-first prefix and expected residual sum |
| `pending` | Admit a scalar caller statement with an empty prefix; this establishes no truth |
| `Reduce` | Consume a pending claim, check each boundary sum before drawing, and return a successor claim |
| `Residual<F>` | Exact sum of the fixed reference table after total prefix restriction |
| `Shape<F>`, `TableShape<F, Max>` | Separate reference-table and public-input shape conditions |
| `check` | Consume a pending claim and check a complete evaluation against V's public table |
| `Sumcheck` | Complete public-table composition, returning acceptance |

## Pending claims

Construct an initial claim with `pending(claim)`. Pass it to `Reduce` together
with P's checked `multilinear::Table<F>`. The result has three ports: P's
point for this call, P's residual table, and V's `Pending<F>` under the
`evaluation` port. P's outputs are ordinary droppable data. V's claim must move
into another reduction or a terminal check; it cannot be dropped, inspected
by an external module, or returned through an Entry.

A second reduction takes P's residual directly and consumes V's successor
claim. P's returned point covers that call's coordinates; V's sealed prefix
accumulates coordinates across calls. The terminal consumes the accumulated
claim against the original public table. With zero rounds it still consumes
and returns the initial obligation. A complete zero-round terminal accepts
exactly a one-entry matching table.

The continuation has no acceptance Boolean:

```zkc
continuation initial_sum = Residual<F>(in.values, in.claim.point, in.claim.value)
  residual Residual<F>(in.values, out.evaluation.point, out.evaluation.value);
```

Specification field reads consume nothing. A continuing component makes no
acceptance decision; `check` returns the Boolean used by the caller's target.
A normal `false` return must also consume the claim. A failed guard stops and
has no continuation obligation. Swapping two values of the same pending type
is not a frontend refusal: their fixed reference instances must be checked by
the mathematical seam evidence.

## Fixed mathematical references

`Residual<F>` means

```text
claim = sum(restrict_prefix(reference entries, accumulated prefix))
```

The source uses total `multilinear.restrict_prefix` and a Math finite fold.
Cube shape, prefix length, repeat maxima and finite-domain representability
remain separate applicability obligations. `Shape` constrains the reference
Table's width and cube dimension; it does not assert residual truth.

The `parameter values` slot is a fixed mathematical reference. At a call its
assignment is rebound to the caller's chosen reference, independently of P's
working table. In a public wrapper it must decode V's original public vector.
In a partial-reduction chain both calls use the same original reference,
although the second runtime operand is P's smaller residual. Binding to P's
residual anew, choosing an existential table per clause, or choosing a table
after its relevant challenges changes the statement. The binding and causal
scope require checked evidence. They add no reference table to V's runtime
inputs.

`Sum<F>` remains the public target's total sum. `TableShape<F, Max>` selects
V's public vector and round count. These authored clauses are mathematical
contracts, not guards asserting that an adversarial initial claim is true.

## Execution

Each pair-valued round fixes one leading Boolean coordinate. P's table must
have width one and enough remaining variables; excess rounds stop before
sending. Each boundary sum is checked before its challenge. The same random
service is threaded through every round and subsequent call.

The complete wrapper constructs P's table at the full `rounds` dimension
before the first message. The terminal checks V's table after the interaction:
a malformed verifier dimension returns false, as does a wrong complete value.
The pending wrapper adds no wire messages or challenges. Construction handlers
retain `reduce.round`, `reduce.challenge` and `reduce.delivery`; direct
reductions retain `round`, `challenge` and `delivery`.

See the [composed client](../../../../examples/projects/sumcheck/composed/README.md)
for two independently discharged claims and the
[public-table Entry](../../../../examples/projects/sumcheck/README.md).
Partial reductions remain reusable protocols rather than Entry results.

## Expression variant

`sumcheck::expression` retains its arena-indexed scalar-input and ordinary
`multilinear::Evaluation<F>` API. Its round carries `A::Degree + 1`
coefficients for `A::Inputs` ordered factors and one output. Its terminal
checks `A(f1(point), ..., fk(point))`. A partial residual is the sum of that
expression over remaining Boolean assignments, not the multilinear extension
of its Boolean product table.

The total Math reading of a captured Ring expression is a separate required
operation. The existing Local `ring.point` and `ring.affine_sum` kernels do
not supply it. This variant therefore does not advertise the pair-valued
pending-claim contract. A migration needs a typed reference indexed by both
`F: Field` and `A: Ring`, with the exact admitted arena identity and factor
order retained; an opaque true predicate cannot replace that meaning.

See the [expression client](../../../../examples/projects/sumcheck/product/README.md).

## Formal bindings

The retained formal adapters and generated artifacts concern their exact
admitted bodies. Changing the source ABI and helper bodies requires their
regeneration, new body associations and reissued canonical receipts. Existing
proofs are not receipts for the changed source. The mathematical fixed-table,
shape, stopping and uniform-service obligations remain explicit. No compiler,
native provider, commitment-opening or Fiat–Shamir correctness follows from
source formation alone.
