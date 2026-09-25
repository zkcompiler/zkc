# Field-table source and direct plan

This is the instance of the
[common language](../../spec/language/programs.md) and
[direct plan](../../spec/profiles/compiler/direct-plan.md).
[Model.lean](Model.lean) gives its executable meaning. It uses the maintained
`Language`, `Values`, `Program`, `RawProgram.elaborate`, `bindInputs`, `lower`
and `checkDirect` definitions directly.

## Sorts and original inputs

The first registered field domains are the prime fields `F₂` and `F₇`.
`Domain` denotes their mathematical interpretation, independently of the
backend's storage. Distinct domains cannot be implicitly coerced. A future
field extension needs its own resolved descriptor and field/kernel contract;
it does not change generic control.

| Sort | Logical value |
|---|---|
| `scalar(d)` | An element of the resolved field `F_d` |
| `table(d,N)` | An immutable origin, an ordered list of exactly `2^N` actual field cells, and that shape invariant |
| `residual(d,N)` | An original `table(d,N)` and ordered prefix `p` with `length(p) ≤ N` |
| `point(d)` | A finite ordered list of elements of `F_d`; the consuming operation checks its arity |
| `boolean` | `false` or `true` |
| `digest` | A natural number in this contrasting, noncryptographic client |
| `summary` | An ordered tuple in `F₂ × F₇ × Nat` |

`N` is a natural original dimension. It is never interpreted as an element of
`F_d`. Zero dimension has one cell, and its valid evaluation point is empty.
The first variable is the most significant table-index bit: `[a,b,c,d]` has
Boolean positions `00,01,10,11`. Fixing the first coordinate to `r` yields
`[(1-r)a+rc, (1-r)b+rd]`, if materialized.

The origin identifies an immutable input occurrence within its owning binding.
It is not evidence that a caller supplied an authentic table. The Lean record
permits arbitrary natural origin labels and retains the cells themselves; the
native issuer additionally ensures that one live origin resolves to one frozen
payload. Equality of origin labels alone is not logical table equality.

Malformed cell counts are rejected during input admission, before source
execution. No padding, truncation, modular reduction of dimension, default cell
or out-of-range lookup repairs an input. `admit` in the client checks the actual
list length. Cell decoding and all temporary parsing allocations belong to the
separate bounded input-admission implementation in the native path.

## Public specialization and binding

The initial table source is specialized by public dimensions. Retain the caller's
public expressions, their declared public context and actual ordered public
values. Scope every expression first, bind the exact public list, evaluate in
natural arithmetic, specialize sorts/operation descriptors/counts, and elaborate
the entire resulting body. Only public values participate in this step.
`0 * hidden(0)` is invalid even when simplification could produce zero.

`PublicDimensions.RawDim.scope`, `publicEnv` and `Dim.eval` provide the existing
formation and evaluation boundary. `publicEnv_exact` proves successful binding
retains the actual entries. The client's `Controls.specialize` connects them to
one actual table-evaluation body whose type contains the selected dimension.
This is a concrete template, not a general dependent-language elaborator.

The host retains both that specialization input and the specialized request.
The candidate cannot select a replacement instance. Version-1 `Request` stores
the resulting source, declarations and dependencies, but has no public-template
field. Consequently this host-side connection is a separate native obligation;
`checkDirect` alone does not prove template specialization. A portable template
format, if later needed, requires an explicit versioned design.

Bind all declared inputs and captures against the specialized declarations,
including captures unused on the selected path. Resolve their role, name, sort
and actual value, then freeze their ownership/snapshot. This instance uses the maintained
ordered Lean binder. A native named-input adapter may normalize a supplied map
only after rejecting duplicates, missing entries and extras, and must reconstruct
the exact declaration order. It cannot normalize by sorting declarations or
relabeling values. A private capture stays private to its declared role.

An input's point length is an admitted public shape parameter for the initial
capacity policy. Point elements and table cells need not be public. This choice
does not change the logical `point(d)` carrier or infer permission to publish
private data. Unsupported private-dependent unbounded sizes require another
admission policy.

## Operations and complete behavior

Let `MLE(T,q)` denote the maintained multilinear extension of the **original**
cells of `T` at ordered point `q`. Let `W=(cell₂,cell₇,writes)` be this client's
handler state, and `write(d,x)` its selected event. Every row specifies its own
state/event delta; effects of earlier calls remain in the complete result.

| Operation | Arguments → result | Meaning and effects |
|---|---|---|
| `view(d,N)` | `table(d,N) → residual(d,N)` | Return `(T,[])`; unchanged `W`, no event |
| `restrict(d,N)` | `residual(d,N), scalar(d) → residual(d,N)` | If `length(p)<N`, return `(T,p++[r])`; otherwise stop `refused`. Both cases leave `W` unchanged and emit nothing |
| `evaluate(d,N)` | `residual(d,N), point(d) → scalar(d)` | If `length(p)+length(q)=N`, return `MLE(T,p++q)`; otherwise stop `refused`. Unchanged `W`, no event |
| `add(d)` | `scalar(d), scalar(d) → scalar(d)` | Return field addition; unchanged `W`, no event |
| `record(d)` | `scalar(d) → boolean` | Set `cell_d=x`, increment natural `writes`, emit `write(d,x)`, and return `x≠0`. A returned `false` keeps the write/event |
| `abortWrite(d)` | `scalar(d) → boolean` | Perform the same write/counter/event, then stop `abort`; there is no returned Boolean |
| `orderedPair` | `digest, digest → digest` | Return the exact ordered `Nat.pair(a,b)`; unchanged `W`, no event |
| `pack` | `scalar(two), scalar(seven), digest → summary` | Return the ordered tuple; unchanged `W`, no event |

The digest operation exercises a resolved non-field signature without suggesting
a cryptographic hash property. An actual ordered Merkle compression must be
instantiated with its own interpretation; this toy operation does not supply it.

`record` and `abortWrite` are explicit requests to the same opaque handler.
The program receives only their Boolean replies or stopping outcomes. It cannot
read the hidden world as an SSA value. In both outcomes the other domain's cell
is unchanged. Any analysis fact about the written cell or write count must be
updated or invalidated; a success-only summary is unsound. Neither call changes
the immutable table snapshots. These are complete concrete transition contracts,
not preconditions requiring all recorded values to be nonzero.

`restrict` and `evaluate` have logical shape guards, so they cannot be marked
unconditionally speculatable merely because they have no heap writes. Proving a
guard always succeeds is a separate transformation obligation. Allocation errors
are not additional cases of these logical guards.

## Residual law and representation choice

For every commutative ring, original dimension and valid residual:

```text
evaluate((T,p),q) = Some(MLE(T,p++q))  when length(p++q)=N
evaluate(extend((T,p),r),q) = evaluate((T,p),r::q)  when length(p)<N
```

The second equality includes wrong final arity: both sides refuse together.
`original_cell` connects flat cells to the maintained Boolean indexing;
`evaluate_original`, `restrict_evaluate` and `extend_root` establish these
connections without replacing a product of extensions by the extension of a
pointwise product table. Repeated factor occurrences remain separate operands
when the factor workload is introduced.

The type `residual(d,N)` uses **original** rank, not remaining rank. A loop body
must return the same accumulator sort; fixing one more coordinate changes the
residual value and preserves that type. The remaining rank is `N-length(p)`.
This is an invariant-bearing value with ordinary checked operations. It avoids
adding dependent loop typing for a property the common source can already express.
Static remaining-rank refinements can later remove proved guards locally.

## Branches, repetition and checking

Use the existing structured constructors. Both branch bodies and every loop
body must form, including under a false condition or zero count. Counts are
public naturals. A body `ret` returns the accumulator to the loop; it is not an
endpoint-level early return. A stopped body preserves its actual post-state
and event prefix and skips remaining iterations and the continuation.

The direct plan has the same logical operation descriptors and ordered operand
positions, interpreted by `meaning`. `direct_preserves` specializes maintained
`lower_correct` to every source, binding and initial world in this instance,
including all stopping paths. `checkDirect` compares a candidate to lowering of
the independently retained source. Its success is source-relative logical
equality; it neither authenticates caller inputs nor proves native storage.

The main bound program restricts/evaluates tables over both fields, applies
`orderedPair` to captures `2,5`, and returns `(1,6,Nat.pair(2,5))`. Reversing those
same-typed captures remains well typed but fails direct checking against the
unchanged source. Over `F₇`, `[0,1,2,4]` at `[2,3]` yields `6`, while `[3,2]`
yields `0`. A residual loop fixes `[2,2]` and yields `3` without changing its
accumulator type. A separate three-iteration loop over `F₂` records `0,1,0` and
returns `1`; its natural write count `3` distinguishes it from one iteration.
