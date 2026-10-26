# Checked nested matrix collections

This rule is an instance of the ordered mathematical correspondence for
[finite computations](finite.md), under the installed field and matrix primitive
contracts and sufficient native capacity. It does not equate instruction counts,
allocations, retained storage, exhaustion, or arbitrary provider failures.

For a matrix `M` over the exact nominal field `F`, a vector `x` over `F`, and a
uniform scalar seed `s : F`, collecting the ordered fold of `s + a*b` over every
row gives the vector whose entry `r` is

```text
s + sum(c in [0, columns(M)), M[r,c] * x[c]).
```

The column analogue gives entry `c` equal to
`s + sum(r in [0, rows(M)), M[r,c] * x[r])`. Field associativity and commutativity
justify the installed contraction, including logical sparse zero entries. They
do not authorize changing a callback with effects, an opaque operation, a
predicate, a different nominal field, or an explicit implementation binding.

The outer domain is precisely the corresponding `indices(M)` axis. The inner
matrix view uses that same matrix and the actual outer index. The other factor
is the actual captured vector, identified through the nested call and callback
parameter mappings. The seed is a captured scalar or a field constant and is
independent of the outer index. The returned step denotes the admitted field multiplication and addition;
either commutative operand order is allowed. Bounded neutral additions of zero
and multiplications by one may surround its result, factors or state, or the
outer returned inner result. The source reader reconstructs these identities
independently. Every instruction, including unused work, must still belong to
the admitted total scalar fragment; neutral result syntax cannot hide an effect
or remove an implementation constraint.
Additional ignored vector lanes and nested strict zips retain their admission.

If the outer extent is zero, the result is an empty vector. No inner domain
constructor or shape check is evaluated. Otherwise, constructors are admitted in
source order for the first outer index, zero: matrix view bounds precede that
view's inner extent, and each strict zip compares its first child's extent to
each subsequent child in order. Unused descriptor constructors retain their
checks. Successful first admission establishes the same shape equations for all
remaining outer indices; the exact outer indices domain establishes their
selector bounds. The callback then has no logical stop.

The nonempty branch performs exactly one `matrix.mul_vector` or
`matrix.transpose_mul_vector`, fills an outer-length vector with the uniform
seed, and adds the two vectors. A zero inner extent is admitted normally and
produces a vector containing the seed at every outer position. Shape disagreement
must be rejected by the explicit `control.require` guards before the native
matrix primitive. The selected native outcome interpretation maps those guards
to the original finite admission rejection (`rejected:require`); a native
`matrix-shape` backend failure is not substituted for that logical stop.

The default source form is an `exec.collect` whose scoped callback contains an
`exec.fold`. Their data domains and callbacks remain explicit until finite
preparation selects an algorithm. Optional analysis may inspect an
invocation-local SSA view of those callbacks, including typed placeholders for
nested computations. This view retains associations to the actual source
operations, result coordinates and implementation constraints. It is neither a
replacement program nor evidence for candidate correspondence.

Selection uses the caller's installed recipe inventory throughout the nested
preparation transaction. Withholding the row or column recipe, disabling bulk
selection, or retaining an implementation constraint keeps the checked ordered
path. A pin preserves mathematical recognition but forbids replacing its actual
invocation. Unsupported scalar operations likewise remain ordered.

The candidate uses standard functions and CFG with explicit `exec` outcomes.
An outlined nonempty arm contains the ordered inner admission followed by the
matvec, fill and addition. The empty arm contains only empty-vector construction
and control completion. Captures are distinct from returned values; ordinary
function return packaging does not add a control-completion charge.

Each synthesized admission guard retains the actual inner fold occurrence's
diagnostic location and its ordinary finite admission leaf (`finite_N`, counting
all inner admission primitives). Its executable name encodes the qualified outer
occurrence and outer callback, followed by the inner fold site and step callback.
The ordinary [site encoder](protocols.md#executable-local-calls-and-type-use)
applies its 128-byte hashing threshold and the transaction's cumulative origin
byte allowance. This retains source coordinates without a separate expansion
record. Generated control shape and every executable site need not be identical
across algorithms; these names are diagnostic provenance, not cryptographic
identities.

Preparation retains an immutable source until its owned candidate has been
admitted and independently checked. The source reader reconstructs domain
constructors, actual callback SSA, scalar laws, captures, seed, output and pins;
it consumes no producer recognition view or recipe inventory. The candidate
reader checks actual operands, both outlined arms, capture mapping, ordered
guards, guard coordinates and locations, bulk orientation, seed fill and terminal
result. The enclosing scoped checker accounts for retained definitions,
generated functions and bindings, and the surrounding computation.

Source interpretation debits the optional comparison allowance. Exhaustion is
reported separately from mismatch and can trigger the transaction's checked
ordered retry. Candidate construction, admission and checking retain their
required limits. Failure never publishes a partially prepared source. This
bounded native correspondence does not prove provider implementations, native
resource equality, or a cryptographic protocol theorem.
