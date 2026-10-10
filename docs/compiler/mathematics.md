# Mathematics and data

Mathematical SSA retains expressions until their analyses and consumers are
finished. Execution recipes and installed kernels then realize the selected
operations. The [mathematics](../spec/ir/mathematics.md),
[polynomial](../spec/ir/polynomials.md) and [data](../spec/ir/data.md)
contracts define the admitted vocabulary and bounds.

## Polynomials

`!poly.polynomial<"F", n>` denotes `F[X0, ..., X(n-1)]`. Constructors retain
constants, coefficients, multilinear extensions, addition, multiplication,
prefix fixing, Boolean suffix sums and interpolation. Observations request
evaluations or bounded coefficients. Named SSA preserves sharing without
requiring dense coefficient expansion.

| Expression | Meaning |
|---|---|
| `mle(T)` | Multilinear extension of the ordered table |
| `mle(T) * mle(U)` | Formal product, generally not multilinear |
| `mle(pointwise_product(T,U))` | Table-product interpolation; it may differ from the formal product away from the Boolean cube |
| `interpolate(evaluate_on_domain(p,D),D)` | Reconstruction below the domain-size degree bound |

Axes, point order and coefficient order are explicit. Constructor-derived degree
bounds can exceed actual degree after cancellation. An author annotation cannot
establish a bound for an opaque polynomial. Transparent acyclic helpers may
carry formal values when preparation exposes their constructors and bounds.
Runtime entry and message ports use concrete values; there is no universal
formal-polynomial ABI.

Static explicit domains support bounded interpolation. Dynamic transforms use
compact installed kernels inside local bodies. Unknown bounds refuse the
selected lowering. [Compiler limits](../spec/ir/limits.md) and recipe-specific
bounds remain separate from runtime capacity.

## Containers and changing shapes

Numeric tensors carry field/group vectors and matrices. Runtime lengths may
change while the logical MLIR type remains fixed. `data.sequence` carries an
ordered runtime count of immutable records, sums or independently shaped data.
The [sequence rationale](../rationale/nested-sequences.md) explains this
choice alongside numeric tensors.

Copyability, total mathematics, disclosure, wire admission and setup authority
are separate properties. A copyable PCS payload can be constructed and matched
locally without becoming total common mathematics. Every alternative is checked,
including inactive arms; live resources and keys cannot hide in wire messages.

Native sequence append copies the immediate slice. Checked operations validate
the expanded sequence, and the Runner charges frame bindings cumulatively.
Repeated indexing or carrying can therefore have quadratic validation or value
charges even when shared live storage fits. `NativeBackend::with_sequence_work_limit`
controls sequence-kernel work independently of Runner payload limits. A storage
change needs an explicit accounting contract and a measured consumer.

## Bulk computation

Scalar field/group expressions, pairings, sparse matrix operations, transforms,
folds and oracle operations compose through ordinary local bodies and the same
Runner. Protocol exchanges, guards, relation bindings and terminal decisions
remain inspectable. Kernels implement numerical primitives rather than complete
protocol execution.

`bn254.gt` is a group value with total pairing from distinct G1/G2 inputs.
Individual values can be carried, sent and combined; dense GT vectors and batched
value-producing pairings are separate extensions. Bulk equality and contractions
avoid repeated scalar-frame capture charges. [Representation](representation.md)
owns implementation selection; [capacity](../spec/runtime/capacity.md) owns
operational limits.

## Protocol and relation consumers

Public-table and weighted R1CS Sumcheck clients expose formal polynomial recipes,
actual received coefficients and explicit terminals. The [relation guide](relations.md)
explains their bounded structural recognizer. A binding cannot make a private
prover value available to a verifier: a private terminal needs an actual
commitment/opening contract.

The [native validation map](../../common/tests/native.md) includes shrinking/growing numeric
state, ragged matrices, batched openings, QAP and AIR compositions. They validate
general mechanisms at their stated scope, without claiming full Groth16, BP+,
FRI or zkVM implementations.

## Extension boundary

The formal-polynomial subset uses flat expressions. Before admitting region
mathematics, availability, helper summaries, demand and lowering need a shared
dependency query covering free captures, plus positive totality and bounds
rules. The current direct-operand interface is sufficient only for its admitted
scope. [Roadmap](../roadmap.md#extend-on-demonstrated-demand) records the
triggers for extending these contracts.
