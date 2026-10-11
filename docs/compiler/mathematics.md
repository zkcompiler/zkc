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

## Analysis and realization boundaries

Typed domain operations remain the mathematical representation. Contracts own
closed scalar laws, lane lifting and contraction equations with exact nominal
ports. `Analysis/Computation` derives bounded, read-only views of existing SSA:
iteration and admission order, accesses, captures, seeds, nested calls and result
demand. These views borrow the current IR and must be recomputed after changes.
They are neither serialized evidence nor a second mathematical language.

One structural analysis records constructor provenance for each helper item and
the complete payload, including unused instructions. Concrete reduction,
elementwise and bilinear equations consume these facts and a shared admission
of the payload's installed contracts. Bilinear selection is part of the same
view. Finite realization uses its admission order and seed/capture mappings;
if bounded analysis cannot produce a view, the ordered realization derives the
same mappings directly from the finite ABI. Selection never uses an extent fact
known only on a total operation's actual operands: the source domain or helper
premises must also make it available to the independent reader.

Transforms select among admitted realizations and the ordered fallback. Map and
finite field formulas share lane emission, including scalar subexpression
sharing and cached broadcasts. Their common lane analysis takes explicit lane
arguments and treats other arguments of the exact field type as uniform. It
retains only indexed-read mappings used by the emitter, with no public scalar
mode inventory. A separate reader reconstructs meanings from
actual source and candidate operations without the selector's classifications.
Closed Ring laws justify its bounded comparison; ordered guards, helper
expansion and unchanged context have their own checks.

Helper normalization has an explicit checked boundary. The producer proposes
an expanded polynomial-free body; a separate reader follows the original helper
calls under positional argument substitution and checks all result coordinates
with the existing independent polynomial laws. Recipe checking reads only these
checked bodies. `local.realize` also compares against its original helper before
publication, so a snapshot taken after normalization cannot hide a substitution
or polynomial error. This is native compiler correspondence checking; the
independent Lean models do not establish a bridge to this implementation.

Optional finite strategies share a work allowance and may decline before payload
emission. Their ordered fallback retains full domain admission. Required maps
use their existing cumulative helper limits; an optional optimization allowance
does not impose a new map admission limit. Domain constructors retain unknown
MLIR effects until their ordered admission is explicit in the lowered code.

Demand determines the contraction's size. A single selected row or column uses
`matrix.row_dot` or `matrix.column_dot` and returns one scalar. Collecting a
uniform dot fold over all rows or columns can use one matrix-vector product.
The nested rule keeps inner shape admission inside the nonempty outer branch,
so an empty outer collection still skips the inner fold. Uniform nonzero seeds
are broadcast and added after the contraction. Other nested or effectful
callbacks retain ordered execution.

This nested strategy is a bounded rule for an outer matrix-index collection
and an inner scalar dot fold with direct capture mappings and a uniform seed.
It consumes the compositional view, but its conditional matvec emitter and
independent structural reader remain specific to that rule. It does not recover
contractions from arbitrary authored loops or provide general nested-program
equivalence. The [nested collection contract](../spec/ir/nested-matrix-collections.md)
states its precise admission and zero-trip obligations.

## Finite vector reductions

Source binders reach general finite IR through ordinary scoped consumers. Its
checked lowering recognizes admitted native contractions and retains an ordered
loop fallback. `MathematicalSelectionPolicy` enables the finite bulk family by
default and leaves vector reduction fusion disabled. `--no-finite-bulk` selects
the ordered finite fallback while retaining the same domain admission.
`--no-simplify` controls generic total-expression folding independently; it does
not disable mathematical selection. Explicit authored `map` plus reducer calls keep the separate
`algebra.map_realize` path. Native `vector.product` reduces an already constructed
vector to a scalar with empty identity one, separately from elementwise
multiplication. The [source contract](../spec/language/definitions.md#finite-reduction-binders)
owns binder scope, captures and shared scoped extraction.

Optional `--fuse-vector-reductions` exposes admitted maps through checked
`RetainMaps` local expansion, recognizes adjacent single-use multiply-map/sum,
and replaces it with all original shape guards followed by dot. Residual maps
and helpers finish through the ordinary realization path before the strict
local snapshot. Independent checks compare both expansion stages and the
actual fused candidate with their originals, retaining full occurrence paths.
The [IR contract](../spec/ir/protocols.md#optional-vector-reduction-fusion)
defines exact eligibility and shared bounds.

`EntryOptions`, `RunOptions` and `NativeProofOptions` carry one
`mathematicalSelection` policy, with independent `finiteBulk` and
`vectorReductionFusion` family controls. Preparation, total Math demand
lowering, proof construction and polynomial correspondence reconstruction all
receive the same policy. Public preparation, projection and lowering passes
expose `optimize-finite` and `fuse-vector-reductions` options; the participant
pipeline forwards both choices to its stages. Physical storage release remains
a separate control.

Entry packages and compilation reports record `finite_bulk` and
`fuse_vector_reductions` alongside their separate simplify and storage choices.
Native-proof deployments record simplify, storage release, fusion and finite
bulk in that order; readers require all four choices. Reconstruction uses the
selected policy, including when generic simplification is disabled.

The explicit `rewriteLocalAlgorithms` preparation service admits the immutable
whole source and owns each proposed rewrite. It retains finite and map structure
through the checked selection window, then expands residual helpers. When
there is no finite declaration or requested fusion, helper expansion runs once;
an empty intermediate window must not charge the same expansion twice. Independent
readers compare each actual nested-collection, finite, map and fusion candidate and both staged
expansion results before publication. Generic simplification runs afterward;
projection and execution lowering retain their structural Local preservation
checks against the accepted preparation result. No additional profile or
post-projection Local rewrite window is introduced.

Fusion compares values and
ordered shape refusals under sufficient resources; changed allocation and
instruction charges may change exhaustion.
No general optimization theorem, backend-failure equivalence or peak-memory
improvement follows. The independent Lean reduction laws cover their list
model, with no source capture or native runtime adequacy theorem.

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
