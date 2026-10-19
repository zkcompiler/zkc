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

Nominal Algebra types carry field/group vectors, indices, field matrices and
field arrays. Runtime vector lengths and matrix dimensions may change while
their logical MLIR types remain fixed. Known shape evidence cannot change a
collection's family or logical binding identity. `data.sequence` carries an
ordered runtime count of immutable records, sums or independently shaped data.
The [sequence rationale](../rationale/nested-sequences.md) explains this
choice alongside numerical collections. The shared `CollectionTypeInterface`
reports structure only; finite, mathematical, Copy/Drop, wire and physical
admission still use their owning contracts. Builtin tensors are not alternate
logical carriers. `algebra.array_from_elements` packs ordered field operands
into a nominal field array, including an empty array. Source arrays and nominal
fixed vectors retain their separate meanings and representations.

Copyability, total mathematics, disclosure, wire admission and setup authority
are separate properties. A copyable PCS payload can be constructed and matched
locally without becoming total common mathematics. Every alternative is checked,
including inactive arms; live resources and keys cannot hide in wire messages.

Native sequences use immutable shared storage. The Runner accounts separately
for retained live storage, newly allocated storage, and logical kernel reads.
Aliases and frame handoffs preserve sharing; equal contents do not establish
allocation identity. Successful validation can be reused for retained immutable
values, while capability custody and external admission remain checked. Sequence
work limits still bound nested validation independently of storage. See the
[capacity contract](../spec/runtime/capacity.md#retained-values-and-logical-work)
for the accounting rules.

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

[Logical Kernel units](../spec/ir/kernel.md) own numerical bodies and their
helper/domain dependencies. Preparation forms units for executable helper
requests; demand lowering forms them for participant calculations. Both retain
an ordered Local wrapper. Physical planning retains those units alongside the
selected Local realization, using the existing normalization and recipe readers.
The checked plan connects numerical correspondence and physical choices before
publication removes the units.
The shared mathematical vocabulary is owned outside the Protocol dialect, so
Protocol and Kernel admission apply the same laws under explicit symbol owners.

The [shared fact contracts](../spec/domains/mathematical-facts.md) keep extent
equality and index bounds separate from exact value identity. Contracts owns the
MLIR-free derivation kernel; Language and Analysis independently extract premises
from source origins and SSA. A query reports proven evidence, missing evidence
or exhausted work. Learning a count preserves the nominal container family and
every ordered admission obligation.

`TotalClosure` admits acyclic total functions and finite-domain definitions under
an explicit symbol-table owner. It checks retained unused definitions, formal
operand dependencies, bounded access premises and polynomial observations with
shared work limits. Known non-fitting polynomial observations refuse even when
unused; unknown bounds on formal polynomial inputs remain obligations when a
caller supplies their constructors. An owner may designate one public entry;
other functions are private. Protocol separately checks participant availability
and ordered actions.
Moving a mathematical definition to another owner does not grant new operations,
resource ports or bounds. The enclosing dialect still owns its declaration
vocabulary and entry rules.

Each analysis describes an immutable subject and its inspected helper closure.
Source checking retains its occurrence-specific origins and symbolic natural
dimensions. After checking a concrete Math call's input conditions, it can
follow returned inputs and full record projections through checked helper calls.
This preserves the original value's facts. A newly collected value instead has
a fresh identity, including through total helper returns and record projections.
An unfiltered collect can preserve an extent or exact count,
while filtering preserves only an upper count, except when that upper count is
zero. A direct call to a Math finite definition keeps its computation at the
caller occurrence during specialization. The independent specialization reader
checks the actual domain, data arguments and callbacks against the source call.
Ordinary wrappers with domain parameters retain their generic formation boundary.
SSA checking substitutes exact helper arguments and reads actual
result constructors. Independent candidate readers construct their own facts;
they do not consume a producer's selected classification. These shared rules and
their adapters belong to the native checking trust boundary.

Typed domain operations remain the mathematical representation. Contracts own
declaration-generated identities and closed scalar/access laws with exact nominal
ports. The [operation-contract guide](operation-contracts.md#mathematical-meaning-and-realization)
describes how logical meaning remains independent of installed realizations.

The compiler answers three separate questions:

| Owner | Question | Retained information |
|---|---|---|
| `Analysis/Computation` | What does this admitted SSA computation contain? | Ordered domain constructors, axes, accesses, payload, nested calls, input environments, seeds, predicates and yields |
| Transforms equation matching | Which supported equation describes this computation? | Pointwise/reduction/contraction roles and exact source occurrences, accesses, seeds and admission premises |
| Transforms recipe selection | Which available logical algorithm can realize that equation? | Selected operations and operand order, or a reason to retain ordered execution |

Physical implementation selection remains a later responsibility. Structural
views contain no reduction, elementwise or bilinear strategy choice. Every view
and equation witness borrows the current IR and must be recomputed after mutation
or cloning. Neither is serialized evidence or another editable mathematical graph.

An axis identifies a constructor coordinate at an exact invocation and traversal
path. Reusing a descriptor in both factors of a product does not merge the axes.
Equal extents establish neither axis identity nor equal elements. Indexed accesses
retain their actual index SSA; non-affine accesses are not forced into affine maps.
The structural view retains all domain constructors in admission order, including
unused ones, and every helper instruction. Nested views carry exact actual/formal
mappings; recurrence state remains distinct from its initial seed.

Equation matching uses these environments for reductions and nested collection
composition. Transient witnesses retain free/reduced axes, accesses, seed and yield
mappings, and the occurrence at which admission is required. They guide producers;
independent readers reconstruct source and candidate meaning without consuming
these witnesses. Recognition misses and unavailable recipes retain the ordered
path. Explicit implementation constraints independently prevent replacement.

Bilinear reduction and whole row/column contractions use the same closed recipe
boundary. Recipes validate nominal signatures, operand and axis roles, and seeded
combination. The independent correspondence readers do not import those recipes.

Map and finite field formulas share lane emission, including scalar subexpression
sharing and cached broadcasts. Collection realization uses explicit typed contract
choices; collection interfaces expose observations without granting execution
permission. A candidate-local binding allocator avoids duplicate generated bindings
and collisions with authored symbols, while preserving authored implementation pins.

Total callbacks may compose indexed arithmetic through ordinary acyclic helpers.
For example, an indexed sum of `left[i] * right[i]` can select a dot even when
its loads and multiplication live in separate helpers. The callback must retain
the relevant extent premises; knowing only that both reads are in bounds does
not establish that the traversal covers both vectors. The independent reader
follows the original calls and carries exact argument meanings back to those
premises. It checks actual candidate operands, including matrix axes and fixed
selectors, without using the producer's normalized body or equation witness.
Returned arguments and repeated captures retain their original value identities.
Fixed pack/projection pairs can be folded before equation selection, including
inside ordinary helpers. Normal canonicalization can also apply this fold.
When selection folds a retained pack, the independent reader interprets that
source pack and its selected coordinate. Projection folding does not remove
other operations or admission checks. General constructed containers and nested
finite computations remain outside this optional normalization rule.

Indexed-access recognition currently covers field vectors and field matrices.
Group-vector indexing retains ordered execution; zipped group/scalar elements can
select MSM. Closed Ring laws justify bounded field comparison; group/module
contractions have a separate interpretation. Admission order, helper expansion,
seed/result mappings and unchanged surrounding declarations remain separately
checked obligations.

Helper normalization has an explicit checked boundary. The producer proposes
an expanded polynomial-free body; a separate reader follows the original helper
calls under positional argument substitution and checks all result coordinates
with the existing independent polynomial laws. A realization stage caches these
checked bodies, copies them into its candidate, and reuses them for recipe
checking; each emitted copy still consumes work. `local.realize` also compares
against its original helper before publication, so a snapshot taken after
normalization cannot hide a substitution
or polynomial error. This is native compiler correspondence checking; the
independent Lean models do not establish a bridge to this implementation.

Optional finite recognition shares separate structural, equation and bound/extent
allowances across definitions and nested occurrences. A private per-callback
structural ceiling covers discovery, preparation and analysis, preserving opportunities after an expensive callback. A memoized
preflight counts helper expansion before copying, including repeated call
occurrences; declining an oversized expansion charges only inspection already
performed. Decision records distinguish `expansion-size` from actual work
exhaustion, and `finite-callback-structural` from a depleted stage allowance.
Optional lane emission has its own allowance. Exhaustion retains ordered
execution with full domain admission; it does not consume the reserve for required expansion. Required map and helper
copies consume cumulative operation and slot budgets across the preparation
window. Domain constructors retain unknown MLIR effects until their ordered
admission is explicit in the lowered code.

An aligned field formula can compose with addition or multiplication reductions.
The recognizer separates the accumulator from the complete associative spine,
retains sibling terms and keeps the authored seed outside the identity reduction.
Specialized contraction equations and general pointwise equations coexist;
target availability selects between checked realizations. This does not authorize
partial, effectful or accumulator-dependent terms as pointwise formulas.

Finite correspondence distinguishes a mismatch from exhausted comparison work.
An optional candidate that exceeds comparison capacity is discarded. Kernel
selection advances the reader-identified occurrence while preserving unrelated
choices. Standalone Local finite realization retains its conservative ordered
retry. Both paths preserve cumulative recognition and checking work, and charge
rejected expansion to a separate discard reserve before restoring required
construction quotas. The ordered candidate must still pass independent checking.
Required-reader exhaustion reports `finite-verification-capacity`; a
correspondence mismatch remains a refusal.

Demand determines the contraction's size. A single selected row or column uses
`matrix.row_dot` or `matrix.column_dot` and returns one scalar. Collecting a
uniform dot fold over all rows or columns can use one matrix-vector product.
The nested rule keeps inner shape admission inside the nonempty outer branch,
so an empty outer collection still skips the inner fold. Uniform nonzero seeds
are broadcast and added after the contraction. Other nested or effectful
callbacks retain ordered execution.

This nested strategy is a bounded rule for an outer matrix-index collection
and an inner scalar dot fold with direct capture mappings and a uniform seed.
Neutral `+ 0` and `* 1` spellings compose through the inner and outer callbacks;
general contraction-plus-bias expressions still retain ordered execution.
It consumes the compositional view, but its conditional matvec emitter and
independent structural reader remain specific to that rule. It does not recover
contractions from arbitrary authored loops or provide general nested-program
equivalence. The [nested collection contract](../spec/ir/nested-matrix-collections.md)
states its precise admission and zero-trip obligations.

## Finite vector reductions

Source binders reach general finite IR through ordinary scoped consumers. Its
checked lowering recognizes admitted native contractions and retains an ordered
loop fallback. `MathematicalSelectionPolicy` enables the finite bulk family by
default and leaves both fusion families disabled. `--no-finite-bulk` selects
the ordered finite fallback while retaining the same domain admission.
`--no-simplify` controls generic total-expression folding independently; it does
not disable mathematical selection. Explicit authored `map` plus reducer calls keep the separate
`algebra.map_realize` path. Native `vector.product` reduces an already constructed
vector to a scalar with empty identity one, separately from elementwise
multiplication. The [source contract](../spec/language/definitions.md#finite-reduction-binders)
owns binder scope, captures and shared scoped extraction.

Maps and their scalar closures remain available through preparation and
projection. Late physical selection uses installed capabilities to choose
specialized primitives, native pointwise expression calls, vector operations or
an ordered finite realization. Required maps retain their vector alternative;
they do not gain an invented ordered callback path. Independent readers compare
the retained source with the actual candidate before publication.

Optional `--fuse-vector-reductions` admits adjacent single-use map/sum pairs.
A product of two row inputs can use a dot product; a supported field formula can
use `numerical.sum`. If those choices are unavailable, the original sum consumes
a native or vector map. All original shape guards and occurrence paths remain.
The [IR contract](../spec/ir/protocols.md#optional-vector-reduction-fusion)
defines eligibility and the [native contract](../spec/runtime/numerical.md)
defines execution and resource boundaries.

`EntryOptions`, `RunOptions` and `NativeProofOptions` carry one
`mathematicalSelection` policy, with independent `finiteBulk` and
`vectorReductionFusion` and `collectFoldFusion` family controls and the `calculationBatching` schedule.
Preparation, total Math demand lowering, proof construction and polynomial
correspondence reconstruction all receive the same policy. Public preparation,
projection and lowering passes expose `optimize-finite` and
`fuse-vector-reductions` and `fuse-collect-fold` options, and the lowering pass also
`calculation-batching`; the participant pipeline forwards these choices to its
stages. Physical storage release remains a separate control.

Total Math demand lowering outlines a participant's pure calculations into
calculation calls placed before actions. With batching, the default, each
needed operation is computed in the one call before the first action whose
demand reaches it, so a value consumed only late is deferred past the
transcript operations, receives and loops in between. `--no-calculation-batching`
computes, before each action, the needed concrete results of operations that
precede it in source order and were not computed yet. Formal polynomial
descriptors are reconstructed beside their consumers; they do not become
participant ports. The compiler's lowering check expects the selected schedule; the
[executable lowering rule](../../lean/docs/spec/executable.md#normalization)
accepts both, since their normal forms are the export's.

Entry packages record `finite_bulk`, `fuse_vector_reductions` and
`fuse_collect_fold` and `calculation_batching` alongside their separate simplify and storage choices;
compilation reports record the three family choices and the schedule. Native-proof deployments record
simplify, storage release, vector reduction fusion, finite bulk, collect–fold fusion and calculation batching in that
order; readers require all six choices. Reconstruction uses the
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

After numerical recipe inlining, an identity recipe can make two distinct
Local captures refer to one SSA value. Capture normalization retains the first
occurrence and rewrites region arguments and loop forwarding together. The
independent kernel reader derives this layout from actual operand identities;
distinct values of the same type and ordered loop state remain distinct.

Preparation expands callers that reach retained computations and the callbacks
those computations name. Unrelated definitions keep their exact bodies.
Source inspection and actual helper substitution have separate cumulative
allowances; copying an unchanged root is not a second helper expansion. Both
phase results and their accounting are independently read before publication.
The [function contract](../spec/ir/functions.md) defines these boundaries.

### Inspecting preparation

`RealizationTrace` optionally records the requested selection policy,
initial/remaining realization allowances, and each stage's completion status,
elapsed microseconds and operation counts. Counts include nested regions and
declarations; timings include each service's checks. A completed stage can be a
no-op. These measurements do not measure native runtime work or memory.

Typed decision events explain the path through recognition and realization:

| Event | Interpretation |
|---|---|
| Selection | A supported choice, or the reason to retain the existing path |
| Proposal | A private candidate attempt under its effective policy |
| Discard | An abandoned proposal and its cause |
| Retry | Another attempt after a discarded proposal |
| Publication | Incorporation into a parent candidate, a returned candidate, or installation for the caller |
| Completion | A scope completed, stayed unchanged, or refused |

Recognition distinguishes unsupported structure or equations, missing evidence,
capacity, disabled policy, implementation restrictions and missing recipes.
Capacity comes from an actual failed query or debit. A successful operation may
spend its final unit; a zero remaining allowance alone is not a capacity failure.
Verification outcomes remain separate: a mismatch is a required failure, while
optional comparison capacity may trigger the existing ordered retry.

Events own their declaration, site and occurrence information rather than
borrowing mutable IR. Parent scopes describe the existing transaction boundaries.
An inner publication is historical if a later failure discards its parent; only
the outer installation event means that preparation changed the caller's module.
The observer records these decisions without supplying evidence, consuming
semantic work or changing selection and retry policy.

For tool-driven inspection:

```sh
zkc-opt input.mlir --zkc-prepare-protocol='trace-mathematics=true'
zkc-opt input.mlir --zkc-prepare-protocol='dump-mathematics=true'
```

Remarks and labeled before/after IR go to the diagnostic stream. `RetainMaps`
through `Finish` remains one stateful invocation; diagnostic phases do not reset
its occurrence or work accounting. Standalone transformations begin a new scope
unless their caller supplies shared work. A private candidate is published only
after its own reader accepts the actual source/candidate pair. Rejected proposals
leave the original body and external expansion state unchanged. Stage records and
IR dumps carry no independent proof authority. Reusing a trace starts a fresh
journal at the outer invocation; nested services append within that invocation.
Observers require exclusive access, including across pass-manager clones. Use
separate observers to retain separate invocations. Readers that return only a
success/failure result report an unclassified verification failure; the journal
does not invent a mismatch or capacity cause.

Fusion compares values and
ordered shape refusals under sufficient resources; changed allocation and
instruction charges may change exhaustion.
No general optimization theorem, backend-failure equivalence or peak-memory
improvement follows. The current scalar Lean bridge does not cover these native vector reductions.

The [finite contract](../spec/ir/finite.md) defines checking allowances separately
from stage-wide recognition. Late numerical selection shares those balances
across occurrences and retries; exhausting optional comparison cannot grant
additional required checking work.

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

Two smaller executable examples exercise compositional source facts directly:
[FRI folding](../../common/tests/fixtures/projects/fri-fold/README.md) collects folded pairs
and checks their next-layer residuals; [LogUp rows](../../common/tests/fixtures/projects/logup-rows/README.md)
compresses tuples and computes reciprocal and Boolean residuals. Both read a
fresh collect using the original collection's indices. The LogUp companion also
constructs a fixed array over a range whose endpoint passes through a helper.
Their tests compare arithmetic with independent integer references under default,
unsimplified and ordered compilation. They establish these mathematical slices,
not complete proof protocols or a performance improvement.

The maintained [AIR library](../../libraries/arguments/stark/README.md) also uses finite
folds for quotient-claim recombination and interaction nonzero checks. Complete
single-table AIR and three-table machine tests exercise these through proof
construction and verification, with both LogUp and grand-product reductions.
FRI retains native polynomial evaluation and coset folding. The
[protocol measurement tool](../../common/benchmarks/README.md) compares these
workloads with bulk selection disabled and storage release enabled separately.
It records process timings, executed work and cumulative allocation charges;
these counters do not establish peak memory or a security theorem.

## Extension boundary

The formal-polynomial subset uses flat expressions. Before admitting region
mathematics, availability, helper summaries, demand and lowering need a shared
dependency query covering free captures, plus positive totality and bounds
rules. The current direct-operand interface is sufficient only for its admitted
scope. [Roadmap](../roadmap.md#extend-on-demonstrated-demand) records the
triggers for extending these contracts.
