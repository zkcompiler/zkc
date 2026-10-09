# Verification and preservation

The compiler validates adjacent transformations of the existing MLIR
program. It keeps the four native mathematical profiles
`protocol → participant → exec → physical`, ordinary SSA and
regions, and the [dialect responsibilities](pipeline.md#profiles-and-dialects).
A validator compares actual operands and control as well as retained metadata.
It does not introduce another editable graph, runtime interpreter or certificate
format. The [refinement specification](../spec/verification/refinement.md) owns
meaning; [status](../status.md#checking-and-evidence) distinguishes
implemented checks from their remaining interpretation assumptions.

## Checking boundaries

The [validation rationale](../rationale/validation.md)
explains why acceptance must cover the actual artifact supplied to the consumer.

A compilation retains its original input and checks the candidate of each step
before publishing it. Adjacent checks compose only through the same actual
intermediate object and compatible interpretations. A supplied artifact has its
own admission boundary; it does not acquire source correspondence from its label.

| Boundary | Required comparison | Current implementation |
|---|---|---|
| Original to prepared protocol | Application/helper substitutions, folds, action operands, statements, role maps and repeat interfaces; admit every definition before erasure | Separate algorithm, polynomial-recipe and pointwise-map checks, virtual helper/application substitution and bounded mathematical value comparison |
| Prepared protocol to participants | Role-indexed SSA correspondence, actual receives, action inputs/results, loop captures/yields and outputs | The actual retained prepared object is compared with the actual projected candidate; restrictions are interpreted per role |
| Participant rewrites | Action operands under supported mathematical laws, unchanged ordered effects and custody | Shared transient value comparison for simplification, fixing and elimination; independent Boolean and polynomial laws |
| Participant to exec | Demand at the consuming action, captures, recipes, result order and partial-call placement | Separate closed recipe/demand validator |
| Exec to physical | Logical participant data flow/order plus validated representation and kernel choices | Fresh checked plans plus a separate reader of every materialized kernel, conversion, operand and declaration |
| Storage release | Retain computation and authored releases; add only admitted releases | Full module admission and comparison after removing only additional releases in a temporary comparison copy |
| Native transcript construction | Selected-entry pruning, actual observations, challenges, state, indices, completion and retained declarations | Independent construction reader over the actual projected subject and generated helpers; source occurrence admission and contract semantics remain premises |
| Checked physical program to emitted artifact | Decoded executable content, entry, host bindings, policy and schedule | Exact program bytes compared directly with physical SSA; run steps checked against retained prepared source; deployment maps checked against original source ports |


The preservation API admits the three forward edges above and same-profile
checks on `participant`, `exec` and `physical`. It refuses skipped or backward
edges. Preparation has its own protocol-to-protocol check. A legal edge is only
the scope of a check, not evidence that every obligation in this table is met.
For Exec-to-Physical, `verifyProjectionPreserved` checks only participant flow
and projection metadata. It does not validate local materialization. The complete
edge is checked by `protocol::lowerPhysical` and the SelectPhysical pass, which
also invoke the internal whole-module materialization validator. Executable
inputs without projection records receive the participant comparison too; it
cannot establish their derivation from a common source.

Preparation and projection have separate postconditions, including when a single
public pass performs both. The raw-source API first validates expansion; the
projector compares its actual prepared input. Run compilation retains an
unsimplified prepared snapshot until final schedule validation. This snapshot is
invocation-local and is never another editable IR or a serialized certificate.

### Comparison relations

These native validators are implementation checks for specified obligations.
They are not proved instances of the specification's checked rule: there,
reconstruction suffices because the rule already has a soundness theorem. The
native constructors have no such theorem. Each implemented checker must state
its recognized transformations and remaining interpretation assumptions.

| Boundary | Intended relation and premises |
|---|---|
| Preparation and participant mathematical rewrites | Equal role-component results and ordered action arguments under the same actual inputs, typed open replies and action interpretations; preserve formation obligations before erasure. This is a mathematical relation, not equal native instruction charges. |
| Protocol to participants | Related entry/result coordinates and each role's ordered actions under the selected open-reply/service meanings. A joint execution claim additionally composes the selected schedule and transport relation; honest delivery is assumed only by a claim that requires it. |
| Participant to exec | Related logical values, action state, returned/stopped outcomes and ordered observations under the recipe/primitive contracts and sufficient realization capacity. Native exhaustion and implementation failures retain their separate execution-policy contracts; operand validation proves no capacity bound by itself. |
| Exec to physical | The same logical participant control and related local computation under the selected representation/kernel contracts, related initial states and explicit capacity premises. Native kernel correctness is a remaining implementation assumption. |
| Physical to emitted artifact | The same executable description, up to the explicitly permitted naming/representation mapping, including invocation and host policy. This binds actual bytes to the checked subject; it does not prove the interpreter or recover omitted source meaning. |

If a claim includes exhaustion behavior, state the budget relation and compare
those stops and residual states explicitly. A sufficient-capacity comparison
cannot be relabeled as equality at arbitrary native caps. The runtime review must
supply evidence for the declared execution-policy behavior separately.

### Role-indexed value correspondence

Use a transient relation between source values and each role's actual candidate
values. Entry coordinates, source action occurrences and region argument/result
positions determine the correspondence. Metadata locates candidate occurrences;
the checker independently checks their kinds, owners, order and operands.

```text
source: received = exchange P -> V(x)

P: sent operand relates to value(P, x)
   value(P, received) relates to value(P, x)
V: value(V, received) relates to the actual receive result
   later guards and returns consume that result
```

Even if V also has an input named `x`, the receive is a distinct value. Honest
transport is an additional premise. A comparison that identifies the two would
accept replacing a check on hostile input with a check on local input.

Total expressions are compared using memoized terms over those fixed values.
An operation key includes its full mathematical identity, relevant attributes,
operand order, result coordinate and logical type. SSA renaming and sharing can
differ. A hash is an index, with equality checked on its key. Resource values and
ordered action results remain distinct; equal types or roots do not merge them.

The checker must compare:

- Every send, guard, query and authored call operand, including unused results
  of actions whose execution remains observable.
- `finish_if` predicates and returned coordinates on the completing path, and
  actual successor values on the continuing path.
- Repeat counts, carried initial values, body argument maps, immutable captures,
  ordered yields and result maps, including zero iterations and nested paths.
- Statement entry bindings and ordered participant outputs.

A loop's induction value is distinct from its trip count. An iteration-local
receive/draw denotes that occurrence under the bound iteration environment;
a static site does not identify all dynamic values across iterations. Rebuilt
capture expressions are compared with their outer terms under explicit capture
substitution. Helper expansion can be checked by virtual argument substitution;
re-running the producer's inliner does not independently validate it.

Use iterative traversal, memoization and explicit work/depth limits. Limit
exhaustion is an unsupported check, not success or a claim of inequivalence.
No witness is needed for the present occurrence-preserving transformations.

### Rewrites and realization

Structural term comparison covers copying, SSA renaming, CSE and removal of
unused total expressions. It does not establish arbitrary mathematical equality.
Check typed selection laws such as constant conditions and identical arms,
including field/group leaves treated as opaque values. Use a bounded independent
Boolean decision for differing i1 expression cones, with agreeing subterms as
cut points, to cover the actual enabled folds after structural equality. Refuse unrecognized
rewrites. Check the supported pattern set against the pinned MLIR implementation;
restrict that set if its transformations cannot be validated. Do not impose a
small global Boolean-variable limit on programs whose expressions already match.

Polynomial comparison checks prefix fixing, nested substitutions, fixed tables,
coefficient/evaluation laws, multilinear observations and bounded interpolation.
Interpolation uses a Vandermonde solve independent of the producer's Lagrange
construction. Invocation-local coefficient and evaluation caches avoid repeating
that work at each action. Symbolic fixing is compared before expansion, preserving
shared factors. These are recognized laws, not a general polynomial prover.

Local algorithms are checked by virtual argument substitution into the source
body while reading the actual expansion, including stop and capture/yield rules.
The six polynomial-recipe realizations are checked by a separate body reader for
shape guards, coefficient convolution, prefix state and declared degree padding.
Algorithm/recipe expansion, physical materialization and storage insertion publish
only after their checks pass on an owned candidate.

Keep the existing independent lowering recipe walk. Producer and validator may
share operation descriptors, types and contract identities; sharing the routine
that emits the candidate would lose a useful wiring check. A recipe's mathematical
law and its native primitive implementation retain separate obligations. Finite
Boolean evaluation tests can strengthen these checks without replacing them.

Transcript construction changes the interaction experiment under its selected
policy. The checker separately requires every cross-role message and validator
query to be covered, including nested message-only loops, and ties a removed
delivery to its paired actual challenge. A charged postorder source walk finds
which loops need transcript state independently of the event list. It reads each helper's contract, codec arguments, source occurrence label and
actual operands; checks ordered state flow, captured iteration coordinates and
conditional completion; and preserves original declarations. Source-event records
are immutable. Generated names remain local emitter state.

Source policy admission and occurrence encoding remain shared semantic inputs to
this check. Admission checks query/delivery selection, public/setup coverage and
original role substitution. Origin labels are distinct and their roles must agree
with prepared actions. Projection formation checks the rewritten action records.
The public reconstruction check composes this independently checked constructor
with exact comparison of the supplied candidate. Neither check proves a
Fiat–Shamir security theorem or the native transcript primitive implementations.

### The emitted artifact

Decode the exact bytes that will be returned, including embedded participant
programs in bundles/deployments. Compare all execution-relevant content with the
checked physical subject: ordered inputs/results, operand references, nested
control, literals, kernel/codec identities, bindings and entry selection. Check
host policy/public-context mappings and the generated schedule against their
own retained source subjects. Validate after storage release and every other
pass that changes the published candidate.

The executable view omits projection/relation declarations, source locations and
argument display names. Immutable local-for capture forwarding is implicit in
the carrier and checked by formation. Original semantics remain available in the
compilation; re-import cannot recover them. The artifact reader permits consistent
SSA renaming, while comparing all bindings, local bodies, participant bodies,
services and entry mappings. It neither exports nor imports an expected model.

The joint schedule reader walks prepared source actions directly, comparing every
role/instruction/anchor coordinate and nested loop group. Lowering metadata only
identifies generated calculation calls whose wiring was already checked. Native
deployment validation decodes the returned envelope, checks its source and byte
identities, retained descriptor/policy, options and wire sites, and derives data,
service and acceptance maps from original source coordinates and actual programs.
Descriptor equality binds the publication to source admission; a matching digest
alone supplies no such relation. C++/Rust codec agreement remains a separate
cross-language obligation. JSON whitespace and equivalent string escapes do not
change this decoded-content comparison. Authentication of an outer deployment
still pins the actual selected bytes.

### Bounded checking and trust

| Reader | Bounds and refusal |
|---|---|
| Mathematical values | Four million charged steps; structural equality first; independent Boolean decisions over at most 12 differing leaves, with conservative shared-subterm fallback; polynomial recursion 128 and interpolation at most 64 points. Work exhaustion reports `mathematical-correspondence-limit`; an unrecognized law reports `mathematical-correspondence`. |
| Algorithm expansion | One million charged steps and depth 64; `algorithm-correspondence` or `algorithm-correspondence-limit`. Capture deduplication uses value-indexed lookup. |
| Polynomial recipes | One million steps, within the admitted recipe slot/degree/operation bounds; `polynomial-recipe-correspondence` with the failed obligation. |
| Pointwise maps | One million steps, with the live scalar formula rederived from the retained original under the shared helper-expansion budget and matched against the candidate body operation by operation. The reader never builds a body and checks every operation kind, operand and binding, but it shares the formula derivation, helper expansion and live-operation selection, with the realizer; `algebra-map-correspondence` with the failed obligation. |
| Physical materialization and storage | Fresh validated selection, full module admission, bounded traversal and exact retained computation; `binding-materialization-correspondence` and `storage-correspondence` diagnostics. |
| Executable bytes and construction | Program admission bounds, one million checker steps, body depth 64; `artifact-correspondence`, `native-transcript-correspondence` and their separate subject/limit refusals. |
| Outer bytes and schedules | At most 16 MiB, 250,000 JSON nodes and depth 256 before parsing; exact unsigned numbers, scalar Unicode and unique decoded keys. Source schedules have depth 64 and one million comparison steps. `artifact-json[-limit]`, `run-correspondence[-limit]` and `native-deployment-correspondence` distinguish these boundaries. |

The admitted upstream arithmetic vocabulary is scalar constants, Boolean
and/or/xor, comparisons and typed selects. Existing-operation greedy folding and
CSE run in mathematical bodies; tensor containers remain excluded. The checker
uses the expression semantics rather than upstream rewrite implementations.
An upstream rewrite outside its recognized laws is refused. Installed compiler
versions and finite fold controls are validation evidence, not a proof of every
upstream pattern or a completeness guarantee for this bounded checker.

These checks still trust MLIR parsing/SSA formation, neutral type and contract
identities, specified primitive/recipe laws and the explicit source-policy
admission rules. They independently discriminate wiring and publication errors.
Native kernel correctness, runtime behavior at resource limits, and Lean
correspondence remain separate obligations.

The outer deployment pin authenticates selected bytes, including the recorded
source digest. It does not authenticate their derivation from that source.
Structural runtime admission and source-relative compilation remain distinct.
Checks are scoped to a source/candidate pair and rule set. Mutating either subject
invalidates them. Reports record the actual route and remaining unchecked steps;
no producer-controlled artifact flag grants assurance.

## Effects, schedules and limits

Total mathematics has no ordered runtime draw or stop. Its realization can still
allocate, charge work or stop. Outlining decides where that work occurs relative
to protocol actions. A rewrite law about mathematical results does not permit
moving a partial call before a guard or discarding a stopped execution's prefix.

MLIR's [effect and speculation interfaces](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
help constrain generic transformations. They do not prove custody, sampling laws
or protocol observations. Retain conservative action effects and closed pass
admission. Do not add generic region/loop interfaces until their successor,
zero-trip and affine-transfer semantics are valid for every supported consumer.
Formation still checks original unused operations before simplifying them away.

Role programs preserve each role's ordered behavior and message dependencies.
The [joint host](../spec/runtime/joint.md) additionally follows its selected
global schedule. Moving another role's draw before a failing guard can change
consumed state and the reported prefix, even if each local program is unchanged.
Thus schedule coverage alone does not establish source-order correspondence, and
per-role preservation does not make all interleavings equivalent. Claims about
independent hosts state their observer and transport assumptions separately.
The compiler outlines at most one calculation for each first-demand cut. This is
its checked lowering policy. It is not a restriction to one local call in a role
program: a supplied bundle can represent two pure locals as `[L]` followed by
`[L,S,R]`. Combining them into `[L,L,S,R]` is outside the admitted group grammar.
The adjacent lowering check refuses a split recipe; the emitted-schedule check
also refuses regrouped anchors against the retained source. Formation and supplied
schedule admission alone cannot grant either correspondence claim.

A split identity calculation control returns the same value and sends the same
bytes with an extra dispatch, frame entry and executable return instruction.
At a fixed instruction budget one version can stop while the other completes.
Local frame entries also remain subject to the runtime's frame limit.
A mathematical equality therefore cannot justify unchanged finite-cost outcomes.
Keep the existing outlining and schedule metadata until a measured overhead,
required memory bound or provider requirement needs different partitioning. Then
extend the adjacent recipe and emitted-schedule checks together, with explicit
cost preconditions. Crossing a draw, guard, message or stop requires its own
preservation argument. A general optimizer and concurrency scheduler are separate
work, and no additional IR is required by these controls.

| Limit | Boundary and comparison |
|---|---|
| Parsing, formation, expansion and checker work | Pre-execution admission/refusal; exceeding implementation capacity is not evidence of an invalid protocol |
| Bytes, dimensions and input loading | Host-authorized admission bounds; preserve exact domain and failure cause when claiming execution coverage |
| Retained buffers and interpreter work | Execution policy with observable exhaustion, residual state and consumed prefix; counts may depend on realization |
| Program loop/condition bounds, provider consumption and attempt limits | Selected program/host contracts, including stops and persistent work across attempts |

Resource-bounded implementations cannot promise identical outcomes at an unchanged
instruction cap merely from equal mathematical results. A comparison states its
capacity preconditions, related budgets or justified observation projection.
Erasing charge events alone does not erase a different stop or final state.
Cap-sweep tests use fixed inputs, provider behavior and scheduling; no universal
monotonicity theorem is inferred from those finite tests. Keep distinct units
rather than combining byte, heap, primitive-work and source-expansion counters.

Future analyses stay attached to a frozen revision and their actual requirements.
[MLIR analysis invalidation](https://mlir.llvm.org/docs/PassManagement/#preserving-analyses)
handles pass-managed analyses; an exported report also needs explicit subject
binding. Preserve original and unsimplified prepared subjects where their remaining
consumers require them. Honest delivery, independent randomness and cryptographic
assumptions remain premises beyond placement and resource-root checks.

This design follows the translation-validation separation demonstrated by
[Rideau and Leroy](https://xavierleroy.org/publi/validation-regalloc.pdf): the
validator may conservatively reject transformations it cannot justify. Their
proved register-allocation validator is a methodological reference, not a proof
of zkc's validators. Native Lean connection follows the explicit
[evidence milestones](../assurance.md#native-correspondence).

### Same-profile executable API checks

`verifyProjectionPreserved` requires admitted subjects. Its Exec-to-Exec and
Physical-to-Physical cases recognize structural identity of the entire protocol
unit, ignoring locations and SSA names. Local bodies, bindings, representations
and projection records are included. A formed same-typed operand change inside
a local function is refused; formation already rejects changes to a guard's
prescribed stop reason. Materialization and storage transformations
use their dedicated comparison contracts; this identity check does not authorize
those rewrites. Adding projection metadata to a supplied executable does not
establish a source relationship and is refused on adjacent executable edges.

## Checking boundaries

| Check | Establishes |
|---|---|
| Local operation formation | Attributes, SSA types, signatures, binding applicability and region interfaces |
| Whole `protocol.module` | Profile rules, declaration closure, role availability, resources and control obligations |
| Relation assets/declarations | Canonical R1CS/AIR structure, exact identities, typed purposes and conflicts |
| Projection and later profiles | Required metadata, participant structure, executable readiness and physical bindings |
| Checked export | Complete verified physical IR and an admitted `zkc.program/0` model |
| Source-relative preservation | An explicit comparison against the retained input at the selected transformation boundary |

Standalone operation validity does not imply a valid complete program. External
clients call `mlir::verify` or checked export; private region-verifier hooks rely
on nested operation checking. Mutable IR must be checked again after an edit.

## Translation and executable reading

[Protocol translation](../../compiler/include/zkc/Translation/Protocol.h)
exports verified physical IR. The core
[execution reader](../../compiler/include/zkc/Dialect/Protocol/Execution.h)
reconstructs executable content without depending on Translation. Its internal
use by a root verifier does not recursively invoke export. Reading an executable
model alone does not establish mathematical or projection invariants.

Mathematical profiles retain native SSA until realization. The serialized
`zkc.program/0` boundary is physical-only. Relation adapters use
[Relations.h](../../compiler/include/zkc/Translation/Relations.h); relation
attribute reading belongs to the core dialect so transformations need not link
Translation. Register required dialects/interfaces before parsing native programs.

## Diagnostics and regression controls

[Diagnostic metadata](../../compiler/include/zkc/Dialect/Diagnostics.h) carries
owned refusal identifiers/details alongside MLIR locations, notes and rendered
text. Callers inspect identifiers without parsing message prose. Metadata is not
proof data or artifact identity; ordinary MLIR errors need not have a native code.

Component checks enforce source ownership and dependency direction. Installed IR,
Translation, Transforms and Compiler consumers exercise their declared
public APIs. Native mutation tests cover actual types, operands, effects and
retained interfaces. These are implementation controls, not a universal native
refinement or protocol-security theorem.
