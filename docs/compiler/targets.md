# Native and relation targets

This is the selected target architecture. The [implementation design](design.md)
owns MLIR interfaces and passes; [runtime design](../runtime/design.md) owns
artifact custody and execution.

The subsequent [protocol pipeline](protocol-pipeline.md) supplies the common-source
and independent-role stages upstream of these target choices. The branch here
consumes an admitted participant algorithm; it does not require a physical plan
before generating verifier constraints.

## Logical source and target selection

A compilation entry selects supplied participant code, static interpretation,
ordered inputs/captures, output meaning and target. Source admission precedes
erasure of information needed for locality, phase or operation legality.
Retain the selected logical source for checking and independent execution.

```text
supplied algorithms + resolved construction + explicit inputs
                         |
                 admitted logical source
                         |
            selective domain transformations
                    /                 \
          native realization      verifier acceptance
          storage and kernels     constraints and exposed outputs
                    |                 |
          closed execution plan   closed relation artifact
                    |                 |
          Rust plan runtime       selected relation consumer
```

These are different abstraction responsibilities, not a requirement to lower
an entire module to one dialect at a time. Arithmetic can expand while tables,
calls or construction operations remain logical. Each packaged target must be
closed under its own supported semantics and requirements.

The earlier OIR label in this target study described executable endpoint behavior.
The joined pipeline now distinguishes operational participant algorithms from
their physical storage/kernel plans; the label does not collapse those two
abstractions. `Zkc.Compiler.Plan` is a direct proof
reference with constructor correspondence to tree programs; it remains useful
to existing clients but is not the new physical-plan definition. Do not add a
Region-shaped second copy merely to label it a plan.

## Native physical plan

The first plan is synchronous, with static callable definitions, explicit
operands, structured bounded control and returned/stopped call exits. Preserve
shared continuations and loops in exported plan data. No mandatory inlining,
path expansion or loop unrolling. General recursion and reentrant/asynchronous
calls require later profiles.

| Plan responsibility | Retained data and interpretation | Initial lowering obligation |
|---|---|---|
| Scalars and domains | Selected field/group/digest representation; public dimensions and canonical codecs | Typed logical value correspondence; range/shape checks for machine representations |
| Immutable storage | Owner-relative handles, actual buffers, layouts and immutable views | Handles denote the same ordered original or derived object in the actual store |
| Preparation | Chosen materialization or reuse, complete dependencies and capacity | Cache validity and readiness; no removal of logical guards, queries or fresh response uses |
| Kernel invocation | Installed coarse kernel contract, ordered arguments and outputs | Actual values and complete success/failure transition satisfy the selected contract |
| Provider invocation | Selected instance, request/reply shape and owned provider state | Correct operation, actual residual state and ordered events; no implicit reset |
| Codecs | Selected encoder/decoder and cursor/buffer state | Canonical domain, complete consumption policy and actual receive effects |
| Control and lifetime | Calls, branch/loop operands, returned/stopped exits, release points | Causal order, stopped suffix suppression, surviving aliases and final output decoding |

Use `func`/structured control where their semantics match; target-specific
operations express coarse kernels, storage and contracted provider effects.
Use `ConversionTarget` legality and `TypeConverter` when representations change.
Mixed IR is an intermediate state. Final serialization rejects unsupported
operations, unresolved casts, invalid references and hidden unsupported callees.
The finite wire schema is implemented together with its consumer and independent
decoder; it is not inferred from arbitrary printed MLIR. The native scalar
implementation now provides that boundary for the finite table client.

Ordinary tensor/memref bufferization can implement an admitted numerical region
after its alias, ownership and failure contract is established. It cannot
choose the logical original, erase an authentication check or decide whether
resource exhaustion counts as protocol rejection. Built-in bufferization
interfaces support local memory reasoning; the protocol contract supplies the
additional meaning. [MLIR bufferization](https://mlir.llvm.org/docs/Bufferization/).

The correctness claim relates the source's complete execution to the plan's
complete execution, using an explicit state relation and a value relation that
can inspect both final stores. Input binding must succeed throughout the
advertised source domain. A handle returned after an invocation still needs a
live owner or an explicit copy/export; equality of handle integers is irrelevant.
The generic execution relation is available now. A proof/checker over the new
physical-plan evaluator requires its own laws, not just the reference `Plan`
theorem. The scalar instance below now supplies those laws and its checker;
additional physical operations require corresponding local laws.

The first physical choice is **retain a lazy immutable view or materialize a
requested table scalar in owned storage**. Repeated reads can reuse the scalar;
an unused result may favor the view. Both retain the original alias and check
the logical shape guard at its original point, even if no later read occurs.
The physical-plan probe proves both complete-result correspondences over the
maintained table meaning for arbitrary ranks and commutative rings. Returned
handles are interpreted in different final stores. It also shows why equal
handle numbers do not establish value equality and why materialization is not
always cheaper.

This selects a concrete plan-level decision before adding a new carrier. The
probe models storage logically. The native scalar gate now implements both
choices with checked capacity/layout data, alias controls and differential
execution. Neither the probe nor those tests prove a Rust allocator.

The checked physical-region reference now lifts that choice through complete
typed control. Its state-dependent value relation includes an immutable frame:
every previously represented value still denotes the same value after an
operation, including a stopped call. Local output
correspondence alone cannot establish this for captured aliases. The generic
`RegionSimulation.run` theorem supplies the composition law; the table client
proves an instance and checks the actual candidate's logical projection. This
uses the existing Region grammar with different operation/value meanings.
Native lowering and capacity checks are now implemented for that scalar profile;
their correspondence evidence is differential execution. The
[physical phase connection](phase-admission.md#physical-table-admission)
now instantiates the same simulation with logical call instrumentation and
consumes the existing source-admission laws. Native progress proofs and broader
endpoint/provider admission remain separate obligations.
The first scalar-store instance is append-only. Releasing a represented cell,
in-place accumulation and destructive reuse require a different rule that accounts
for liveness; the general lifetime responsibility above is not supplied by this
immutable frame. Additional physical operations and analysis may express that
rule without adding control constructors to the common Region grammar.

Exact stop matching also means a native capacity failure cannot be silently
identified with a successful logical evaluation. The unbounded reference does
not satisfy a finite allocator's progress obligation. Native admission reserves
resources outside protocol execution; any future proof of execution after that
admission must cover the actual bounded program and its remaining capacity.
It must not assume the generic all-operations law for arbitrary regions follows
from a successful reservation. Host refusal remains distinct from PIR stops.

## Verifier acceptance target

Select an acceptance predicate from the actual verifier execution and its
exposed outputs. For example:

```text
accepts(input, output) :=
  execution(input) returned an accepting verdict with this output

exists witness, constraints(input, output, witness)
  iff accepts(input, output).
```

The `input` fixes the selected source/configuration and intended public/proof
partition; `output` retains residuals needed by later consumers. Witnesses may
represent internal arithmetic assignments, encodings and provider values only
under the selected constraints. A derived challenge must be constrained to its
actual derivation. Choosing an arbitrary existential challenge does not encode
Fresh randomness or Fiat–Shamir security.

Soundness quantifies over every satisfying witness; completeness supplies one
for every selected accepted output. A stopped verifier has no accepting output
under this projection. This does not identify its execution with a returned
Boolean, and it does not erase native stop reasons from native refinement.
Different outputs can expose different relations; preserving just an acceptance
bit is insufficient when an opening or connected component consumes a residual.

The maintained `Realization.Acceptance` already supplies input binding,
adequacy, following consumers and heterogeneous relation connections. Its
concrete execution projection belongs to each target adapter. No universal
acceptance-execution calculus is required. The bounded Sumcheck/Clean/LLZK
experiment and the new execution projection probe validate these obligations
at their recorded scopes; a production relation compiler remains undelivered.

Native allocation schedules are not mandatory inputs to relation lowering.
Reuse a total arithmetic/verifier subset when it helps both targets, but retain
separate input coverage, constraints, observer and realization requirements.
One relation target may be reached by
[several routes at once, each declaring the inputs it covers](../rationale/acceptance-targets.md).
Recursive proving additionally needs a faithful verifier encoding and an outer
protocol theorem. Acceptance adequacy alone proves neither.

## Shared evidence boundary

The driver retains the original entry and requested claim. A candidate binds
that source, its final target body, interpretation, ordered input mapping,
observer/output relation, rule evidence and typed remaining requirements.
Shared envelope mechanics validate finite metadata; target body decoders and
semantic checkers remain specific to their meanings.

An evidence chain must connect the same actual intermediate artifact and
compatible input/value/state/observation relations. The implementation may
recheck a whole candidate or replay scoped rule evidence. Neither a pass log
nor producer-controlled reference resolution establishes those connections.

The maintained `TransformationRule` is specifically `Program → Plan`; its
`CheckedTransformation` output cannot directly be supplied as another rule's
`Program` input. It is a proved direct-profile API, not an implemented arbitrary
pass-chain calculus. Production logical rules check `Region → Region` changes
under the selected interpretation; final lowering connects that actual region
to the chosen physical evaluator or acceptance relation. Each path must provide
its concrete input/denotation bridge, or check the original-to-final relation
directly. Do not round-trip through the direct reference Plan merely to make
logical rules composable. Phase admission transports through its all-reply law
or is checked again; complete execution refinement alone does not supply it.

### Checked logical folding

The table folding implementation now checks an actual logical change against the
retained original source and composes it directly with physical checking. The
common
[`OperationFolding`](../../formal/Zkc/Compiler/RegionFolding.lean) contract permits
replacing an operation by an existing variable only when its interpreted
procedure equals `done` of that variable for **every input environment**. Its
renaming-aware traversal preserves branches, bounded loops and shared suffixes;
it does not unroll loops or expand continuations.

The installed table rule is `linear(a, a, r) → a`. It checks endpoint variable
identity and uses the field interpolation law. Partial evaluations, restrictions,
provider calls and their producers remain, even if their values become unused.
No runtime sample or cached fact authorizes a replacement. The MLIR pass uses
explicit rewriting without implicit dead-code elimination; capture aliases are
propagated, while a loop accumulator stays distinct from invariant captures.

The checker independently elaborates the original and physical candidate, erases
only physical representation choices, then compares the folded logical bodies.
Acceptance contains equality of logical procedures. The existing arbitrary-handler
simulation therefore still supplies the immutable frame and complete result;
instantiating it with call instrumentation transports the original source's
all-reply admission proof. Its certificate continues to describe the original
body, not the shorter candidate. Rejection means this rule did not establish
equivalence; the checker is deliberately incomplete.

Physical wire version 1 is retained: body grammar, interpretation, realization
and complete-execution claim are unchanged. The installed checker accepts an
additional proved equivalence class; earlier checkers can refuse those candidates.
The direct logical artifact still uses `direct-lowering`, so the CLI requires
`--physical` with `--simplify`. This closes one logical-to-physical checking path.
State-dependent facts, loop invariants for reuse, shared preparation, and
protocol-changing transformations need their own laws and remain future work.
In particular, equality only under a lawful provider cannot populate this
unconditional procedure-equality record. Such a rule must carry its provider
premises and establish the corresponding instrumented admission relation; it
must not weaken `OperationFolding.correct` to equality under the test handler.

Checkers run under the consumer's installed policy. Execution of a proved Lean
checker, per-artifact kernel replay and native differential tests are distinct
assurance methods, recorded separately.

## Contrasting traces and implementation gates

| Client | Source information that survives | Native choice | Relation consequence |
|---|---|---|---|
| Table → Sumcheck → opening | Original ordered factors, variable order, challenge prefix and actual residual | Immutable views/materialization and field kernels; provider calls keep order | Expose the same original/point/value; constrain round and terminal checks |
| Authenticated query | Root/object binding, index, path and each check occurrence | Reuse immutable preparation; execute every logical opening/check | Constrain authentication and actual connected output; no automatic multiproof |
| Correlated service | Actual request, setup binding, response coins and post-stop state | Share immutable setup while consuming fresh response resources | Only a selected verifier relation; service legality is not a crypto theorem |
| Proof/signature connector | Different boundary types and the actual shared key/message | Ordinary calls and explicit connector; no machine-specific tuple | Connect their actual exposed values using the selected predicate |
| Binary/linear or folding operation | Field/basis/embedding or residual algebra | Family-specific typed kernels behind common interfaces | Its own algebraic/encoding law; no prime-field or degree-two assumption in the common layer |

Before the first native path is accepted, trace one table computation and one
ordered service through source admission, physical values, both call exits,
serialization, checking and Rust execution. Include wrong-role/phase, two
different operation slots, dynamic shape, failed-write, alias, capacity and
stale-evidence controls. The existing bounded relation client constrains this
design; implementing a complete relation backend is a following capability.
The [roadmap](../roadmap.md) is the sole delivery sequence.
