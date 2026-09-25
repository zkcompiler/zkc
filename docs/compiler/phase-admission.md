# Checked phase admission

Finite source admission joins the
[source-relative plan checker](source-plan.md) to the existing
[interaction semantics](../guides/composition.md). It establishes enabled calls
and permitted normal-return phases for a consumer-selected interaction. It does
not infer cryptographic contracts from operation names.

The normative contracts are [phase analysis](../spec/verification/analysis.md),
[admission through interpretation](../spec/core/interpretations.md#phase-admission)
and the [phase-certificate format](../spec/profiles/compiler/direct-plan.md#phase-certificate-sidecar).
This page explains the common tree/compact checker and its concrete consumers.
The current table runtime consumes phase certificates under a separately selected
policy. The earlier scalar reproduction below remains historical evidence;
[native table admission](#native-table-admission) records the current path.

## The consumer boundary

A well-typed source can request a challenge before committing. Its direct plan
may preserve that source exactly. Preservation therefore does not establish
phase legality: the consumer checks the retained source against its resolved
interaction separately, then combines both results for the same source and plan.

[`PhaseAdmission`](../../formal/Zkc/Source/PhaseAdmission.lean) provides:

| Component | Obligation |
|---|---|
| `Policy.step` | Abstract returning phases for an operation at an abstract entry phase; absent means unsupported |
| `Realizes` | Every supplied summary describes the actual operation meaning, for all arguments and every interface-typed reply |
| `Certificate` | The actual source's control shape, with finite phase invariants on loops |
| `check` | Compute a sufficient set of returning phases, checking both branches and loop invariants |
| `checkRegion` | Check compact binding directly, composing returning covers without duplicating the shared suffix; tree checking uses `toRegion` |
| `Admitted` / `admit` | Retain successful checking and containment in the consumer's permitted return phases |

The realization relation connects abstract phases to concrete interaction
phases; it need not be equality. An operation may denote multiple interface
calls. Its law supplies both `Conforms` and a returning-phase postcondition for
that entire meaning. No law about one honest handler can replace this obligation.

The consumer selects the policy, its realization laws, entry phases and allowed
return phases. A certificate cannot overwrite those choices. There is no change
to the direct-plan format, claim or rule: phase admission is a separate result.
Missing summaries or failed certificates mean **not admitted by this analysis**,
which is weaker than proving the program semantically illegal.

[Summary translation](../../formal/Zkc/Source/PhaseAdmissionInterpretation.lean)
composes a proved policy realization with an
[operation-interpretation admission](../../formal/Zkc/Semantics/InterpretationAdmission.lean).
It retains the source certificate while relating its abstract phases to the
expanded lower protocol. Both legality and returning-phase relations are consumed.

The [algebraic-round source](../../formal/Zkc/Protocols/AlgebraicRounds/Source.lean)
has a direct semantic admission proof for its validity-dependent challenge branch.
This finite, value-insensitive policy checker cannot infer that branch's guard
fact. Extending compiler admission requires a proved guarded analysis and actual
fact production; operational correspondence alone does not supply that analysis.

## Analysis and proof

The abstract state is a finite set represented by a list. An operation joins its
summary across every possible entry phase. Branches join both returning sets;
joins remove duplicates. Returns preserve the current set. Stops have no normal
returning phase, while their actual outcomes, state and events remain observable.

A loop certificate supplies an invariant. Checking requires entry containment,
conformance of the body from every invariant phase, containment of all body
returns in the invariant, and admission of the continuation from that invariant.
The count remains a mathematical natural and is never unrolled for admission.

This applies Hoare-style sequencing and inductive invariants to the existing
`Boundary.Returns` judgment, with a sound abstract transfer relation. The
`checkRegion_sound` theorem proves conformance and returning coverage by induction
on compact source; `check_sound` follows through the tree embedding, and
`Admitted.sound` adds the requested final-phase restriction.
The methods are established: [Software Foundations, Hoare Logic](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)
and [Cousot and Cousot, POPL 1977](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
This implementation proves a sound analysis, without claiming a complete
abstract domain, least fixed point, Galois connection or novel program logic.

[`Compiler.Admission`](../../formal/Zkc/Compiler/Admission.lean) combines that
source result with `CheckedPlan.correct`. For any stateful handler, every actual
instrumented plan call is enabled, and every normal return has a permitted phase.
Erasing phase instrumentation recovers the complete ordinary plan execution.
A stopped provider call retains its entry phase and its actual residual state
and events; no typed reply or successful phase transition is fabricated.

The analysis is intentionally insensitive to values. It checks dormant branches
and zero-iteration bodies, and may lose correlations between replies and later
branches. The tests prove both a safe zero-loop refusal and the impossibility of
an exact-phase summary that ignores a phase-changing reply. A future client that
needs such correlations should add a value/phase relation or a different checked
certificate rule. The general `Conforms`/`Returns` semantics already allows it.
This is an extension trigger, not a reason to weaken the current summary law.

Defining legality as what this checker accepts would make the zero-iteration
example illegal, and a general refinement-type solver is more than the
supported sources need. An extension keeps advancement on the actual reply and
accounts for unreachable branches explicitly.

## Concrete compiler connection

[`InteractiveRound`](../../formal/Examples/InteractiveRound.lean) has a local
endpoint with `commit`, `challenge` (receive) and `respond`, all returning `Nat`.
Its phases are `ready → committed → challenged → ready`. The example resolves
exactly `interactive-round/1`, local role `prover`, initial phase `ready`, and
normal returns at `ready`. Its operation laws are proved for every natural reply.
It models interaction order; it supplies no cryptographic commitment or random
challenge distribution, global choreography projection or secrecy theorem.

The separate C++ vocabulary supplies only signatures. Generic MLIR import,
flow verification and export are unchanged. The Lean executable offers distinct
`check`, `admit` and `run` commands; execution requires both checks.

Certificate JSON uses exact arrays:

```text
["terminal"]
["next", continuation]
["branch", yes, no]
["loop", [phase, ...], body, continuation]
["bind", body, continuation]
```

The vocabulary's phase codec and a depth limit parameterize the decoder. The
example allows 256 certificate levels and one MiB per file. Unknown fields,
tags and phases are refused. Successful decoding is not admission, and an
admission result is not a serialized kernel proof. Parsing, compiled-checker
execution and consumer resolution retain their implementation trust.

## Native table admission

The installed `table-round/1` policy fixes role `trace`, initial phase `ready`
and permitted normal returns at `ready`. A send moves `ready → sent`; a draw
moves `sent → ready`. Other table operations preserve phase, including their
possible stopped outcomes. The [profile contract](../spec/profiles/compiler/finite-phases.md#table-trace-application)
states this bounded application precisely. It is an invocation-local trace
discipline, not participant projection or a challenge-distribution theorem.
The checker does not infer the entry phase from persistent provider state.
An admitted run may stop after a send, and its residual state is retained.
Re-admission starts a new abstract trace at `ready`; it does not establish that
continuing the same external protocol session is permitted.

`Examples.TableProtocol.Admission.summaryLaws` proves the summaries for every
operation argument and typed reply. `Tests.TableAdmission` instantiates the
actual region-artifact call and return theorems under that law. The installed
Lean tool checks preservation and the certificate against the same decoded
source; tree sources use their compact embedding.

```sh
target/release/zkc run examples/tables/source.json /tmp/table-plan.json \
  examples/tables/inputs.json formal/.lake/build/bin/table-protocol \
  --phase table-round/1 examples/tables/phase-certificate.json
```

The Rust `CheckRequest` borrows the original source, candidate and optional
`PhaseEvidence`. `AdmittedProgram` owns all those bytes and the consumer-selected
profile after success. Failed admission returns them along with a typed checker
failure. Binding, reservation and provider execution happen later. The phase
profile cannot be selected by candidate metadata or certificate annotations.

`zkc-tools::LeanChecker` maps the request to `check` or `admit`, copies the exact
inputs into private files, and requires the whole installed response and exit
status. Phase requests additionally require the selected profile in the success
response. An omitted or different profile cannot downgrade such a request to
preservation-only checking. Timeout, I/O/process failure, malformed response,
unsupported policy, unresolved requirements and failure to establish the check
remain distinguishable. None is reported as a proved semantic refutation.
The runtime API retains the tool's refusal code in `CheckFailure`; the CLI
reports its stable category, except for the preserved `unchecked-plan` and
`phase-not-admitted` codes. Its certificate prefilter bounds syntax at depth 512;
the installed table decoder separately enforces its policy's depth limit of 256.

Running without `--phase` deliberately requests only the existing preservation
check. Independent C++ family installation and dependent native replies are now
implemented in the [library unit](libraries.md). Stateful admission is described
below. [Checked interpolation](targets.md#checked-logical-folding) supplies one
changed-candidate rule; arbitrary optimizations need additional rules.

## Stateful table admission

The `table-endpoint/1` consumer now binds the initial phase to owned runtime
state. Its [profile contract](../spec/profiles/compiler/finite-phases.md#stateful-table-application)
uses role `prover` and normal returns at `ready`. The state envelope is
`[role, phase, tableState]`; the table state retains its existing five fields.
The [runnable endpoint example](../../examples/endpoint/README.md) exercises
both carriers.

`PhaseEvidence.entry` optionally records the consumer's `[role, phase]`.
The CLI's `--endpoint` mode derives it from installed bindings; the Lean tool's
`admit-entry` mode decodes it and checks from that phase. `LeanChecker` requires
its exact canonical acknowledgment as well as source-relative preservation and
phase admission. It cannot treat a trace-only response as endpoint admission.
The acknowledgment is part of the trusted tool protocol, not a proof object.

Rust checks agreement between source and requested role before checker dispatch.
The installed table checker resolves that role to `prover`; the adapter compares
it to its actual actor before loading private inputs. `Bindings::validate_entry`
runs again at reservation and execution entry. Stateful bindings require their
policy even when evidence is omitted. A failed final check reports `start-failed`
and preserves prior observations; `Completed::started()` distinguishes it from
an interrupted invocation. Consumers with shared external provider state must
supply their own synchronization and correspondence contract.

The table adapter records phase at each provider call and sets it to unknown
before possible effects. A noncopyable completion token carries that call and
its entry phase; consuming it after a logical completion restores the proper
phase. Dropping it on error/unwind leaves unknown without recovery code. Logical
stops retain the call's entry phase. Errors between completed calls keep the
last known phase. A composite adapter control distinguishes these cases at the
second call; phase tracking is not tied to source-operation count.

`Examples.TableProtocol.Endpoint` wraps the existing `ExecutionPath.handler`.
Its entry validation supplies actual initial coverage, and its erasure theorem
preserves ordinary outcomes, data state and events. `Tests.EndpointAdmission`
instantiates artifact call/return permission from a retained `sent` state.
The generic phase semantics and checker proof are unchanged. These results do
not establish the full `PIR.Admitted` judgment: public bounds, a frontend instance,
participant projection and native correspondence proofs remain separate.

`Tools.SourceConsumer` shares tree/compact decoding, source-relative checking,
input binding and execution reporting between the table and independent vector
service. Its entry callback receives the actual context role. The consumer
retains policy and state codecs: the vector service has no phase policy.
The earlier scalar `SourcePlanExample` and `InteractiveRound` tools keep their
separate experimental schemas; they are not the native table consumer's driver.

The tested correspondence compares outcomes, final phase, logical data and
original events, with independent expected results. Native internal call audit
records are not exported or compared. Initial phase truthfulness, provider
behavior, parser/checker execution and native code remain explicit trust.
No automatic recovery or successful handoff at `sent` is supplied by this
bounded profile. Physical scalar admission is connected below and
[checked interpolation](targets.md#checked-logical-folding) admits a bounded
class of changed plans. General endpoint admission remains broader than this
phase boundary.

## Physical table admission

The native `table-physical-plan` path now consumes both installed policies.
The physical admission unit connects the same logical source certificate to the
submitted physical body, including lazy/materialized scalars and retained
endpoint state. It changes no PIR constructor, control grammar, phase policy or
candidate wire format.

The proof boundary is the **logical provider call inside physical execution**.
`prepare` publishes a scalar cell, and later reads interpret it in its owner.
Neither action is a send or draw. Assigning a phase transition to every coarse
physical operation would count the wrong events and constrain future expansion.

[`TablePhysical.Checked.correct`](../../formal/Examples/TablePhysical/Checking.lean)
now quantifies over any logical handler, state and event types. Instantiate it
with `ExecutionPath.handler interaction logicalHandler`: the physical interpreter
then records the actual logical call and its entry phase before invoking that
handler. [`TablePhysical.Admission`](../../formal/Examples/TablePhysical/Admission.lean)
derives three results for the independently decoded candidate:

| Result | What it establishes |
|---|---|
| `audit_correct` | Complete instrumented outcomes, logical state and ordered events correspond, with final-store value meaning and the old-alias frame |
| `calls_permitted` | Source certificate acceptance plus actual initial coverage implies every logical provider call made by physical execution is enabled |
| `return_permitted` | A normally returning physical execution ends in the checked returning-phase cover |

This uses the existing all-typed-reply `summaryLaws`, not equality of ordinary
trace observations under one honest handler. For example, a false send reply
still advances to `sent`. A stopped draw retains `sent` and any provider effects;
it does not establish a normal-return postcondition. The tests also instantiate
a handler whose stopped draw changes state and emits an event.

Both Lean tools use `Tools.TableAdmission` to resolve the consumer's policy and
check the same logical source. Physical success additionally acknowledges
`table-physical-plan`; an endpoint request also requires its exact entry.
The historical reference-only profile cannot acquire native phase authority.

Rust wraps the existing `TableBindings` owner in `PhysicalTableBindings` and
delegates entry checks at binding, reservation and execution. The existing
actual-call completion token controls phase. A deferred read fault before a
provider call retains the known phase; a host fault during that call leaves it
unknown. Final output decoding retains the completion owner and prior effects.
No extra physical phase machine or provider reset is introduced.

For the supplied table example, append
`--phase table-round/1 examples/tables/phase-certificate.json` to `run-physical`
before an optional trailing `--storage packed` or `--storage segmented`.
An endpoint uses `--endpoint table-endpoint/1 CERTIFICATE` with the existing
`[role, phase, tableState]` input envelope. The CLI derives entry evidence from
that state; it cannot consume a previous ready receipt after stopping in sent.

The complete Lean/native comparisons include independent expected outcomes,
final phase, provider state, events and evaluation counts. They supply finite
native correspondence evidence. The proof concerns the physical Lean interpreter
with logical contracts; Rust kernels, allocator, provider, parser and compiled
checker execution retain their stated trust. This is local phase admission,
not complete endpoint projection, cryptographic security or native verification.
