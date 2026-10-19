# PIR semantics

These semantics define the typed mathematics, participants, effects,
observations and refinement shared by every imported model. Admission and
process equations concern the imported Lean constructors; the
[bridges](../../bridges/common/README.md) test their agreement with native
execution, and [formal support](../support.md) records the scope of each claim.

## Local structured computations

`Source.Dialect` declares operand types, ordered result types and closed region
input/output signatures. `Region` binds ordered result tuples before the retained
caller context. The empty result list is valid and does not remove an operation.
`bind` stores its continuation once. Region bodies see only declared inputs;
operation operands and contracts explicitly transmit captured values.

`RegionMeaning` interprets operations and effectful callbacks into `PIR.Proc`.
Its contracts determine callback execution and failure behavior. Pointwise process
equality lifts through nested bodies and shared suffixes. Translating effects
requires the explicit operation compatibility law in `RegionMeaning.Translation`.
`Region.Total` is a sufficient predicate over this same syntax: its per-operation
premises and callback premises prove immediate return without interactions or
stopping. Native memory annotations do not establish this property.

`Region.Derivation` constructs process correspondence from local operation laws
over this same typed body. Its indices fix the source region, environment,
effect interpretation and target process. Return, stop, lexical bind and
operation constructors cover the stored structure. Each callback is derived
for every declared input before an operation law may use its translated
meaning. Pure-return and stopped-prefix rules avoid obligations about unreachable
suffix executions; they do not remove those suffixes from source admission.
`Region.Derivation.sound` produces the whole process equation. There is no
constructor that accepts that equation as its sole premise.

An operation law can still be mathematically substantial: a call, fold or repeat
must use an appropriate helper theorem or invariant. The derivation does not
discover these proofs. Its execution corollaries use the handler
semantics and retain returned values, stop causes, residual state and ordered
events. Property-specific weakening, such as hiding events or bounding only
acceptance, requires an additional explicit theorem.

`RegionDecoding` checks reference indices, result annotations, intermediate bind
types and exact closed region signatures, including dormant bodies. Typed erasure
roundtrips for all regions; successful formation preserves all raw structure.
Each import profile supplies its own operation resolution.
The single-result `Source.Program` is an independent reference
profile with the exact bridge `Program.denote_toRegion`. The participant profile
and admitted scalar imports have the corresponding `Common` bridges, retaining
the final output-role restriction as well as all actions and stops.
`Common.ParticipantOp` and its dialect are indexed by the selected participant.
A region lowered for one participant cannot be interpreted by another
participant's meaning without an explicit change of representation.
Structured protocol roots instead use a role-agnostic dialect: role indices are
resolved within each root, and the meaning receives the chosen participant.
Closed helper dialects have no protocol effects, and roots never enter helper
closure tables.

The [structured native profile](structured-source.md) resolves an actual export
into this same `Region` carrier. Its operation family owns signatures and
meanings; named helpers retain shared checked bodies, and ordinary control
passes closed callbacks. Provenance stays in the admitted snapshot instead of
being inferred from process equality.

`Region.component` is a second interpretation of that same typed body. It changes
each value to `Option Value`; operation arguments and results are optional tuples,
while nested callbacks retain the original nonoptional `RegionFunction` type and
meaning. `strictComponent` sequences all operands and delegates present inputs to
the original operation. Missing operands produce absent results without running
that operation. A zero-result operation still runs when its operands are present;
an explicit `Region.stop` always stops. Named calls can instead pass optional
tuples directly to a component closure.

`ComponentOperations.Adequate` requires agreement with the original operation on
every present argument tuple and every closed callback tuple. Under precisely
this premise, `Region.component_present` proves equality with the complete
original process followed by marking returned values present. The proof covers
lexical binds and nested regions, preserves interactions and stops, and assumes
neither totality nor static availability. It is a change of value assignment;
the effect translation in `RegionInterpretation` alone does not supply it.

`Region.denote_congr` and `Regions.denote_congr` lift agreement on the stored
operation inventory to equality of nonoptional meanings. `Region.component_congr`
requires both nonoptional and component operation agreement on that inventory,
because callbacks use the nonoptional meaning. The inventory includes dormant
callbacks and stopped suffixes. These laws provide no availability admission:
an absent unused intermediate can coexist with a present returned component.

`Source.Finite` defines ordered domain admission and open folds as semantic
helpers. Admission runs before iteration, even when a loop is empty or a domain
is otherwise unused. Zip checks both factors before their lengths; product checks
both factors even for an empty outer list. Its replacement laws preserve the
first stop and retain admission around any pure mathematical equation.

## Mathematical and participant layers

A `Language` has sorts and typed operations. A mathematical `Meaning` assigns a
Lean type to each sort and an interpretation to every operation. Group operations
can be interpreted in a module over a field; different native nominal domains
must not be silently equated. The scalar proof-request profile checks domain
assignments explicitly because its chosen field/group interpretation is uniform.

A source context indexes the type of every reference. Elaboration constructs a
well-typed program or refuses it. Values available to participants are optional:
absence is not zero, false, or a default group element. Inputs carry role scopes;
projection preserves restrictions, sender/receiver actions and service ownership.
Inputs shared by two roles may have different role-local values. The semantic
model never derives agreement merely from their shared source port name.

## Effects and observations

`Source.Participant` owns the role/type-parametric action interface and the
shared open rules used by both `Common.Program.denote` and
`Common.participantMeaning`, and by structured roots. Their callers compose returned components with the
remaining program; shared rules preserve the actual action continuations.

- `exchange` stops `incomplete` when the sender lacks its operand. Otherwise it
  sends that value and returns the same sender component. At the receiver it
  consumes an independent actual reply, regardless of the local operand. Other
  roles return an absent component. Sender precedence also defines coincident
  endpoints, although Common admission rejects them.
- `query` requires every ordered argument only at its owner. Missing owned
  arguments stop `incomplete`; a successful call returns the actual reply at the
  service's exact declared result type. Other roles return an absent component
  without querying. A service tag does not select a sampling distribution.
- `guard` takes an optional Boolean. At its owner, absence stops `incomplete`,
  false stops `reject`, and true continues. Other roles continue without an
  action or stop. Common supplies its mathematical condition policy by mapping
  the local condition into this Boolean boundary.
- `owned` sequences all arguments only at its owner and runs closed work even
  with zero results. Missing owned arguments stop `incomplete`; nonowners skip
  the work. Stopping and callbacks remain those of the supplied closed process.
- `restrict` retains a selected optional component or hides it. It cannot create
  an absent component and emits no action or stop. Common uses the same rule for
  lowered restrictions and the imported program's final output-role filter.

Participant contracts and handlers name `Participant.Action` and
`Participant.interface` directly. Mathematical value meanings and service
behavior remain separate parameters. These rules define no joint scheduler,
honest-peer equality or randomness assumption.

`Source.PeerExecution` is a separate handler for honest delivery between two
endpoints of one invocation. `peerHandler self other service` keeps the other
endpoint's actual residual process in its state: a receive of `self` takes the
value of that process's next send when type, site and endpoints match; a send
of `self` is consumed by that process's next matching receive; queries of
`self` go to `service`. Every mismatch refuses without inventing a reply, and
the peer may not query a service of its own. It models no loss, reordering or
adversarial network and is not a scheduler for more than two endpoints.

`PIR.Proc` is a well-founded interaction tree with returned values, terminal stops and
typed requests whose continuations consume actual replies. A handler maps an
operation and state to its outcome, successor state and ordered events. `run`
threads that state. `runM` does the same in a lawful monad, enabling VCVio
probabilistic handlers. Rejection, refusal, incompleteness and a returned false
Boolean remain distinct. A statement annotation has no runtime proof effect.

The optional `ZkcSecurity.VCVio.Execution` module supplies full-distribution
and reachable-prefix composition for this same `runM`/`followM`, including
value-returning trusted work and conservative Boolean checker laws. It compares
complete output records, not reply marginals. Its support transfer relies on
VCVio's pinned uniform-oracle semantics; the core is independent of that
package. See the [causal security contracts](multilinear-sumcheck-security.md#local-distribution-and-computed-value-contracts)
for an actual structured-operation example.

`ExactRefinement p q` contains equality of their open processes. Its laws preserve
all handlers, replies, stops, final states and events, and compose under bind.
This is intentionally stronger than final-result agreement. It can reject an
optimization that changes observable actions even when outputs coincide. Such a
case needs a separately stated observation/refinement interface and proof.
Process equality does not preserve static source admission, relation annotations
or artifact identity: those are not runtime interactions. A transformation
certificate must bind both actual subjects and establish their required static
contracts separately from its dynamic equation.

## Observation budgets and unbounded behavior

`Machine` has explicit configurations, internal steps, requests and terminal
outcomes. `runFrom` returns a prefix whose progress is running or finished.
A zero/exhausted observation budget does not become protocol rejection. Resuming
for budgets `m` and `n` equals running for `m+n`; terminal states are stable and
prior events remain a prefix. A spin control stays running at every budget.

A `Proc` embeds in this machine. `complete_run` relates every observed
prefix to the full finite execution. `eventually_finishes` proves that every
fixed total handler reaches the same complete result at some finite budget.
It does not assert a uniform depth across all reply-dependent continuations or
a finite number of branches when the reply type is infinite.
The scalar profile admits finite straight-line bodies with bounded static
helper inlining, without general native loops or recursion.
A partial external-reply/waiting scheduler is not supplied by the total-handler
model; it requires a separately specified interface.
