# Logical calls and connected outputs

Calls preserve complete returned/stopped behavior and distinguish reusable bodies
from their selected instances. The native interactive route uses `func.func`
local algorithms, `pir.local_call`, `pir.protocol_call` and, after projection,
`pir.participant_call`. Their structured execution propagates stops without an
explicit pair of MLIR successor blocks at each call. See the
[protocol pipeline](protocol-pipeline.md) for the implemented path.

This chapter develops the call and connection obligations and compares an
explicit-successor representation as a possible lower-level choice. Its
`invoke … returned … stopped …` syntax is an illustrative alternative, not a
registered operation. It adds no normative semantic layer.

The [resolved definition profile](../spec/profiles/source/definitions.md)
supplies maintained Lean source bodies, typed references and complete call
execution. Its inlining theorem renames both value captures and definition
references. The actual Sumcheck verifier is a client with a complete-execution
equality to its staged source. This establishes the stored-body connection in
that profile; it does not prove the native resolver or common-source projector.

The [located-call profile](../spec/profiles/source/located-execution.md)
fixes role-state lifting, diagnostic stop origins and actual guard/count
agreement. Its local-effect policy checks the actual interpreted callee with
the existing all-reply conformance judgment. A function signature or role
attribute does not make a body with receives into a local algorithm; the
positive-round Sumcheck source is a maintained negative control for that claim.
Supplied endpoints and protocol definitions may contain that communication.

The native verifier must therefore distinguish a local algorithm call from a
protocol invocation, resolve the callee's effect contract, and retain explicit
communication at the common-source boundary. A conservative refusal is appropriate
when that contract is unavailable. Per-role result ports must still come from
the declared signature rather than all values available at the role.

The role-state frame law also does not authorize hoisting a call past another
role's stopping action: the complete prefix and peer state can change. Preserve
the selected call boundary, stop behavior and observations when defining native
effects and speculation. This is the concrete use of
[MLIR's effects/speculation distinction](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
at the call boundary.

## 1. Callable bodies and binding

Use isolated local function bodies, explicit arguments and symbol references.
A local function interface does not by itself supply the role and communication
rules of a common protocol or independent participant. Keep those containers'
additional invariants explicit rather than deriving locality from `func.func`.

| Call form | Environment used | Refused ambiguity |
|---|---|---|
| Template call | The caller's selected environment | Calling a bound instance as though it were an unbound body |
| Selected-instance call | The callee's own declared environment | Treating an unbound template as an already selected instance |
| Concrete primitive call | The named contracted primitive, independent of the abstract slot | Omitting that direct dependency from the selected execution |
| Resolved call | The actual specialized body or contracted primitive | Leaving an abstract operation unresolved for execution |

An interactive caller can therefore invoke a separately selected construction
without rebinding it. Two independent Fresh tapes are a useful test of
scope and residual-state separation, but not a test of Fiat–Shamir security.
Resolution determines static code. It neither resets runtime state nor assigns
a new meaning to the original statement. Keep captures, actual residuals and
runtime resources distinct from the specialization key.

The maintained definition table uses a typed dependency order. Production MLIR
keeps named symbols and explicit call operands; a checked resolver supplies the
map between them. Declaration order need not be dependency order, and a local
formal reference index must not become a transcript or invocation identity.
This follows the distinction between lexical value capture and
[MLIR symbol references](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/).

Earlier choreography research remains relevant at the boundary: Pirouette
separates local computation from distributed functions and treats substitution
explicitly. Here, typed operands and definition references use separate
renamings, with a proved interpretation law. This application does not import
Pirouette's projection or deadlock theorem, nor does it allow local value typing
to stand in for global branch agreement.
See [the technical report, §§2.3–3](https://www.mpi-sws.org/tr/2021-004.pdf).

A one-slot scalar callback model cannot establish correctness for multiple
dependent bindings. Production binding must retain each typed operation contract
and inspectable construction. Direct primitive references are additional static
dependencies; a caller's binding attribute does not describe its entire execution.
Environment-independent helpers can remain shared.

## 2. Returned and stopped control

The following alternative makes successful-value availability structural:

```text
invoke @reduce(flow, original_claim)
  returned ^terminal(next_flow, residual_value, actual_point)
  stopped  ^exit(next_flow, reason)

^terminal(flow, value, point):
  accepted = check_original_polynomial(original_polynomial, point, value)
  return flow, accepted

^exit(flow, reason):
  stop flow, reason
```

The invoke produces its successor arguments. It has no unconditional SSA result
for a successful value. The stopped successor therefore cannot access that
value, and several calls can share one stop continuation. MLIR's
[branch interface](https://mlir.llvm.org/docs/Interfaces/) supports produced
successor arguments. An implementation of this alternative would also need a
symbol verifier relating their types to the callee's successful results and stop ABI.

Three distinctions matter in real clients:

- A verifier returning `false` completed its computation. The caller decides
  how to use that Boolean; it is not an outer stopped outcome.
- A service returning only the first part of a response completed a declared
  partial-response operation. The absent fields are unavailable, not fabricated
  values and not an exhausted provider.
- A controller's ordinary service-stop operation can return normally after
  updating its history. A provider exhausting its tape instead stops execution.

Successor separation alone does not enforce propagation. The proposed successor
form must require a stopped continuation to propagate the same reason and actual
flow immediately; it cannot resume or replace that reason. This implements the
existing [execution sequencing law](../spec/core/execution.md). A physical
cleanup path may later release resources, but it needs its own realization law
preserving the selected stop, state relation and observations. It is not an
implicit recovery rule in logical PIR.

Use an opaque ordering value, interpreted separately from the hidden world.
Participants cannot inspect provider state merely because an execution model
contains it. Check that every path forwards the current block's flow and every
call continuation receives its new flow. Forwarding to mutually exclusive
branches is legal; a global single-use count would reject useful control flow.
An order stamp can detect stale flow in a test model, but it is not the semantic
runtime state representation.

## 3. Connections and local information

Successful function return does not discharge a connected relation. In the
Sumcheck client, the reduction returns its actual scalar and point. The terminal
consumer checks them against the original polynomial retained by the caller.
Changing that original or the point is structurally valid MLIR and changes
Lean-relative outcomes. Consequently, the compiler must retain the selected
source and its actual operand mapping when checking a candidate.

The [component relation](../spec/properties/relations.md#component-connections)
also applies when two protocols expose differently shaped boundaries. The
caller supplies the actual connector and values; a generic call graph does not
establish them. Executing two verifier components and exporting their Booleans
can test binding scope; it does not establish cryptographic conjunction or
protocol security composition.

Keep participant-local inputs explicit. Native admission must check actual
input/capture mapping, supported local operations and the selected endpoint's
contract. A role attribute or a function signature alone cannot establish
availability or noninterference. In particular, a structurally valid call graph
can still request an operation after a service has stopped, or call a primitive
not enabled for its participant. Phase admission and operation contracts must
rule these out at their own boundaries; an ad hoc runtime stop guard is no proof
of conformance. Typed native representations must also enforce canonical field
values rather than relying on a fixture to supply reduced codes.

Fixed partial/full response operations can have different successful signatures.
For a runtime-dependent response shape, retain a checked branch or a typed
variant until the shape is known. Do not make every protocol pay for one maximal
tuple, and do not erase the dependency before its consumer has handled it.
A fixed partial-then-full sequence does not test arbitrary reply-dependent
shape selection. Such a claim needs an adaptive source and the corresponding
request-dependent reply checks.

## 4. Optimization and lowering

Use call and control-flow interfaces where their contracts match the actual
operations. They expose structure, not permission for every generic rewrite.
An explicit-successor terminator call would require a dedicated inlining rule
or conversion to a tagged-outcome carrier before ordinary function inlining.
Either approach must map successful exits, propagate stopped exits, and preserve
role context, captures and ordering. Adding a dialect legality hook alone would
not supply those mappings. Current acyclic helper expansion is documented in
[local composition](local-composition.md).

Ordered calls need conservative effects and no unjustified speculation.
Eligible pure arithmetic may still be optimized. Finer effects require sound
summaries and a reordering law for the selected observer, as distinguished by
MLIR's [effects and speculation model](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/).

Lowered arithmetic children do not replace high-level polynomial, commitment, transcript or
domain operations. Those operations remain inspectable until a transformation
needs their expansion. Binding construction and lowering arithmetic are separate
axes. The [selective-lowering discussion](lowering.md) describes local expansion and
source-relative evidence without choosing the physical-plan/OIR carrier.

## 5. Semantic basis and assurance

| Basis | Concrete use | Remaining connection |
|---|---|---|
| [Execution](../../formal/Zkc/Semantics/Execution.lean) | Returned/stopped sequencing, actual post-state and event prefix | General proof of native control translation |
| [Interpretation](../../formal/Zkc/Semantics/Interpretation.lean) | Selected environments and sequencing through residual state | Native substitution/export adequacy for multiple dependent operation slots |
| [Sumcheck connection](../../formal/Zkc/Protocols/Sumcheck/Connection.lean) | Actual reduction outputs and original terminal subject | Actual cryptographic PCS contract and the selected terminal consumer |
| [Correlated source](../../formal/Zkc/Protocols/CorrelatedSetup/Source.lean) | Adaptive continuation and response-dependent availability | Coverage beyond the selected native ownership and control checks |
| [Connected relations](../../formal/Zkc/Semantics/RelationComposition.lean) | Distinguish computational calls from boundary predicates | Native contextual replacement checking with actual premise producers |
| [Refinement](../spec/verification/refinement.md) | Compare selected outcome, state and observations to the retained source | Complete native implementation verification |

Evidence must refer to the actual retained source, candidate and observer.
[Original-source validation](library-design/validation.md),
[interactive execution](interactive-execution.md) and the
[finite table checker](phase-admission.md) document the maintained native joins
and their limits. They do not prove an unimplemented successor-call design.

An output adapter must state what it observes. For example, projecting a service's
last response requires a law that a following ordinary service-stop event leaves
that projection unchanged. Matching an incidental serialization is insufficient.

## 6. Integrated admission responsibilities

The driver composes the following results for the same retained entry. Their
separate producers make a missing obligation visible without introducing a
universal admission theorem or treating an MLIR verifier flag as authority.

| Obligation | Producer and consumer | Required negative control |
|---|---|---|
| Syntax, types, references and dormant declarations | Native decoder/MLIR verifier; closed source resolver | Unsupported dormant helper, wrong arity, unresolved slot |
| Actual inputs and role-local access | Entry binding/locality checker; invocation admission | Swapped captures, missing private input, wrong participant |
| Enabled calls and returning phases | Interpreted operation summaries and phase evidence; source admission | Request after service stop, wrong-role primitive, incomplete reply cover |
| Request/result legality | Family signature/shape validator; checked unpack at each dynamic call | Wrong vector length, noncanonical intermediate field value, wrong slot |
| Complete state/effect behavior | Selected operation contract and target adapter; transformations and runtime | Refusal after write, hidden alias, reset provider |
| Actual candidate preservation | Consumer-selected checker; immutable artifact admission | Changed source or candidate, wrong relation/observer, stale premise |
| Installed assumptions and progress | Consumer deployment policy and invocation guards | Unsupported provider law, exceeded capacity, arithmetic overflow |

`PhaseAdmission.checkRegion` handles shared binding directly; tree programs
reuse it through `toRegion`. Its law quantifies over every typed input and reply
covered by the selected policy. It does not establish locality, canonical native
representation or backend correctness. Native integration has a
[table trace consumer](phase-admission.md#native-table-admission) and a
[stateful local phase consumer](phase-admission.md#stateful-table-admission).
The latter binds the actual recorded entry to its phase check. General
participant ownership, projection and the complete endpoint admission judgment
remain broader obligations; the fixed-prover application does not close them.

The maintained `RegionArtifact.Checked.phase_sound`, `calls_permitted` and
`return_permitted` join certificates to the exact decoded source/candidate
region. Actual artifact tests instantiate both permission theorems. For native
consumption, a typed check request carries source, candidate and phase evidence;
the consumer selects the policy/entry/allowed covers. Retain the evidence bytes
or a policy-authorized bound receipt with the admitted object. A phase
certificate is evidence to check, not a `DefinitionRef` assumption to trust.

Operation slots are statically resolved but need not share a signature. A
request can determine a successful reply's shape: represent the dynamic result
as a family-defined tagged value, validate it against the actual request, and
expose the checked dimensions/shape witness before typed consumers use it.
Fixed-shape specialization is an optimization, not the only calling convention.
Refusal/unavailability replies preserve actual state and events under the
operation's complete-result contract. Reply legality alone is not a frame law.

The [closed library/reply implementation](libraries.md) exercises vector and
Boolean operations with different signatures and request-dependent constraints,
alongside the table client. Integration probes supplied the semantic boundary;
the independent service consumer tests its native join.
Arbitrary open slot-environment resolution is still not implemented.

The C++ resolver separates family signature/type decoding, descriptor resolution
and semantic export from the fixed table vocabulary. It selects loaded consumer
models under the closed entry's exact dependencies; unknown or ambiguous models
refuse. Colliding local operation spellings do not identify their meaning.
Static slot resolution belongs to the compiler environment. Runtime bindings
supply the resolved provider implementation and actual state through that
family's library adapter; no universal runtime dictionary is required initially.
Malformed backend replies are classified by the selected operation/codec
contract. They are not automatically turned into a new logical protocol stop.
