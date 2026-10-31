# Interaction analysis and checking

An interaction analysis reads the actual admitted Protocol IR. It supplies a
shared structural view to scheduling, query-capacity and realization consumers;
it does not define another authored program. [Status](../../status.md) records
which analyses and comparison profiles implement this contract.

## Subject and structure

The subject fixes the module, selected declaration, nominal types, ordered ports,
roles and captures, and every inspected declaration, installation and policy.
The containing module owns cached analyses. Its inspected symbol dependency
closure is distinct from that containing operation. A function-local analysis
cannot inspect concurrently mutable sibling declarations.

The view preserves operations in source order, applications, symbolic repeats,
local control and participant-relative continuation. Operations and operand
uses refer to actual IR. Required semantics remain in typed operands, types and
inherent properties; locations and discardable attributes supply no premises.
The view may index or summarize the subject but cannot be edited independently.

A lexical source path, an application frame, a repeat iteration, an oracle
anchor, a physical handle and a transcript key are different identities. Equal
contents or an equal commitment root do not merge anchors. A coordinate does not
establish that its occurrence was reached. Call summaries preserve the ordered
substitution of inputs, outputs and captures and the selected role mapping.
Symbolic repetition retains multiplicity without enumerating every iteration.

## Separate judgments

Shared extraction does not give every consumer the same transfer or join rule:

| Judgment | Meaning and combination |
|---|---|
| Dependency | Conservative may-influence relation; alternative paths use union |
| Exact origin and custody | Actual resource identity and permitted ownership; possible roots are not interchangeable |
| Reached premise | An interpreted predicate of exact values on a successful continuation; joins retain only facts established on every continuing predecessor |
| Binding and authentication | Evidence for an exact scheme/context, encoding, root, position and answer; every relevant path supplies compatible evidence |
| Sampling and combination | The selected joint law and coefficient family, under their actual premises |

An absorbed value need not be authenticated. A computed verification Boolean
need not be a successful check. A bound on an extent is not its exact value.
Dependency on a value does not establish injective or collision-bounded binding.
No single provenance flag or interface membership establishes these judgments.

## Successful continuations

Reached facts supplement the [mathematical fact vocabulary](../domains/mathematical-facts.md).
A fact names its interpreted predicate, operands, role, successful point and
scope. A guard on one participant does not stop another participant's flow.
Unknown conditions retain every supported continuation. Unreachable states
remain distinct from reachable states with no established facts.

A fact established in only one branch cannot escape its join. Loop entry,
zero iterations and recurrence have separate obligations. A callee's formation
premises cannot discharge its caller's requirements by being assumed at the
call. A checked local body summary must supply the actual successful result
relation and any required caller premises.

Logical evidence can be reused. Affine consumption is imposed only by the
specific resource contract. Ordered admission, observation and failure actions
remain in the program even if analysis can derive a related mathematical fact.

The initial successful-point profile interprets unsigned `data.index_less`
followed by a reached `protocol.guard` owned by the observing participant. It
matches exact SSA operands, allowing exact role restrictions, the observing
participant's assembled component and invariant repeat captures. A constant
upper bound may weaken to a larger constant bound;
an unrelated shape bound may not stand in for an actual extent. Queries inspect
the prefix before their actual occurrence, not all guards in the declaration.
An enclosing prefix applies inside a repeat through invariant captures. A fact
from the body does not escape the repeat, and its carried initializer does not
describe later iterations. Uninterpreted local calls supply no new premises.
Known stopped prefixes are reported as unreachable, not as successful proofs
of arbitrary predicates. Other structured-control profiles require their own
checked continuation rule before they can supply successful-point evidence.

Exact scalar observation is shared by successful continuations, observation
ordering and query-capacity analysis. It distinguishes a named participant's
Boolean or unsigned integer from a uniform value: role assembly selects that
participant's actual component, whereas a uniform observation requires every
component to agree. Pure helper results and invariant captures may forward
constants; loop-carried initializers, loop results and formation premises do
not. A constant is not evidence that its definition or any later action ran.
No observation removes a guard, a count check or a possible stop.

Capacity may tighten a repeat's declared maximum using an exact uniform count
within that maximum. Unknown, differing participant components and out-of-range
values retain the conservative declared bound. Recurrence joins still include
the zero-trip alternative; this analysis does not assert honest completion or
equal execution budgets. All reads and recursive queries share the caller's
cumulative allowance, and exhausted work cannot supply a smaller bound.

## Source-relative comparison

A transformation fixes its comparison profile before proposing evidence. The
profile names original and candidate subjects, applicable model laws, property
direction, observation, stop relation and relevant resource or codec relation.
Raw execution correspondence, lawful deterministic refinement and cryptographic
reduction remain different relationships.

The checker derives obligations from the source and reads the actual candidate.
It may share neutral extraction with the producer but cannot accept the
producer's decisions as evidence. Every admitted target outcome is covered by
the selected relation, including decoding failures and stops. A conditional
reply law with no coverage is insufficient. A stop-permitting safety relation
does not establish successful honest execution.

Claims retain their relation instance, parameters, handles, coordinates and
values. A claim may have a gap between its Yes and No sides; preserving Yes
alone does not preserve No. Partial readbacks must be defined. A component may
export explicit residual obligations, but terminal acceptance closes all
source-required obligations under the selected assumptions. An ignored check,
missing claim or independently renamed anchor does not discharge one.

Application and realization records retain these associations under their own
schemas. This contract adds no universal certificate format or approval bit.
Formal consumers independently interpret the data; native consistency checks do
not establish a Lean theorem or cryptographic security bound.

## Lifetime and capacity

Borrowed views expire on mutation of the subject, inspected callees, relevant
layouts, roles, installations or policies. Direct APIs clear views during
mutation; pass-manager invalidation at the end of a pass is insufficient.
Candidates and clones have separate snapshots. Persisted associations identify
their exact subjects and are independently rechecked after changes.

Extraction and queries debit the declared cumulative analysis allowance,
including nested calls and repetition summaries. Caching supplies no additional
allowance. Unrepresentable counts and exhausted analysis refuse the required
judgment; they do not add a source precondition or an execution stop. Compiler
analysis capacity, runtime resources and adversary query budgets remain separate.

Standard MLIR analysis and control interfaces apply only with truthful transfer
and successor models. A mandatory analysis must enforce its work contract even
when an upstream solver has no budget option. Unsupported, Unknown and Capacity
cannot be interpreted as successful security judgments or trigger a weaker
compatibility checker.
