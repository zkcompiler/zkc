# Bound subjects and artifacts

Evidence concerns a particular subject under particular meanings and premises.
An artifact carries that subject across proposal, checking and execution.
Its representation must retain the distinctions on which the evidence depends.

## Consumer-selected subject

The consumer's request fixes a source and the context in which the requested
judgment is to hold. That context includes the ordered input declarations,
result, role, interpretation dependencies and selected claim. A candidate is
a proposed realization of this retained source. A producer's independently
valid alternative source does not establish the requested judgment.

Admission and execution MUST bind the same source, candidate and meanings used
by the applicable law. Invocation additionally binds the actual input
environment and initial state. A universally quantified preservation theorem
can apply to many environments; each invocation still uses one actual
[binding](../profiles/source/named-inputs.md#exact-ordered-binding).

The [direct profile](../profiles/compiler/direct-plan.md#checked-plans) gives a concrete
source-indexed checked record. Other profiles may use different representations
of evidence, provided they establish the specified judgment about the actual
retained operands.

## Interpretation closure

The interpretation closure of a claim is the collection of semantic operands
and premises on which its proposition or use depends. It includes the relevant
domain, operation meanings and laws, module/source meaning, input binding,
interface versions, observer, relation and assumptions. Dependencies are
selected by their role in that claim, not by proximity in the repository.

A consumer using a name or revision reference MUST resolve it to the actual
meaning required by the claim under its installed policy. Equality of strings
or digests establishes an identity comparison under its own assumptions; it
does not prove that the resolved implementation satisfies the required laws.
Unused definitions and purely editorial changes do not invalidate a proposition
solely because they share a file or package with its dependencies.

*Example (informative).* The direct lowering theorem compares executions under the same
interpretation. This quantification supplies preservation for any shared
interpretation. It does not resolve a provider name or establish that two
different installed libraries implement that shared interpretation.

## Identity purposes

An identity is used within a contract that gives its comparisons meaning:

| Purpose | Subject and validity conditions |
|---|---|
| Source and capture identity | Immutable source meaning and actual ordered captured values |
| Runtime identity | A live object in a particular world and lifetime, including ownership or generation when required |
| Preparation identity | The complete immutable dependency meaning of a reusable value |
| Probability provenance | Joint initialization and the subsequent permitted state transitions |
| Continuation authority | A live installed policy and ledger entry with its custody conditions |

One identifier may serve several interfaces only when each interface's laws
are established for its actual referent and lifetime.

## Premise-preserving reuse

Suppose evidence establishes `P x` under premises `A x`. Reusing that evidence
for subject `y` requires the actual `A y` and a transport law that establishes
`P y` from the available result, or rechecking `P y`. Byte or name equality is
sufficient only where a proved or installed interpretation law gives it that
role.

Changes to captures, domains, guards, effect summaries, challenge prefixes,
observers or terminal targets require rechecking the affected premises or an
applicable frame, equivalence or rebinding law. A mutable read follows its
declared transition. It cannot masquerade as an immutable capture while
rereading changed storage.

The [immutable cache contract](../core/contracts.md#immutable-cache-validity)
can justify reuse beyond the lifetime of a mutable fact when the cache's own
provider and dependency law remains valid. Rebinding a provider requires its
agreement on the actual occupied entries; agreement at an unrelated test key
does not establish that condition.

## Specialization and retained configuration

Specialization may select a different consumer for each configuration `b`.
The existence of suitable `consumer_b` for every `b` does not imply that one
consumer works after `b` is erased:

```text
(∀ b, ∃ consumer, correct b consumer)
  does not imply
(∃ consumer, ∀ b, correct b consumer).
```

The actual selected configuration and its premises therefore remain available
where correctness needs them: in specialized code, symbol selection, captures,
an artifact or a validated execution environment. The contract does not require
per-value metadata or a global configuration registry. Configuration can be
erased when the remaining consumers are independent of it or an applicable
transport law establishes their required behavior from what remains.

Reusing specialized code under a changed configuration requires the affected
premises for that actual configuration and an applicable rebinding law or a
new check. The [input coverage](../verification/refinement.md#advertised-input-coverage)
claim continues to describe the advertised source domain. Whether specialization
reveals information through its code or artifacts is a separate release
obligation, even when execution refinement holds.

## Lifecycle and release

An open candidate can retain unresolved choices, requirements or evidence.
Admission means that a specified judgment is usable at its stated scope.
A sealed artifact fixes a selected subject, interpretations, interface
versions and evidence or trust references for reproducible use. A concrete
sealing mechanism supplies its retention and resolution contract; these terms
alone define no cryptographic sealing operation.

Lifecycle states do not change protocol meaning. Content authentication
identifies bytes under its stated assumptions. It does not establish semantic
correctness, secrecy, security or publication permission.

Source, code, proofs, receipts, digests and diagnostics exposed to an observer
form part of the [permitted release](../properties/disclosure.md). This includes values
revealed through secret-dependent specialization. Admission to execute a
candidate is not by itself admission to publish every artifact of its creation.

## Artifact envelopes

An executable artifact profile distinguishes:

| Field class | Interpretation |
|---|---|
| Format and semantic versions | How to decode the artifact and interpret its constructs |
| Mandatory capabilities | Additional facilities required to admit or use it |
| Realization, rule and claim | What is executed, which checking rule applies, and which proposition is established |
| Source and context | The consumer-retained subject and its declared dependencies |
| Final plan or executable content | The exact proposed object to which checking applies |
| Evidence requirements | Premises still requiring an allowed disposition |

Semantic operands, checked evidence, optional proposal hints and editorial or
cost metadata have distinct roles. Each profile defines their fields or
omits the unused classes explicitly. Unknown mandatory facilities or unresolved
required meanings fail admission. Missing optional hints can prevent an
optimization; missing effect information cannot default to purity.

Extending a logical-plan claim to generated native code requires a realization
definition, a checking rule and the corresponding realization laws. The
[direct envelope](../profiles/compiler/direct-plan.md#envelope-grammar) fixes one
concrete instance of these distinctions.

## Exact retained content

Each profile fixes constructor interpretation, field order and arity, natural
and value encodings, and input-consumption policy. It rejects duplicate
declarations, unknown mandatory constructors and invalid references. Decoder
capacity refusal remains separate from mathematical ill-formedness, as in the
[codec boundary](codecs.md#input-boundaries-and-capacity).

Admission MUST retain or otherwise securely bind the exact checked content
used for execution. It can retain immutable decoded structures when the claim
concerns those structures, or bytes with an established decoding and retention
law. Reopening a mutable file by the same pathname does not establish that the
second read is the checked object. Canonical content identity additionally
requires a specified byte-level serialization rule.

## Requirement disposition

Every premise needed by an admitted conclusion has an allowed disposition:
checked evidence, explicitly installed trust, or an applicable dynamic guard
at the source point where it establishes the required fact. The selected
[conditional judgment](../verification/judgments.md#conditional-evidence)
retains any premise still required for use.

Permitting a requirement name is an authorization choice, not evidence for the
requirement. A dynamic value check establishes its actual checked predicate;
it cannot establish a provider distribution law. Unsupported evidence may
remain available for inspection without constructing an admitted executable.

The consumer states its checker-process, response and build assumptions
separately from kernel replay of a proof. A successful executable response is
interpreted through that process contract. It is not automatically a separately
replayed proof object. The direct profile accepts no introduced requirement,
including one its request lists as permitted.
