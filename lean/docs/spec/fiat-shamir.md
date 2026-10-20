# Fiat–Shamir transcript construction

This chapter defines the formal check of the compiler's native
[transcript construction](../../../docs/spec/ir/construction.md) for a role-local
validator, the transform theorems it supports for the compiled proof Entries of
the Schnorr, Sumcheck, composed Sumcheck, Sigma and GKR examples and of a
guessing fixture, and the security theorem for the Schnorr Entry; the security
theorems of the compiled Sumcheck, GKR and guessing Entries are in
[multi-round Fiat–Shamir security](fiat-shamir-security.md). The native [export](../../../docs/spec/formats/constructed-participant.md)
supplies the checked candidate's validator; the
[structured import](structured-source.md) supplies the original program.

## Transform of a validator

`Zkc.Construction.transform` is the Fiat–Shamir transform of a validator
process over the common participant actions whose every query is a selected
challenge, for a challenge function
`challenge : History F G → m F` in any monad. A history is the ordered list of
absorbed events: the host's `binding` of the public context and scalar values,
a typed public-value binding event (`publicBinding`, [binding codecs](fiat-shamir-security.md#binding-codecs)),
a `message` with its occurrence origin and typed payload, or a `challenge`
occurrence.

- A receive reads the next proof message, decodes it at the expected type and
  nominal domain, and absorbs it. Decoding failure or an exhausted proof stops
  with `refused` and consumes nothing.
- A query is answered by `challenge` on the history followed by the query's
  occurrence, which is then absorbed.
- A send is absorbed with its message occurrence and produces no proof data.

The result is the validator's outcome and the unread proof suffix. The
transform is the core transcript transform (`Zkc.Transcript.transform`) at the
context's transcript interface (`Context.interface`), in which every query's raw
answer is a field element decoded as itself and the challenge function is asked
at the history followed by the occurrence (`transform_eq_transcript`); the
equations for each operation (`transform_eq_done`, `transform_eq_halt`,
`transform_eq_receive`, `transform_eq_query`, `transform_eq_send`) unfold it.
The [typed engine](fiat-shamir-security.md#typed-query-sites) states its
security over the same core interface. Occurrence
origins come from a `Context`: original entry, role roster, producer and
validator positions, the replaced service's original input index and contract,
and the policy's ordered query/delivery sites. An origin names an occurrence by
its qualified site; the native
[occurrence encoding](../../../docs/spec/ir/construction.md#native-occurrence-encoding)
additionally carries the application and repeat path and, inside loops, the
iteration coordinates. The bridge decodes and re-encodes each exported template
exactly.

## Constructed programs

`Zkc.Construction.Participant` carries the exported validator: decoded policy,
sorted inputs and outputs, instructions with scoped operand references and result
sorts, and returned references. Instructions are receives, sends, coordinate
constructions (`indices.empty`, `indices.append`), transcript observations and
challenges with their suites and decoded occurrence templates, calculations of
the structured vocabulary, calls of the original program's helpers by name,
guards, loops with their bodies, and unsupported operations retained by name.
Values are structured data (Booleans, field and group elements, indices and
field vectors), transcript histories and coordinates.

A template keeps the native path (application and repeat steps) and event. Its
model occurrence, the origin the transform absorbs, names a message by its
qualified site and its sender and receiver, and a selected challenge by its
qualified query site under the context's replaced service
(`Template.origin`); a site is qualified by the path's applications as the
structured semantics qualifies nested sites.

`ideal` interprets such a program with transcript capabilities holding their
histories: an observation appends a message event to its state operand, and a
challenge applies the challenge function to its state operand followed by its
occurrence, returning the answer and the extended history. Receives read the
proof as in the transform; calculations use the structured evaluator's meaning;
a call invokes the named helper of a closed helper table at its checked
signature; a guard stops with `reject` when false; a loop runs its body for each
induction index below its count, threading the carried values, and refuses a
count above its maximum. Every unsupported or ill-formed instruction stops with
`refused`.

`spec` reads the same program back as the interactive validator it replaced:
each challenge becomes the selected query on a supplied service handle, an
observation of a message the validator sends is the delivery of that message to
the producer, and transcript values are computed as inert histories. Both
meanings are written in continuation style.

## The rule

`check context participant` walks the instructions with the current transcript
state, the one observation that must come next (a received message or a
challenge delivery), the enclosing loop indices and the selected query sites
already challenged. It accepts exactly when:

- the inputs are data followed by one host transcript of the context's suite;
- a receive has no observation pending, its schema is its site and its peer the
  producer, and it yields one scalar value; the next transcript operation must
  observe that value on the current state with its message occurrence
  (producer to validator);
- a challenge has no observation pending, reads the current state, carries a
  selected query occurrence not yet challenged and produces the replaced
  service's field and the successor state; the next transcript operation must
  observe its answer with the paired delivery occurrence (validator to
  producer);
- an observation is exactly the pending one, on the current suite, and yields
  the successor state;
- coordinate constructions may appear anywhere; every transcript operation reads
  coordinates built from exactly the enclosing loop indices, outermost first,
  and its template has one repeat step for each;
- a calculation, helper call or guard has no received message pending and reads
  data only; it may separate a challenge from its delivery;
- a loop has nothing pending, carries the current transcript exactly once and
  data otherwise, checks its body from the block's transcript argument with
  nothing pending, and its body ends with nothing pending and yields its final
  state at the same position;
- every other operation, including sends and unsupported ones, is refused;
- the selected query sites are distinct and each is challenged, nothing remains
  pending, the last returned value is the final state, and the other returned
  values are data matching the declared outputs.

Each refusal names its obligation (`construction-receive`,
`construction-pending`, …).

`checkExport original participant` additionally compares the export with the
original. The export must name the original's source digest and entry, with
native framing. The policy must publish exactly the validator's data inputs, in
original order, and these must be the exported validator's data inputs with the
same sorts; `publicValues` reads the scalar values the host binds at those
positions. Vector, index and count inputs, which the Sumcheck Entries publish,
are bound by typed public-value binding events
([binding codecs](fiat-shamir-security.md#binding-codecs)), which this rule does
not derive from the policy.
The replaced service must be a validator service input, and every challenge must
produce that service's field. The selected acceptance output must be a Boolean
validator output selected by every statement retained in the entry's body, and
the exported outputs must be the validator's outputs followed by the final
transcript; `exportAcceptance` gives the returned position of the decision. The
context is derived from the original roster, the policy and the service's
contract. Only the installed native construction with one replaced service and
distinct selected draws is admitted. The rule does not compare the program's
calculations, guards or results with the original; that is the obligation of
the [participant projection](participant-projection.md) rule, which composes
with this one.

`check_sound` uses only that the instruction walk (`checkFrom`) succeeds from the
initial state and that nothing is pending at its end. The other final clauses of
`check`, the coordinate conditions and the comparisons in `checkExport` are
deployment checks; `Tests.ConstructionControls` and
`Tests.SumcheckProjectionControls` exercise them as well, including coordinates
not built from the enclosing induction values and a template without its repeat
step.

`check_sound` proves, for every accepted program, every monad, challenge
function, helper table, data input, initial history, service handle and proof:

```text
ideal context challenge table returned instructions (inputs ++ [transcript initial]) proof
  = transform context challenge (spec context handle table returned instructions …) initial proof
```

Outcomes, stops and unread proofs are equal. The proof is a simulation: each
accepted step transports agreement of continuations backwards, with the
invariant that the transform's absorbed history is the current transcript state
followed by the received message awaiting observation, if any. A loop is
handled by induction on its iterations with the same invariant at each body
entry and exit. No typing premise on supplied values is needed, because both
sides make the same dynamic checks. `transform_bind_done` moves a pure final
projection through the transform.

## The compiled Schnorr proof Entry

`ZkcExamples.Construction.SchnorrProofData` is the original export of
`example::Proof`, and `SchnorrProofParticipant` the exported validator of its
compiled candidate. In `ZkcExamples.Construction.SchnorrProof`:

- `admitted` admits the original from the literal bodies in
  `SchnorrProofBodies`, and `verifier_correspondence` equates its validator
  process with the common Schnorr experiment;
- `accepted` runs `checkExport` on the actual export in the kernel, and
  `public_values` shows that the values the host binds at the checked public
  positions are the validator's original base and statement inputs;
- `compiled` runs the composed check `checkCompiled` (transcript construction
  and [participant projection](participant-projection.md)) on the actual export
  in the kernel, against the admitted original `imported` that
  `structured_views` builds from the snapshot and its admission;
- `compiled_transform` instantiates the composed theorem: for every challenge
  function, the compiled verifier's ideal meaning is the Fiat–Shamir transform
  of the original Proof Entry's validator. Its Entry-specific premises are the
  admission, the derived context, the input relation (`inputs_related`) and the
  position of the acceptance output; no equation about the program's meaning
  is assumed or computed;
- `spec_equation`, that the export's interactive reading projected to the
  selected acceptance output is the common Schnorr experiment, is derived from
  `project_sound` and `verifier_correspondence`.

The compiled proof Entries of the Sumcheck example, its composed variant, the
Sigma example, the GKR example and the guessing fixture are checked the same way
([Sumcheck](participant-projection.md#the-compiled-sumcheck-proof-entry),
[Sigma](participant-projection.md#the-compiled-sigma-proof-entries),
[GKR](participant-projection.md#the-compiled-gkr-proof-entry),
[guessing](participant-projection.md#the-compiled-guessing-proof-entry)):
each validator's ideal meaning is the Fiat–Shamir transform of its original
validator for every challenge function. For the compiled Sumcheck Entry,
[multi-round security](fiat-shamir-security.md#the-compiled-sumcheck-proof-entry)
composes this with the round-by-round soundness of the imported verifier's
transform. The compiled GKR Entry's bound composes the construction rule's
equation with a reading of the admitted original's verifier normal form as the
plain GKR verifier on well-formed statements
([GKR](fiat-shamir-security.md#the-compiled-gkr-proof-entry)). The compiled
guessing Entry's bound is imported from a worst-case round-by-round proof
stated in ArkLib's framework (written for the example)
([imported certificates](fiat-shamir-security.md#imported-certificates-for-compiled-verifiers)).
The composed Sumcheck and Sigma proof Entries have no security theorem.

`ZkcSecurity.Examples.CompiledSchnorrFiatShamir` answers every challenge with
one lazily sampled random oracle on histories, which the prover may query at any
history. `verify_eq` shows that the compiled verifier asks one challenge, at its
initialized transcript followed by the commitment message and the challenge
occurrence. `route` sends such a history to VCVio's Fiat–Shamir key (the prior
history and the commitment) and every other history to a separate key; it is
injective. `route_verify` shows that the routed compiled verifier is VCVio's
Fiat–Shamir verifier for the Schnorr Sigma protocol, and `run_eq` that the whole
experiment equals VCVio's verification run for the routed prover, because the
routed cache restricted to histories is the history cache. `knowledge_soundness`
is the registered knowledge endpoint applied to the subject's evidence
([endpoints](fiat-shamir-security.md#endpoints-over-artifact-indexed-evidence)):
this module's routing, routed prover, compiled verifier and experiment are those
of the Schnorr family package at the subject's checked context (`route_eq_shape`,
`reduce_eq_shape`, `verify_eq_evidence`, `acceptance_eq_endpoint`), and the
endpoint's Sigma bridge applies `FiatShamir.knowledgeExtractor_success`: for
every prover whose oracle queries number at most `Q`,

```text
acc * (acc / (Q + 1) - 1 / |F|) <= Pr[extractor finds w with key = w • base]
```

where `acc` is the acceptance probability of the ideal experiment run on the
compiled verifier's modeled meaning, and the relation is
the authored one retained by the Proof Entry's export
(`SchnorrProofBinding.Relation`, the retained formula's process; it equals the
Interactive import's relation, `relation_iff_interactive`). The experiment's
initial history is the binding of the checked public values
(`initial_binds_public`). `ZkcSecurity.Examples.StructuredSchnorrFiatShamir`
states the same bound for the transform of the imported interactive verifier's
Sigma instance.

## Typed requests

A selected challenge's occurrence carries its typed request
(`Zkc.Construction.Request`): the method, the operands fixed before sampling and
the result sort. `draw` is the only method of the construction model: it has no
operands, and its result sort is the field its service contract names
(`Request.draw`). The model key of a challenge (`Origin.query`) spells the kind,
the occurrence (entry, site, port and contract) and the owner, and carries the
request. The transform reads the request from the validator's query, the draw of
its field. The construction rule and occurrence templates read it from the
context (`Context.request`), which the check derives from the field of the
export's first challenge (`exportContext`), the export under check rather than
the original; the rule checks that each challenge carries the draw of its own
field. For `draw` this check is implied by the contract check, which requires
each challenge's field to be the replaced service contract's field: field,
contract and request determine one another, so the derivation certifies nothing
by itself and nothing is lost. A method with operands must instead take its
request from the original or authenticated side, the original's service call
or a checked policy, since a request derived from the export under check would
certify itself. The exported structured key `["draw", owner, field]` and the native occurrence
template, which already carries the method, are unchanged: with `draw` the only
method, they encode the typed request injectively. The respelling of the export
key as `["query", owner, method, [operand…]]`, with the occurrence encoding's
injectivity (`occurrence_inj`) extended to the operand list, lands with the
first method that has operands (`index`, `indices`).

## Interaction patterns

A programmable history provider binds its construction identity through the
digest of an interaction pattern the compiler emits
([construction obligations](../../../docs/spec/ir/construction-obligations.md#query-identities)).
`Zkc.Construction.Pattern` defines its data shape only: a `Pattern ValueSort` is
a list of `PatternStep`s, each with a kind (`StepKind`: a public value, an
absorbed message, a hint that is not absorbed, a challenge, a proof-of-work step
or a salt), the sort of its values (a parameter, to which a catalogue's sort
vocabulary attaches), how many values it carries (`StepCount`: none, one, a
static number, or at most a static maximum; a proof-of-work step carries its
difficulty in bits) and its label. No digest, encoding or semantics is defined.
The salt kind is reserved: it is part of the vocabulary because adding it later
would change request and transcript identities, but it has no semantics, and an
admissible pattern has no salt step (`Pattern.Admissible`).
`Tests.ConstructionPattern` checks that Schnorr-shaped and gated query-phase
patterns are admissible, that a salted one is refused, and that patterns
differing only in a difficulty or a maximum are different data.

## Named assumptions

- Random oracle: the suite's challenge on an absorbed history is a uniformly
  random function of that history, shared by the prover and final verification.
  Canonical value encodings are injective, so typed histories stand for
  absorbed bytes. For occurrences this is proved: the canonical occurrence
  encoding is injective and prefix-free in the template and the iteration
  coordinates (`Zkc.Construction.occurrence_inj`), and the construction bridge
  checks in the kernel that the model encoding of every exported template is its
  native bytes; the suite's framing and payload codecs remain assumed. Fields of
  a native occurrence that the model origin does not read (protocol names in the
  path and event, and a query's service port, contract and owner) are fixed by
  the exported instruction. Model occurrences omit the iteration coordinates
  that native occurrences inside loops carry; a typed history stands for the
  absorbed bytes because a validator's coordinates at each occurrence are
  determined by its absorbed history. The suite reduces 64 squeezed bytes to a field
  element, which is close to, not exactly, uniform; the model treats it as
  exactly uniform.
- Binding: the deployed host initializes the transcript with exactly the
  authorized context and the values at the policy's public inputs. The
  experiment starts from that binding (`initial_binds_public`); that the host
  does so, and that the context identifies source, policy and application, is
  assumed, not checked.
- Transport: proof bytes decode canonically to the typed messages in order.
- Native correctness: the exporter prints the checked candidate, the bridge
  decodes it, and native field, group and transcript kernels implement their
  mathematical meanings. The field and group are mathematical; no discrete-log
  hardness is assumed or used.

The theorem is fixed-statement knowledge extraction: the statement and the
initial history are fixed before the prover runs. The bound does not depend on
what the host absorbs, so statement binding carries no weight in it; binding
matters when the prover chooses the statement adaptively, which is not covered.
The theorem bounds no running time, covers no zero knowledge or other suites,
and makes no claim about Merlin or BLS12-381 implementations.

The [executable stage](executable.md) relates this constructed validator to the
program the runtime admits and replaces the transport and native-correctness
assumptions with assumptions about the runtime, its kernels and its codec.
