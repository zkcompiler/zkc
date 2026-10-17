# Fiat–Shamir transcript construction

This chapter defines the formal check of the compiler's native
[transcript construction](../../../docs/spec/ir/construction.md) for a role-local
validator, the transform theorems it supports for the compiled Schnorr and
Sumcheck proof Entries, and the security theorem for the Schnorr Entry. The native [export](../../../docs/spec/formats/constructed-participant.md)
supplies the checked candidate's validator; the
[structured import](structured-source.md) supplies the original program.

## Transform of a validator

`Zkc.Construction.transform` is the Fiat–Shamir transform of a validator
process over the common participant actions whose every query is a selected
challenge, for a challenge function
`challenge : History F G → m F` in any monad. A history is the ordered list of
absorbed events: the host's `binding` of the public context and values, a
`message` with its occurrence origin and typed payload, or a `challenge`
occurrence.

- A receive reads the next proof message, decodes it at the expected type and
  nominal domain, and absorbs it. Decoding failure or an exhausted proof stops
  with `refused` and consumes nothing.
- A query is answered by `challenge` on the history followed by the query's
  occurrence, which is then absorbed.
- A send is absorbed with its message occurrence and produces no proof data.

The result is the validator's outcome and the unread proof suffix. Occurrence
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
same sorts; for scalar inputs, `publicValues` reads the values the host binds at
those positions. Vector and index inputs, which the Sumcheck Entries publish,
have no binding model.
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
  in the kernel;
- `compiled_transform` instantiates the composed theorem: for every challenge
  function, the compiled verifier's ideal meaning is the Fiat–Shamir transform
  of the original Proof Entry's validator. Its Entry-specific premises are the
  admission, the derived context, the input relation (`inputs_related`) and the
  position of the acceptance output; no equation about the program's meaning
  is assumed or computed;
- `spec_equation`, that the export's interactive reading projected to the
  selected acceptance output is the common Schnorr experiment, is derived from
  `project_sound` and `verifier_correspondence`.

The compiled proof Entries of the Sumcheck example, its composed variant and
the Sigma example are checked the same way
([participant projection](participant-projection.md#the-compiled-sumcheck-proof-entry)):
each validator's ideal meaning is the Fiat–Shamir transform of its original
validator for every challenge function. For the compiled Sumcheck Entry,
[multi-round security](fiat-shamir-security.md#the-compiled-sumcheck-proof-entry)
composes this with the round-by-round soundness of the imported verifier's
transform; the other compiled Entries have no security theorem here.

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
then applies `FiatShamir.knowledgeExtractor_success`: for every prover whose
oracle queries number at most `Q`,

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
