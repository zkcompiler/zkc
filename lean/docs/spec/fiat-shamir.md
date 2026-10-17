# Fiat–Shamir transcript construction

This chapter defines the formal check of the compiler's native
[transcript construction](../../../docs/spec/ir/construction.md) for a role-local
validator, and the security theorem it supports for the compiled Schnorr proof
Entry. The native [export](../../../docs/spec/formats/constructed-participant.md)
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
and the policy's ordered query/delivery sites. They are the flat native origin
templates of the native
[occurrence encoding](../../../docs/spec/ir/construction.md#native-occurrence-encoding),
whose canonical bytes the bridge decodes and re-encodes exactly.

## Constructed programs

`Zkc.Construction.Participant` carries the exported validator: decoded policy,
sorted inputs and outputs, instructions with absolute operand references and
result sorts, and returned references. Instructions are receives, sends,
flat coordinate constructions, transcript observations and challenges with
their suites and decoded origins, scalar calculations of the common vocabulary,
and unsupported operations, retained by name.

`ideal` interprets such a program with transcript capabilities holding their
histories: an observation appends a message event to its state operand, and a
challenge applies the challenge function to its state operand followed by its
occurrence, returning the answer and the extended history. Receives read the
proof as in the transform; calculations use the selected scalar interpretation;
every unsupported or ill-formed instruction stops with `refused`.

`spec` reads the same program back as the interactive validator it replaced:
each challenge becomes the selected query on a supplied service handle,
immediately followed by the delivery of its answer to the producer, and
transcript values are computed as inert histories.

## The rule

`check context participant` walks the instructions with the current transcript
state, the one observation that must come next (if any) and the number of
challenges so far. It accepts exactly when:

- the inputs are data followed by one host transcript of the context's suite;
- a receive has no observation pending, its schema is its site and its peer the
  producer, and it yields one scalar value; the next transcript operation must
  observe that value on the current state with its message occurrence
  (producer to validator);
- a challenge has no observation pending, reads the current state, carries the
  next selected query occurrence, produces the replaced service's field and the
  successor state; the next transcript operation must observe its answer with
  the delivery occurrence (validator to producer);
- an observation is exactly the pending one, on the current suite, and yields
  the successor state;
- coordinate constructions (`indices.empty`) may appear anywhere; each
  transcript operation reads one of them;
- a calculation has no observation pending and reads data of its declared
  argument sorts, producing its declared result sort;
- every other operation, including sends and unsupported ones, is refused;
- every selected draw occurs, nothing remains pending, the last returned value
  is the final state, and the other returned values are data matching the
  declared outputs.

The rule is narrower than the native construction, which may keep
calculations between a draw and its delivery: such programs are refused here,
and `spec` places each delivery immediately after its query.

`checkExport original participant` additionally compares the export with the
original. The export must name the original's source digest and entry, with
native framing. The policy must publish exactly the validator's data inputs, in
original order, and these must be the exported validator's data inputs with the
same sorts; `publicValues` reads the values the host binds at those positions.
The replaced service must be a validator service input, and every challenge must
produce that service's field. The selected acceptance output must be a Boolean
validator output selected by every statement retained in the entry's body, and
the exported outputs must be the validator's outputs followed by the final
transcript; `exportAcceptance` gives the returned position of the decision. The
context is derived from the original roster, the policy and the service's
contract. Only the installed native construction with one replaced service and
distinct selected draws is admitted. The query and delivery sites come from the
policy; the per-compile equation between the interactive reading and the
original validator (`spec_equation` below) ties them to the original.

`check_sound` uses only that the instruction walk (`checkFrom`) succeeds from the
initial state. The final clauses of `check` (every draw occurs, nothing remains
pending, the final state and the outputs are returned) and the comparisons in
`checkExport` are deployment checks; the controls exercise them as well.

`check_sound` proves, for every accepted program, every lawful monad, challenge
function, data input, initial history, service handle and proof:

```text
ideal challenge returned instructions (inputs ++ [transcript initial]) proof
  = transform context challenge (spec context handle returned instructions …) initial proof
```

Outcomes, stops and unread proofs are equal. The proof is a simulation over the
instruction list: the transform's absorbed history is always the current
transcript state followed by the one observation the rule requires next. No
typing premise on supplied values is needed, because both sides make the same
dynamic checks. `transform_bind_done` moves a pure final projection through the
transform.

## The compiled Schnorr proof Entry

`ZkcExamples.Construction.SchnorrProofData` is the original export of
`example::Proof`, and `SchnorrProofParticipant` the exported validator of its
compiled candidate. In `ZkcExamples.Construction.SchnorrProof`:

- `admitted` admits the original, and `verifier_correspondence` equates its
  validator process with the common Schnorr experiment;
- `accepted` runs `checkExport` on the actual export in the kernel, and
  `public_values` shows that the values the host binds at the checked public
  positions are the validator's original base and statement inputs;
- `spec_equation` proves that the export's interactive reading, projected to
  the selected acceptance output, is that same experiment, by computation;
- `compiled_transform` composes these: for every challenge function, the
  compiled verifier's ideal meaning is the Fiat–Shamir transform of the original
  Proof Entry's validator.

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

where `acc` is the compiled verifier's acceptance probability and the relation is
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
  Canonical value and occurrence encodings are injective, so typed histories
  stand for absorbed bytes. The suite reduces 64 squeezed bytes to a field
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
