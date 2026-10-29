# Participant projection

This chapter defines the structural check relating a compiler-exported
role-local validator to the original protocol program, and its composition with
the
[transcript-construction rule](fiat-shamir.md#the-rule). The native
[export](../../../docs/spec/formats/constructed-participant.md) supplies the
validator; the [structured import](structured-source.md) supplies the admitted
original program.

The generic checker uses the same recursive data eligibility as the nominal
runtime, including products and sequences. Its result is structural admission.
Typed property consumers also supply a checked complete Process binding and
source laws; the table root reuses the exact retained helper and formula
closure. `Domain.Correspondence` quantifies every environment and typed reply,
retaining stops, frames and all outputs. A general source-to-constructed theorem
for every generically admitted program is not asserted here.

## Readings

The original side is the admitted root's role-local participant Process, with
components outside that role's scope absent and its helper calls interpreted
by the admitted program. The constructed side is `Domain.participant`, with
nominal data, transcript custody, dynamic coordinates and physical checkpoints.
An explicit handler supplies proof messages, public challenges and private
services. There is no additional interactive interpretation of Instruction.

`ScalarVerifier.verify` installs the selected scalar ABI for the maintained
Fiat–Shamir consumers. It prepares the exact nominal input frame, runs the
actual participant, selects the declared acceptance output and reads back the
unread proof. An unrepresentable readback refuses; it cannot silently erase a
message. Original-source correspondence is a separate proved connection.

## Slots

The rule tracks, for every original component in scope, what the exported
program holds for it (`Slot`):

- `absent`: the component is absent at the validator;
- `held r`: the exported value at reference `r` encodes the component;
- `free`: the component is present, and the exported program does not keep it;
- `service`: the component is the replaced challenge service;
- `local root`: the component is an independently owned service capability at
  that original input, matched with a nominal local request.

The root's input slots hold each published data input at its exported position
and the replaced service as `service`; every other input is absent. The root's
input scopes then mask the slots as the semantics masks the values.

## The rule

`project program context participant` walks the root body in lockstep with the
exported instructions. Before every instruction it consumes, it skips the
coordinate constructions and transcript observations that have no direct source
operation counterpart. This is a structural traversal decision; the actual
Domain execution still performs their checks and effects, which the separate
source binding must account for. For each original operation:

- marks and retained statements have no action and no exported counterpart;
- a restriction keeps its operand's slot when the validator is among its roles,
  and is absent otherwise;
- assembly selects the slot assigned to the validator's mapped role, or is
  absent when no role selects it. It consumes no instruction or reference; a
  malformed operand count is refused (`projection-assembly`);
- a calculation of the carrier vocabulary with an absent operand is absent.
  Otherwise the next instruction must be the same calculation on the references
  that hold its operands, with data results; its result is then held. If the next
  instruction is anything else, the calculation is admitted without an exported
  counterpart only when it cannot stop, and its result is `free`;
- a Math helper invocation whose operands are all absent is absent when the
  checked helper's body preserves absence (`absentPreserving`: every operation
  in it reads an operand and is evaluated strictly, so absent inputs give absent
  outputs with no effect or stop). When its operands are all present, the
  checked helper's body is walked inline: every operation in it must be a
  carrier calculation, matched as above, and the body's returned slots are the
  invocation's results: the export must inline the helper, and a Math helper
  kept as a call is refused. An invocation with both absent and present operands
  is refused (`projection-invoke`). A fold with an absent operand is absent;
  other folds at the validator are refused (`projection-operation`);
- a helper call owned by the validator must be implemented by a call of the
  same checked helper of the original program on the references holding its
  operands, with the helper's data outputs; its results are held. Calls owned by
  other roles are absent;
- a guard owned by the validator must be implemented by a guard on the
  reference holding its condition;
- an exchange must have distinct sender and receiver roles and a recursively
  handle-free data type (including services and logical oracle handles). A message from the producer to the validator must be implemented by a receive at
  the same qualified site with the same type; the received value is held. A
  message from the validator to the producer must be implemented by the
  observation of the reference holding it as a message the validator sends at
  the same qualified site, with an admitted occurrence: the delivery of a
  challenge. Exchanges between other roles are absent, and any other exchange
  involving the validator is refused;
- a draw owned by the validator on the replaced service must be implemented by a
  challenge of the same field at the same qualified query site, with an admitted
  occurrence; its answer is held;
- a protocol application in which the validator participates is walked through
  the callee's checked body in the child context (the application's qualified
  site prefix and role substitution), from the argument slots under the callee's
  input masks; its results are the callee's output slots under its output masks.
  The exported program has no instruction for the application itself: the
  callee's instructions are inlined. An application without the validator is
  absent, and an unknown callee is refused (`projection-application`);
- a repeat in which the validator participates must be implemented by the next
  exported loop, at the same qualified site, with the same maximum and with its
  count held at the loop's count operand. The loop's carried values must start
  with the references holding the state components the validator has, in order
  (the others are absent); the remaining carried values are not related to the
  original: the transcript, or data that no matched instruction reads.
  The loop body is walked once against the repeat body, from slots holding the
  induction index, the carried state and the repeat's captures; after its
  instructions only plumbing may remain, and the yielded references must start
  with the references holding the new state components the validator has. After
  the loop, those components are held at the loop's results
  (`projection-repeat`, `projection-repeat-yield`). A repeat without the
  validator is absent.

After the body, only plumbing may remain, every returned reference must be
bound, and the data return references must hold the validator's outputs in
original order. Plain profiles keep every returned reference. Only the
Fiat–Shamir profile excludes its final transcript from that comparison. Each refusal names its
obligation (`projection-calculation`, `projection-receive`,
`projection-unexplained`, …).

Helper calls are read with the original program's checked helpers
(`helperTable`). The candidate's prepared helper bodies are not compared with
them by these rules: that a candidate helper computes its original's function is
the native construction check's obligation, which the bridge exercises with a
mutated helper body.

The rule compares operations, not their algebra: a calculation implemented by an
algebraically equal but different calculation is refused. A total calculation
the export omits may be omitted only because its result is never needed: a
later use of a `free` component as a guard condition, message, helper argument
or output requires a held reference and is refused, and a total calculation on a
`free` operand can itself only be omitted.

## Soundness

Structural admission and semantic correspondence have distinct obligations.
`project` rejects mismatched source/artifact structure. Its acceptance alone
is not used as an assumed execution equation. `Domain.Correspondence` checks
an actual artifact against a generated or authored Process view, quantifying
all environments and all typed replies and preserving actual stops, frames
and returned values. An `Original.Simulation` or source equation connects that
view to the admitted original, with the appropriate role masks, helper laws,
service routing and output relation.

This division makes the view reusable for completeness, adversarial soundness
and cost arguments. Generating a readable view does not discover a mathematical
invariant or prove its intended reference law. Helpers and loops use reusable
structural rules; authors supply the missing helper mathematics, source routing
and state relation when existing library laws do not suffice. Actual artifact
and source identities are kernel checked, not inferred from matching labels.

### Checked connection certificates

`ConnectionCertificate.Certificate` fixes the checked source body, role and
roster, input pattern, complete output locations, initial frame layout and
indexed target block before certificate search. Its fields contain a checked
normalization result and a finite typed alignment derivation. Search is
untrusted: an accepted derivation is ordinary kernel-checked data, with no
instance-supplied root execution equation.

`ConnectionCertificate.Certificate.simulation` proves the corresponding
`Original.Simulation` for the plain profile. It quantifies over the nominal
model, exact helper-table interpretation, source binders, physical environment,
ABI-related captured inputs and frame/history relation. It retains all typed
replies, stops and complete returns. A malformed or missing routing entry must
not be justified by a vacuous refusal simulation: reached-source routing
coverage remains a separate caller obligation.

This bounded certificate interface has no normalizer-law or retained-callee
environment. The occurrence-preserving nested-application pilot composes
source normalization, selected callee equations and finite connection rules
explicitly; transcript delivery and private-service rules have complementary
checks. These pilots do not establish a generic certificate for every admitted
root. Root masks, ABI assembly, routing coverage and retained-callee installation
are not yet generated for all maintained clients. The structural `project`
walker remains in admission and has no passing-check-to-simulation theorem.
Its retirement and complete common root assembly remain separate work.

## Composition with transcript construction

`checkCompiled imported participant` checks the transcript construction and
projection against the same `Structured.Imported original`. It cannot pair an
admitted program from a different snapshot with the export's claimed original.
`select` and `Selection.check` fix the context, public input order, service
replacement, declared sorts and Boolean output position. These are finite
admission facts, not a universal source-equivalence theorem.

For a maintained scalar consumer, its checked all-reply binding yields:

```text
ScalarVerifier.verify program context artifact position challenge public initial proof
  = transform context challenge originalVerifier initial proof
```

The equation retains arbitrary typed public values, scalar proof messages,
initial history, lawful monadic challenges, exact unread suffixes and stops.
Its source side may later be rewritten using a decoded mathematical table or
well-formed circuit; those extra hypotheses belong to that later theorem.

When a selected scalar ABI projects occurrence coordinates, projection happens
before invoking the existing oracle and cache. The initial scalar history is
an opaque prefix. The equation does not identify a fresh random oracle on
nominal coordinate-bearing keys with the projected scalar oracle. Native byte
correspondence and its resource/codec assumptions remain separate.

## The compiled Sumcheck proof Entry

`SumcheckArtifact` holds generated admission and input metadata.
`SumcheckDomainConnection` checks the actual artifact's round, loop and root
Process; `SumcheckSourceConnection` connects it directly to the admitted
source. `ZkcExamples.Construction.SumcheckProof.compiled_transform` selects
acceptance of that actual canonical execution for every raw typed table,
claim and round count. It does not assume a valid table or honest proof.

`compiled_transform_rounds` adds the source theorem's admitted-count and decoded
table premises to interpret the terminal as multilinear evaluation.
`ZkcArkLib.Examples.CompiledSumcheckFiatShamir` then applies the multi-round
bound: `(Q + count) / |F|` for a fixed well-formed false statement, with the
separate adaptive theorem under typed public binding. The same canonical
participant also underlies the [byte consumer](executable.md#the-compiled-sumcheck-proof-verifier).

## The compiled composed Sumcheck proof Entry

The retained `TwoSums` source applies `Reduce` at two sites, each with its own
loop, then checks both residual claims and conjoins the results. Its complete
source and artifact identities match the existing TwoSums validator
certificate. `ComposedSumcheckDomainConnection` reuses that certificate and
proves the routing of both applications. The maintained
`ComposedSumcheckProof.compiled_transform` therefore concerns the actual
canonical participant, rather than another instruction interpreter.

The connection covers raw tables, claims and counts, every reply, zero and
excess counts, and helper failure. It supplies no composed security theorem by
itself; the separately generated TwoSums receipts retain their own fixed
requests and property proofs.

## The compiled Sigma proof Entries

`SchnorrAndProof` and `ChaumPedersenProof` connect the actual compiled
`AndProof` and `EqualityProof` participants to their admitted originals. Their
Domain/source bindings preserve the two commitments, shared challenge,
response arities, guards, result selection and stops. They reuse generic
Process and handler laws; source-specific finite equations remain checked
facts rather than trusted premises.

Their fixed-statement knowledge claims are applications of the registered
knowledge endpoint to those subjects' evidence. The source connection is
independent of the extraction method. Okamoto uses the same boundary with its
own representation relation and checked participant connection.

## The compiled GKR proof Entry

`GkrArtifact` records admission of the full `examples/projects/gkr` proof
Entry. The actual validator contains the output-point loop, layer loop, both
nested degree-two Sumcheck loops, and the line-coefficient phase. Its checked
connection retains all four raw public tables, dimensions, replies, helper
failures and zero/excess counts. It is separate from the smaller finite GKR
gate component used to test reusable bindings.

`GkrProof.compiled_transform` connects that complete canonical participant to
the admitted original. On well-formed statements, `GkrSourceVerifier.verifier_reads`
rewrites the original into the mathematical GKR verifier; the ArkLib consumer
transfers its weighted and query-count bounds for widths/layers within the
exported maxima. This source/constructed theorem does not establish a native
GKR byte verifier or nominal-ROM equivalence.

## The compiled guessing proof Entry

`GuessProof` connects the actual participant of the guessing fixture to its
source: receive a guess, draw and deliver a field challenge, then compare the
guess plus the public offset with the challenge. `verifier_correspondence`
identifies the source Process by computation, and the checked Domain binding
supplies `compiled_transform`. `ZkcArkLib.Examples.CompiledGuessFiatShamir`
uses a certificate imported from ArkLib's round-by-round framework for that
fixed actual verifier.

## Controls

`Tests.ProjectionControls` runs the composed check on mutations of the actual
compiled Schnorr validator. Each mathematical mutation keeps the transcript
wiring, so `checkExport` accepts it, and each is refused by the projection rule:
the final comparison of the base with itself, the response scaling the
statement, the challenge scaling the base, a sum with the wrong summand, a
comparison with swapped operands, and a constant `true` returned as the decision
(`projection-unexplained`). The other controls are a returned sum instead of the
decision (`construction-final`), an acceptance selection of an output the
validator does not have (`construction-acceptance`), the witness published to the validator
(`construction-context`), a delivery observed as sent by the producer
(`projection-delivery`), a challenge drawn at the delivery site
(`projection-challenge`), a response received at the commitment site
(`projection-receive`), an extra calculation (`projection-unexplained`) and a
truncated program (`projection-outputs`).

`Tests.SumcheckProjectionControls` does the same for the compiled Sumcheck
validator: a dropped round check (`projection-guard`), a round check comparing
the sum with the claim (`projection-guard-operand`), a mutated claim update and
challenge term (`projection-unexplained`), a loop yielding the claim it started
with (`projection-repeat-yield`), a changed loop bound, an unqualified loop site
and a loop starting from the table values (`projection-repeat`), and a terminal
check with swapped operands (`projection-call`). The transcript-construction
rule accepts every one of these mutations. The same module exercises that rule's
deployment checks inside the loop: coordinates without the induction index and a
template without its repeat step (`construction-observe`), coordinates appending
a non-index value (`construction-coordinates`), and a loop count, guard or call
reading the wrong sort (`construction-loop`, `construction-guard`,
`construction-call`). The construction bridge also refuses
mutations of the composed export: a conjunction reading the left check twice
(`projection-unexplained`) and a right terminal check reading the left
reduction's point and claim (`projection-call`); and of both Sigma exports: the
second commitment's observation absorbing the first commitment
(`construction-observe`), a comparison of a base with itself and a conjunction
reading the first check twice (`projection-unexplained`). For the GKR export it refuses a
dropped first round check and a dropped wiring check (`projection-guard`), a
mutated round claim update (`projection-unexplained`), a layer loop yielding the
claim it started with (`projection-repeat-yield`) and a challenge origin naming
the delivery site (`construction-challenge-site`).

`Tests.ProjectionControls` also shows why the composed check takes an admitted
original. Changing the original Schnorr root's final comparison into a
comparison of the sum with itself gives a snapshot that still admits; its
program and a candidate whose decision compares the sum with itself pass the
construction rule against the unchanged snapshot and the projection rule
against the altered program (`unlinked_accepts_mixed`), and the altered pair
passes the composed check against its own snapshot (`altered_accepted`). The
unchanged snapshot does not admit the altered program (`mixed_unadmitted`), so
every admitted subject of the unchanged snapshot is the actual program
(`subject_unique`) and refuses the altered candidate (`mixed_refused`,
`projection-unexplained`).

`Tests.SigmaProofControls` evaluates the compiled Sigma verifiers in the kernel
over `ZMod 3`: each accepts an honest proof exactly at the challenge it answers,
rejects a wrong response and stops with a refusal on a truncated proof, so the
instantiated `compiled_transform` equations are not about verifiers that always
stop.
