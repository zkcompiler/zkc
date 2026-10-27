# Executable validator stage

This page specifies the Lean model of the validator participant in a deployed
`zkc.program/0` artifact and its connection to the authoritative constructed
`Domain` execution. A finite reader identifies the actual machine program;
a separately proved correspondence relates its bytes, budget and oracle
interaction to canonical execution. Connecting that participant to the admitted
original protocol requires the shared source connection described in
[participant projection](participant-projection.md).

The main owners are `Program`, `Execution`, `Installed`, `Reading`, `Code`,
`DomainLowering`, `DomainNormalizationCheck`, `DomainNormalizationSoundness`,
`DomainNativeEntry`, `DomainNativeSoundness`, `DomainNativeExecution` and
`DomainNativeByteTransport` under `Zkc.Executable`. Helper preparation and cost
laws live in `Helpers`, `HelperSoundness`, `NativeLaws` and `HelperCosts`.
`Observations` owns the property-independent pruning relation. There is one
constructed-instruction evaluator, `Construction.Domain`; the costed `Code`
interpreter calls its operations and adds the machine's resource schedule.

## Carrier

`Validator` holds the participant that the program's entry map assigns to the
deployment's entry and validator role, with every local function it calls and
every operation binding those functions use. Names, sites, schemas and physical
types are kept as the artifact spells them; a physical type is a value sort with
a representation, such as G1 at `arkworks.g1/0`. An occurrence template carried
by a transcript operation is decoded; other parameters stay text.
Bindings retain the complete list of physical specialization arguments from the
five-field native binding record. The bridge never erases that list.

Participant instructions are typed receives, local calls, counted loops, the
yield that ends a loop body and the final return. A loop names its count, which
must not exceed a static maximum, its induction variable, its carried values
with their initial values, its captured values, its body and the names bound to
what the last iteration yields. Local function bodies are operations on declared
bindings, Boolean constants, conditional regions on captured values, counted
iterations over an index range, explicit stops, region yields and the final
return. Any other instruction is kept as unsupported, which the rule refuses.
The carrier fixes no meaning.

## Meaning

`execute` runs a validator as the native runner does, on data inputs, the host's
initial transcript and the proof's message bytes, with the deployment's
occurrence `Context`, a challenge function in any monad, a decoder and an
instruction budget.

- Work. Every receive, local call, loop, yield and return of the participant
  and every instruction of a local body is charged one instruction. A local call
  enters a frame and runs the function's body; every loop iteration runs the
  loop body in a frame of its own, holding the index, the carried values and the
  captures. The budget is checked before each charge, so a budget of `b`
  executes exactly the first `b` charged steps.
- Framing. A receive reads an eight-byte little-endian length and that many
  bytes. A missing message cancels the run; a message that does not decode at
  the receive's physical type stops it after charging the receive. A decoded
  value of another sort is a contract failure.
- Operations. A binding resolves through a `Vocabulary`: each row assigns a
  meaning to an exact contract, static arguments, installed implementation and
  physical specialization,
  and each representation row admits a sort at a representation. Meanings are
  those of `Zkc.Construction`: structured calculations
  (`Zkc.Construction.calculate`), the structured index and vector primitives
  (`Zkc.Source.Structured.Primitive.evaluate`), pointwise vector arithmetic, the
  requirement that a Boolean is true, numerical expression calls, occurrence
  coordinates, and observation and challenge on the ideal transcript model. A
  constant takes its value from the operation's single canonical decimal
  parameter. The current native vocabulary separately installs the default and
  explicit BLS12-381 scalar/G1 transcript payload layouts. A different layout,
  crossed payload sort or additional physical argument does not resolve.
- Numerical calls. A `numerical.map`, `numerical.sum` or `numerical.product`
  binding names its field and an operand mask, and its operation carries one
  `zkc.ring/0` expression as text. `Numerical.decode` reads that text into a
  `Zkc.Algebra.RingExpression.Expr` with natural literals and slot inputs,
  refusing with a named reason exactly the payloads the runtime's program
  admission refuses: a body over 4096 bytes, text other than the canonical
  encoding of an arena, an input or constant outside the call's field, a literal
  that is not a canonical decimal below the characteristic, an input node outside
  the declared inputs, an operand that does not point backward, an embedding,
  declared inputs other than the mask's positions, other than one output, and a
  node the output does not reach. A mask has at most 1023 positions. A refused
  payload or mask does not resolve. One vocabulary row serves every mask: the
  mask is the binding's last static argument. The call reads the row count and
  then one scalar for each `0` and one vector of exactly that many values for
  each `1`; another operand count, kind, field or length is a refusal of the
  kernel. Scalars are broadcast, and the call returns the vector of the
  expression's values at the rows, their sum from zero or their product from
  one. The runtime's bound of 1 048 576 rows is a capacity limit of the native
  call, like the element limit of every vector a kernel produces; the meaning
  does not stop on it. A transcript operation's
  occurrence template is named by its model occurrence under the context; a
  template without one is a contract failure, as it is a refusal of the ideal
  meaning.
- Control. A conditional runs the region its Boolean selects; an iteration runs
  its region for every index of its range, carrying what each iteration yields
  into the next; a participant loop runs its body for every index below its
  count. A count above the static maximum, a missing name or a yield of the
  wrong length is a contract failure. An explicit stop names its reason.
- Custody. The transcript is one affine unit. An observation or challenge must
  consume its live state; a stale state is a contract failure.
- Stops. A stop leaves every active frame, innermost first, and retires the live
  transcript; a cancellation leaves them as cancelled. A normal return leaves the
  participant frame and hands the returned transcript to the host, which retires
  it.

`validate` is the host's acceptance of complete proof bytes: the first 40 bytes
must be the framing magic and the expected invocation binding, the run must
return normally with the selected Boolean true, and every proof byte must be
read. `installed` is the vocabulary of the native BLS12-381 deployments: the
arkworks scalar-field, G1, scalar-vector and numerical expression kernels, the
native index kernels and the Merlin transcript kernels of
`merlin3.bls12-381.fr64be/0`.
Its observation rows require the exact arkworks field or group specialization;
an absent, different or additional physical argument has no installed meaning.
Other installed rows require an empty specialization list. Native implementation
correctness remains an assumption; matching a row is not a proof of a kernel.

`evalSteps` is the unbounded meaning of a local body that applies no transcript
operation: the values it hands back, or the cause it stops for, after the
instructions it charges until then. Such a body neither queries the challenge
function nor touches the live transcript, so its run under a budget is this
evaluation cut off by the budget (`localK_evaluates`).

## Lowering rule

`Validator.read vocabulary helpers validator` reads the validator's machine work
back as constructed instructions. `helpers` are the helpers the constructed
validator calls by name.

- A local call to a function the constructed validator calls by name is a
  helper call. Its body must apply no transcript operation, its operands must
  have the sorts of its formals and its results must be data. The reading keeps
  the call, and its charge is what the body's evaluation charges.
- Any other local call is transparent: formals denote actual operands and the
  results denote the operands of the return, as the constructed-participant
  export expands such functions. A transparent body is read operation by
  operation, with a Boolean guard (a conditional that yields nothing or stops
  with `reject`) read as a guard instruction.
- A participant loop must count with an index data input, carry values whose
  sorts it keeps, hand on the live transcript in custody, carry at most one
  transcript, capture data only, and yield its carried sorts; the reading is a
  constructed loop with the same maximum, whose body is the reading of the loop
  body.
- Each operation is read through the vocabulary's meaning, with checked operand
  sorts, consumption of the live transcript and the live transcript as the only
  returned transcript. Function and binding symbols must be distinct, and every
  declared type and receive must have an admitted representation.

The reading records the charge of every instruction and a receive plan: a
receive at its physical type, or a loop whose count is a data input, run at
most its maximum times. `Plan.types data plan` are the receive types of a run
on the data inputs. For a reading without loops and helper calls the charges are
static, and `Lowered.total?` is the charge of a complete run.

`checkLowering vocabulary participant validator` requires the reading's input
and output sorts, symbol, entry and validator role to match the participant.
It then always runs `CanonicalNormalization.check`, including the selected
output schema. Identical instruction lists do not bypass this check.
`checkLowering_checks` exposes those finite facts; it is not a theorem that a
source protocol and a machine program have equal executions.

Native correspondence additionally uses `checkNativeLowering program context
vocabulary participant validator`. It checks the actual entry and program
scope, nominal data/helper signatures, live transcript suite, occurrence shape
and coordinate depth, and loop capture/yield custody. `NativeCertificate`
contains the successful finite check and final scope, not an assumed execution
equation. `nativeEntry_reached` derives the entry relation from the actual input
admission, and `checkNativeLowering_preserves` preserves it for every typed
reply. These are explicit restrictions of the supported native profile.

A refusal identifies the failed boundary: instruction, binding, representation,
signature, input/output schema, custody, occurrence, loop or normalization
anchor. Arithmetic or relation validity is not an entry premise. False claims,
malformed table shapes and arbitrary proof bytes remain in the modeled inputs.

## Normalization

The compiler may place pure arithmetic differently from the constructed export,
share equal values and omit unused values. `CanonicalNormalization.check inputs
outputs exported exportedReturned reading readingReturned` compares those
schedules. It is proved against actual `Domain` execution, including refusals.

- Movable instructions are total calculations and well-formed occurrence
  coordinate construction. Their operand schemas and complete declared result
  lists must agree with the operation. A malformed unused calculation cannot be
  discarded merely because a scalar interpreter would ignore its declaration.
- Other operations are ordered anchors. Their operation, declarations and
  operand terms must agree. Identical anchors may still refuse dynamically;
  the correspondence retains that common refusal. Helpers are interpreted by
  the actual program, not by an arbitrary replacement function.
- A scope interns typed terms over input, loop-index, carried-value and earlier
  anchor-result leaves. A loop creates a child scope and checks its complete
  yielded tuple. The final selected references must agree at the declared
  output schema.

The checker admits dependency-respecting total rescheduling, operand
renumbering, sharing and unused total work. It conservatively refuses changed
anchor order or terms and movement across loop scopes. Refusal does not assert
that every such pair is inequivalent; proving more equivalences requires a
stronger checked rule. Moving a possible refusal after a query is specifically
unsafe because it changes the observable query prefix.

`CanonicalNormalization.accepted_sound` establishes equality of the two
returned-value Processes at the reached input schema. Ordered effects, every
reply, all stops and unread proof consumption are retained by their handlers.
`DomainParticipant.runK_participant` and `DomainVerifierTransport.verifier_observation`
connect this observation to the actual participant and selected scalar verifier.
The participant's finite `ReturnSchema` is explicit.

Normalization makes no equality claim about charge schedules, machine frames,
stop sites or the budget at which execution stops. `metered_prunes_checked`
composes canonical normalization with all-budget pruning;
`metered_checked` uses the actual reading's static sufficient budget.

## Helper preparation

A helper call of the constructed validator is read by a closed table of checked
helpers. `Prepared vocabulary validator table name` states that the executable
body of the local function `name` implements the helper of the same name: on
arguments of its declared input sorts, its unbounded evaluation hands back
exactly the values the helper returns, at the function's declared result sorts,
or stops in the class the helper stops in. Preparation is a premise of the
soundness theorems for every helper the reading calls; a validator without
helper calls needs none. The lowering rule reads a helper body only for its
sorts and its freedom from transcript operations, so a changed helper body
can pass the rule; what the body computes is the obligation of the helper rule.
The executable bridge requires the committed program data, which the
obligation is about, to be the rendering of the fresh program.

The helper rule `checkHelpers vocabulary validator program names` reads, for
each named helper, the local function of that name against the typed body of
the original's checked definition of the same name, one structured operation at
a time, through a closed table of recipes (`Zkc.Executable.Helpers`):

| Structured form | Executable form |
|---|---|
| Site mark | No step |
| Operation without regions | One installed operation with the same meaning (`implements`): the same primitive, an index constant below the index limit, a carrier calculation, or index equality on operands known to be below the index limit |
| Boolean constant | A constant step |
| Invocation of a checked helper | That helper's body, inlined under the names of its actual operands |
| Guard | A conditional that yields nothing on true and stops with reason `reject` on false |
| Branch | A conditional on the same condition and captures, each region read as the corresponding callback |
| Stop, return | An explicit stop for the same reason; the function's return of the returned names |

Every name an executable step binds must be fresh, so that a name keeps the
value it denotes; index names produced by checked index primitives and by index
constants below the limit are tracked as bounded. A body outside the table is
refused with a named reason (`HelperRefusal`): a missing function or
definition, another signature, a structured operation without a recipe (loops,
folds, maps and binds), a step that does not implement its operation, a
rebound name, an unbounded index operand or another ending.

`checkHelpers_sound` proves the rule once: every helper it accepts is
`Prepared` against the program's helper table, for every argument list of the
declared input sorts. The proof simulates the structured evaluation by the
executable one, with the names the walk relates denoting the encodings of the
structured values. A helper outside the table, such as one whose body iterates
over a runtime bound, is prepared by a proof of its own; transferring a
preparation between validators whose local function and bindings agree
(`prepared_agrees`, decided by `bindingsAgree`) needs no further proof.

## Soundness

`DomainVM.metered` executes the actual `Code` under its budget. Ordinary steps
and helpers invoke canonical `Domain.step`; the VM charges before execution,
including each loop entry, iteration yield and final return. Helper charges use
the actual local evaluation cost on the actual arguments. It does not introduce
another interpretation of constructed instructions.

`decodeProof` decodes message bytes at `Plan.types data lowered.plan`. Missing,
truncated, failed or wrong-sort messages remain observable failures. Bytes after
the final planned receive leave an unread obstruction, so successful acceptance
cannot discard a trailing suffix. Arbitrary-byte soundness does not assume a
round-trip codec or an honest prover.

The public correspondence quantifies over lawful monads, challenge functions,
decoders, budgets, admitted typed inputs, opaque initial scalar histories and
all proof bytes. The finite native check and actual helper `Prepared` laws are
its premises. Its public roots discharge the internal scope and continuation
invariants; clients do not supply an assumed whole-execution equation.

| Theorem in `DomainVM` | Statement |
|---|---|
| `checked_execute_metered` | The native machine's observation equals canonical metered execution of its actual lowered Code, decoded plan and returned references |
| `checked_validate_metered` | The exact 40-byte magic/binding test and host acceptance compose with that observation |
| `checked_validate_prunes` | At every budget, host acceptance prunes selected nominal acceptance of the resource-free actual lowered Process, retaining preceding oracle calls |
| `checked_execute_static` | A static total below the supplied budget gives the resource-free observation |
| `checked_execute_sufficient` / `checked_validate_sufficient` | A proved dynamic sufficient-budget predicate gives the same connection, with the validation header retained |

The observation retains the complete returned scalar tuple and unread
emptiness on success, and the stop class on failure. It does not equate raw
unread byte suffixes on stopped runs, counters, frame events or cleanup traces.
`Executable.execute_cleaned` separately proves frame cleanup. A partial decoder
can stop before its typed projection recovers the byte suffix; that is why the
observation does not claim stronger stopped-state equality.

The selected scalar native ABI projects occurrence coordinates with
`Origin.withoutCoordinates` **before** oracle/cache use. The initial scalar
history remains an opaque prefix. This explicit projection is not a theorem
that a fresh nominal random oracle has the same game as the projected oracle.
A finite static artifact uses an additional proved origin-identity connection
when its verifier selects the unprojected key.

`Prunes rejects first second` allows replacing continuations by rejecting
results while preserving the other calls in order. Its probability consumer,
`ZkcSecurity.VCVio.Pruning.Prunes.prEvent_le`, applies under a stateful oracle
implementation. It gives acceptance domination, not completeness, extraction or
an arbitrary game equivalence. The byte-to-participant proof then composes
normalization and the participant/source connection for the selected subject.

## Completeness

`DomainVM.FitsK`, `FitsStep` and `FitsIterate` account for actual Code charges.
`Continues` describes only possible successful continuations of the canonical
operation, quantified over permitted replies and proof consumption. It does not
claim that an operation must return. `Sufficient` includes the final return
charge; `metered_sufficient` gives equality with resource-free execution.

`Code.charges` and `helperBound` compute bounds for their finite supported
fragments. `FitsK.loop_invariant` and the iteration rules compose a proved
invariant and per-iteration bound over arbitrary runtime counts. A dynamic
helper's cost law refers to its real argument list. Resource units are native
instruction charges, not elapsed time or an asymptotic cryptographic cost model.

Honest success is a separate fact. `DomainVM.Passes` reuses the canonical
Process with the actual deterministic scalar oracle and an explicit successful
postcondition. It checks the reached receives and query replies and rejects
every stopped path. Its bind and fold rules compose honest-step mathematics; the
cost proof may reuse the structural continuation facts without treating refusal
as honest success. Both paths use the same checked participant/source binding.

`messageBytes` frames a homogeneous message list with the magic and binding.
`decodeProof_messages` needs codec inversion only at that message's actual
physical type and a size bound. The general `FrameCodecRows` contract pairs each
physical receive type with its actual payload; it does not require a field-only
codec to encode arbitrary groups or Booleans. Honest acceptance additionally
needs the correct binding/header, a successful honest producer, its relation
and shape hypotheses, and sufficient resources. None of those premises is
silently imposed on arbitrary-byte soundness.

## The compiled Schnorr proof verifier

`ZkcExamples.Executable.SchnorrProof` connects the validator of the exact
`zkc.program/0` candidate of `example::Proof` to its actual constructed
participant and admitted source. `native_checked` accepts its nominal input,
helper, occurrence and output boundaries; `schedule_source` uses the checked
all-reply `SchnorrDomainConnection`. A complete run charges 25 instructions.

`executable_transform` preserves the source-transform statement for every byte
string, decoder, public base/key, source handle, opaque initial scalar history,
lawful-monad challenge function and budget at least 25. The native key map is
`Origin.withoutCoordinates`, whereas this static participant's scalar verifier
uses identity. `schedule_keys` proves their agreement on the actual source
histories and sites. It does not assume arbitrary origins are static.

`domain_prunes` has the exact generated endpoint target: selected acceptance of
`ScalarVerifier.verify` at this participant and the actual published inputs,
with the actual receive plan decoding `bytes.drop 40`. It holds at every budget
without codec inversion or relation-validity hypotheses. `executable_validate`
gives equality at budget 25 or greater with the exact binding/header test.
`executable_rejects` preserves preceding challenge effects when a short budget
or bad header forces rejection. A budget of 24 can therefore reject after one
oracle call; a bad header rejects before any call.

`ZkcSecurity.Examples.ExecutableSchnorrFiatShamir` transfers the compiled
knowledge bound to proof bytes through this canonical verifier. `decoded` maps
a byte prover to typed proofs, `validate_cases` splits successful canonical
verification from rejection, and `acceptance_le` transports the probability
bound. `knowledge_soundness` states
`acc * (acc / (Q + 1) - 1 / |F|)` at most the extraction probability for every
decoder, host budget and expected binding, under the compiled theorem's
explicit fixed-statement, field/module and oracle assumptions. The native
reader and runtime links remain the separate assumptions below.

## The compiled Sumcheck proof verifier

`ZkcExamples.Executable.SumcheckProof` applies the rule to the validator of the
`zkc.program/0` candidate of the Sumcheck example's `example::Proof`
(`SumcheckProofProgramData`). The rule accepts it against the constructed
validator of `ZkcExamples.Construction.SumcheckProof`: a helper call for the
empty point, a loop over the round count of at most the Entry's static maximum
of rounds (`maximum`, two for this Entry), each receiving its two message
coordinates, observing them, checking the round sum, drawing and delivering the
challenge, extending the point by a helper call and updating the claim, and
finally the terminal check as a helper call. Its receive plan gives two scalar
messages per admitted round (`plan_types`).

`ZkcExamples.Executable.SumcheckHelpers` proves the three helpers prepared
against the admitted source's closed helper table. The helper rule accepts the
empty point and the point extension (`rule_accepted`). The terminal check
iterates and is outside the rule's table (`check_outside`); its preparation
(`check_prepared`) evaluates its body, which checks the authored table shape
with a doubling loop and then folds the table over the point one coordinate at
a time, interpolating its low and high halves with one numerical map call
(`map_returns`), whose decoded expression is `low + (high - low) r`. The fold is
`Zkc.Polynomial.Multilinear.restrictPrefixValues`, and the source contract of
the check (`SumcheckSourceContracts.check_equation` and the stop contracts for
out-of-range lengths) gives the same result in every case. The same evaluation
gives the check's charge, `62 + 20 · n` on a well-shaped table and a point of
`n` coordinates (`check_cost`).

`ZkcExamples.Executable.SumcheckFamily.honest_accepted` proves actual byte
acceptance for any artifact of the selected Sumcheck shape and its local
realization. The artifact fixes the program, context, nominal names, maximum
below 64, actual participant/validator, finite native admission, Code reading,
returned references, input schema and receive plan. The realization supplies
only local helper mathematics, helper prices, occurrence/request laws and
native helper preparation. It supplies no successful execution or whole-program
correspondence premise.

The family derives round and loop correspondence, the restricted-table
invariant, successful terminal execution, sufficient resources and exact
message decoding. With append-helper price bounded by `a`, its sufficient
charge is `72 + (a + 57) * rounds`; the terminal helper uses the selected
`62 + 20 * point.length` price law. This is a reusable cost method for this
shape, not a universal backend cost model. Generic family modules do not import
the retained Entry; `SumcheckCharges` and `SumcheckDomainHonest` discharge its
concrete local obligations.

Occurrence laws require the actual typed draw request and schema, coordinate
resolution and projected oracle keys. The former condition that an origin
merely exists is insufficient: a present but unsupported request can still
refuse. The malformed-request control demonstrates this changed admission
boundary. A second native fixture changes the actual entry, projected oracle
keys and maximum, and checks framed-byte completeness at zero and three rounds.
It is a constructed fixture, not another compiler-exported protocol.

`executable_metered` instantiates `DomainVM.checked_execute_metered` for the
actual byte program. `domain_prunes` and `executable_transform_prunes` state
that validation can only remove acceptance from, respectively, the actual
constructed verifier and the source transform. They quantify every budget,
framing header, decoder, typed table, claim and round count. The former uses
the actual exported receive plan. Neither theorem requires table validity or
codec inversion. Prepared helper equations and canonical result-schema facts
are proved for the actual program.

`ZkcExamples.Executable.SumcheckCharges` bounds the charges of a complete run on
a table of `2 ^ rounds` values. The charge is derived from the reading
(`SumcheckCharges.charge`): the initial Pending tuple construction and opening,
the loop's entry, the rounds and their yields, the consuming terminal check and
its helper body, and the return. The Pending boundary adds four fixed
instructions relative to the earlier scalar-only root. The loop is bounded by `DomainVM.FitsK.loop_invariant` with the
invariant that the carried point has one coordinate per completed round. For
this Entry `charge rounds = 72 + 59 · rounds` (`charge_eq`): per round, 38
instructions in the loop body, the point extension's body included, its yield,
and 20 in the terminal check: 14 in its fold and 3 in each of its two shape
checks' doubling loops. It is `DomainVM.Sufficient` for every proof and
every round count (`sufficient`).
`ZkcExamples.Executable.SumcheckCompleteness.honest_accepted` states
honest-prover completeness of the executable: for every challenge function,
codec whose decoder inverts its encoder on round messages of bounded length,
budget of at least `charge rounds`, expected binding of 32 bytes, initial
transcript and table of `2 ^ rounds` values with at most the Entry's static
maximum of rounds, host validation accepts the honest proof bytes of the table's
sum. The honest producer absorbs what the verifier absorbs and draws what it
draws, sending the sums of the low and high halves of its current table in each
round and then restricting the table at the challenge. Each honest round passes
by the round statement with the challenge function's answers and no stop, and
the rounds compose by the fold invariant: the claim is the sum of the table
restricted at the point. At two rounds the bound is 186 instructions, the
runtime's measured threshold.

`ZkcArkLib.Examples.ExecutableSumcheckFiatShamir` transfers the compiled
Sumcheck bounds to provers of proof bytes. `decoded` decodes a byte prover's
proofs at the receive types of the statement's round count; with
`Prunes.prEvent_le`, the executable accepts at most as often as the compiled
verifier accepts the decoded proofs (`acceptance_le`). `soundness` bounds the
acceptance of a false claim by `(Q + count) / |F|` for a fixed well-formed
statement, and `adaptive_soundness` by `(Q + 2) * (1 / |F| + loss)` for
statements the prover chooses after its queries, for every decoder, budget,
expected binding and application context; `reduced_soundness` instantiates the
challenge decoding. The adaptive theorems start host validation from `initial`,
the host's binding of the policy's public inputs (`public_inputs`: the table
values, the claimed sum and the round count): one typed public-value binding
event of the application context and the row of those inputs, in order, the
table as a vector, the claim as a scalar and the round count as a count
(`CompiledSumcheckFiatShamir.publicInitial`). The row determines the statement
(`initial_determined`, from `ZkcSecurity.FiatShamir.determined_single`), which
discharges the determining premise of the compiled adaptive theorem. This is
statement determination only; that the runtime's transcript absorbs these rows
is the host-binding assumption below.

## A rescheduled program

`ZkcExamples.Executable.DeferredRounds` connects the exact
`zkc.program/0` candidate of the
[deferred-rounds fixture](../../../common/tests/fixtures/projects/deferred-rounds/README.md)
to its canonical constructed participant. The participant computes the first
round's product after its first draw; the native schedule computes both
products after the second draw. `rescheduled` checks that the instruction lists
differ, and `schedule_normalized` composes the actual reading with the proved
canonical normalization checker. A complete run charges 35 instructions.

`executable_observation` preserves the complete returned scalar tuple and
unread status at budgets of at least 35. `executable_prunes` gives acceptance
domination at every budget, for arbitrary byte strings and decoders.
`readable_returns` proves the scalar readback condition at every actual return;
`canonical_acceptance` connects full native readback to nominal acceptance.
Consequently `executable_validate` gives equality with the actual participant's
acceptance under the exact header and sufficient budget. Short-budget
rejection retains preceding oracle effects: the 34-instruction control rejects
after two calls, while a missing second frame rejects after one.

These theorems take an actual `Structured.Program`; the validator uses no
helpers, so `prepared` discharges that obligation for every program. They stop
at the constructed participant. No original-source or cryptographic theorem
for DeferredRounds is asserted here.

## Named assumptions and trusted links

The security statements keep the random-oracle and encoding assumptions of the
[compiled theorems](fiat-shamir.md#named-assumptions); the Schnorr statement
also keeps the fixed-statement assumption. Their transport and
native-correctness assumptions are replaced by the following.

- The runtime accepts proof bytes for the admitted validator only when
  `validate` accepts them under the Entry's checked occurrence context
  (`SchnorrProof.context`, `SumcheckProof.context`), for the same expected
  binding, data inputs and challenge function. Soundness needs only this
  direction; completeness also needs the converse at a sufficient budget and
  within the runtime's other resource limits. In particular, the Rust host
  caps the whole framed proof at 16 MiB; the preserved Lean honest theorem
  bounds individual encoded messages. Deployment completeness additionally
  needs the whole-proof cap, not just those per-message bounds.
- Installed kernels implement the meanings of `installed`, at the admitted
  representations and within the runtime's capacity limits. For a numerical
  call this includes that the kernel evaluates the expression as
  `Numerical.decode` reads its payload.
- The native codec is a function of a message's bytes and type. Soundness needs
  no other property of it.
- The managed transcript absorbs the invocation's public values injectively.
  For the Sumcheck statement this is the binding `initial`, whose rows stand for
  the canonical public rows of the invocation root.
- The program reader. Each committed `ProgramData` module names the SHA-256 of
  the `zkc.program/0` bytes it was rendered from, and the bridge requires it to
  equal the rendering of the compiler's fresh program, byte for byte. The
  trusted link is the renderer's reading of those bytes: that the entry map's
  validator participant, its instructions in order, the local functions it
  reaches with their formals, results and instructions, the operation bindings
  with their contracts, static arguments and implementations, the physical
  types and the decoded occurrence templates are those the runtime's program
  loader reads from the same bytes. No Lean reader of the program bytes is
  proved; the runtime's identity checks bind the executed package to the
  program digest the receipt names.
- The structured exporter and its renderer denote the original MLIR.

Structural admission checks the constructed-participant export against the
original export; separate all-reply connections establish its execution meaning.
Canonical normalization and the native correspondence connect the actual
program reading to that participant. Its policy must equal the deployment's, and the
deployment's role map, which the runtime uses, must select the acceptance
position and public inputs of the Lean statement; the bridge checks both.
Encoding and challenge-distribution assumptions remain those of the transcript
model.
