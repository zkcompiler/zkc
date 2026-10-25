# Executable validator stage

The [transcript-construction](fiat-shamir.md) and
[participant projection](participant-projection.md) rules relate a native proof
deployment's constructed validator to the original verifier. This page owns the
next stage: the validator participant of the deployment's `zkc.program/0`
candidate, which the runtime admits and executes. A per-compile lowering rule
relates the two, so that a theorem about the constructed validator transfers to
the executable program. The modules are `Zkc.Executable.{Program, Numerical,
Execution, Installed, Refusal, Normalization, Lowering, Relation, Evaluation,
Soundness, Pruning, Completeness, NormalizationSoundness, Cleanup, Helpers,
HelperSoundness, Loops, Framing}`.

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
  parameter.
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

`checkLowering vocabulary participant validator` is the per-compile rule: the
reading for the participant's called helpers must have the constructed
validator's input and output sorts, symbol, entry and validator role, and its
instructions and returned references must equal the constructed validator's or
have the same normal form (below); equality is tried first. A refusal names its
reason: an unsupported instruction, an uninstalled binding, an operand, sort or
custody failure, a helper whose body fails its conditions, a loop failing its
conditions, a duplicated symbol, an unadmitted representation, a differing part,
or where the normal forms differ (an anchor, an anchor's operand, an ill-sorted
calculation, a loop's yields or a returned reference). The kernel evaluates the
rule on the actual pair.

## Normalization

The compiler schedules pure arithmetic differently from the constructed export:
it computes a value in a calculation call placed before the first instruction
that needs it, shares equal values and drops unused ones.
`checkNormalized inputs exported exportedReturned reading readingReturned`
compares two instruction lists up to such schedules, which the native
[normalization invariant](../../../docs/spec/verification/refinement.md#normalization-across-transcript-operations)
permits.

- An instruction is movable when it is a calculation that never stops on
  operands of its declared sorts (every calculation except `boundedAt`) or
  occurrence-coordinate construction (`Instruction.movable`; `movable_iff`
  states the list). Every other instruction is an anchor: receives, sends,
  transcript operations, guards, helper calls, loops, calculations that can stop
  and anything unsupported.
- A movable instruction denotes a pure term over leaves: the inputs (in a loop
  body, the enclosing scope's values), the loop's index and carried values, and
  the results of earlier anchors. Each scope keeps one table of terms, in which
  equal terms of either program have one id, and every term carries its sort. A
  calculation's operands must have the sorts of its signature.
- The check walks both programs anchor by anchor. Before each anchor it records
  the movable instructions of either program. The two anchors must have the same
  operation and declared results, and their operands must denote the same terms.
  The two bodies of a loop are checked as a scope of their own, which starts
  from fresh leaves for the enclosing values, the index and the carried values;
  their yields must denote the same terms at the carried sorts. At the end the
  returned references must denote the same terms.

Accepted are therefore operand renumbering, every schedule of pure calculations
that respects their dependencies, sharing of equal terms, and dropping or adding
terms that reach no anchor and no returned value. Refused are a changed anchor
sequence (a moved, added or removed receive, transcript operation, guard, helper
call, stopping calculation or loop), an operand that denotes another term (a
wrong or retargeted operand, swapped operands, a changed constant or operation),
an ill-sorted calculation and work moved into or out of a loop body. The refused
moves are unsound, not only unrecognized: a calculation that stops, or a
rejecting guard, moved after a challenge makes the program query the challenge
function where the export does not.

| Theorem | Statement |
|---|---|
| `movable_iff` | The movable instructions are exactly the total calculations and well-formed occurrence-coordinate construction |
| `normalize_ideal` | The movable instructions at the head of a program extend its environment by the values of their terms: they never stop and query nothing |
| `checkNormalized_sound` | Accepted programs have equal ideal meanings in every monad and for every challenge function, on inputs of the declared sorts, when every called helper returns values of its declared result sorts (`HelperSorted`). Their outcomes, stop reasons, unread proofs and challenge queries, with their histories, are therefore equal |
| `checkNormalized_flow` | Every term that a value of either program depends on is held by that program at the value's position or earlier, so a value first computed after an anchor is none of the terms the anchor's operands depend on |

A helper of a closed helper table returns values of its declared result sorts
when the call declares the helper's outputs (`helperSorted_of_outputs`).
Normalization relates ideal meanings only: charges, frames, stop sites and where
a budget runs out differ between schedules. Soundness at every budget needs no
more, since host validation prunes the ideal meaning of the reading, which is
the constructed validator's. Completeness at a budget concerns the reading's own
charges (below).

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

`metered` is the ideal meaning of a reading under a budget, in the continuation
style of `Zkc.Construction.idealK`: an instruction runs, as `idealStep` runs it,
only if its charge is within the budget, a helper call charges what its body's
evaluation charges, a loop charges its start and every iteration's yield, and
returning needs one more instruction. `decodeProof` decodes the message bytes at
the receive types, up to the first message that is missing or does not decode,
and marks bytes left after the last receive as one unread entry.

For every validator the rule reads, every occurrence context, challenge function
in every lawful monad, helper table that the called helpers are prepared for,
decoder, budget, data input admitted at the entry sorts, initial transcript and
byte string:

| Theorem | Statement |
|---|---|
| `execute_metered` | The executable and the metered meaning of the reading on the proof decoded at `Plan.types` of the data inputs have the same observation and the same challenge interaction. An observation is the outcome class (a return with its values, a budget stop, or another stop class) and, after a normal return, whether the whole proof was read |
| `validate_metered` | With the expected header, host validation is the acceptance of the metered meaning's observation |
| `metered_prunes` / `validate_prunes` | At every budget, the metered meaning is the ideal meaning of the reading's constructed instructions with some continuations replaced by stops, the two making the same challenge calls in the same order otherwise (`Prunes`); hence host validation, with any header, is the ideal acceptance of the decoded proof with some continuations replaced by rejection |
| `execute_ideal` / `execute_short` | For a reading with static charges, at a budget of at least the total charge the same holds for the ideal meaning itself, and below it every observation is a stop |
| `validate_ideal` / `validate_rejects` | For a reading with static charges, with the expected header and a sufficient budget host validation is the ideal acceptance of the decoded proof; otherwise it rejects on every path |
| `execute_cleaned` | Every run leaves every frame it entered, the participant's, the loop iterations' and the local calls' included, and each exit leaves the innermost frame still open, so a stop leaves the active frames innermost first |
| `checkLowering_sound` | An accepted pair has the constructed validator's interface for its entry and validator role, and the reading's ideal meaning is the constructed validator's on inputs of its sorts when the called helpers return values of their declared result sorts |
| `validate_prunes_export` | For an accepted pair, host validation with any header prunes the ideal acceptance of the constructed validator itself on the decoded proof |

`Prunes` turns into a probability bound in the security integration
(`ZkcSecurity.VCVio.Pruning.Prunes.prEvent_le`): simulated by any stateful
oracle implementation, a pruned computation satisfies an event disjoint from its
rejections at most as often as the computation it prunes. Acceptance is
therefore reflected at every budget, which is what a soundness consumer needs.
Completeness additionally needs a budget sufficient for the run (below), a
decoder that recovers what the producer encoded, the host's binding in the
header, and a producer that completes. The relation preserves outcome classes,
the challenge interaction, the consumed proof on return and acceptance. It does
not relate stop sites, frame events or the instructions charged at a stop, which
belong to the executable meaning alone. Retiring the live transcript on a stop,
and the returned one on a return, is part of the meaning's definition. The
meaning has one resource, the instruction budget.

## Completeness

When a reading has loops or helper calls, its charges depend on the run, and a
sufficient budget is a bound on runs. `FitsK` follows the metered meaning: a
charge, an instruction or a loop iteration must fit within the budget before it
runs, a helper call must fit with what its body charges on its actual arguments,
and the continuation must fit wherever the ideal meaning passes on. Where the
ideal meaning passes on is `Continues`: the ideal step read in the
predicate-transformer monad `Always`, in which a challenge holds of every answer
and a stop holds trivially. A run that stops needs no further budget.
`Sufficient` is the bound for a whole run, its return included.

| Theorem | Statement |
|---|---|
| `metered_sufficient` | Under `Sufficient`, the metered meaning of a reading is its ideal meaning, in every monad and for every challenge function |
| `execute_sufficient` / `validate_sufficient` | Under `Sufficient` on the decoded proof, the executable's observation and challenge interaction are those of the reading's ideal meaning; with the expected header, host validation is the ideal acceptance of the decoded proof |

A program's completeness then needs a charge bound for the inputs it admits and
the ideal meaning's acceptance of the honest proof (`Zkc.Executable.Loops`). For
a program the rule accepts through [normalization](#normalization), the
charges are those of the program's own reading, since normalization relates
ideal meanings only.

*Charges by evaluation.* For code without loops, `Code.charges bound code` adds
what each item charges, taking for each helper call the bound `bound` gives for
its body; `helperBound` evaluates a cost bound of a local function's body
without iterations, a conditional counted with its dearer region
(`helperCost_le`). `FitsK.of_charges` turns the sum into `FitsK`, wherever the
ideal meaning passes on. A helper whose body iterates has its charge on its
actual arguments proved with its preparation.

*Loops.* A loop charges its entry and then, for each iteration, its body and its
yield. `FitsK.loop_invariant` bounds a loop whose runtime count is at most its
static maximum by `used + 1 + chargeSum charge 0 count`, the sum of iteration
charges, from an invariant indexed by the iteration on the carried values and
the unread proof: the invariant holds at entry, each iteration from a state the
invariant holds of fits within its charge and yields a state the invariant holds
of next, and the continuation fits from every final state. The invariant states
what each iteration consumes from the proof, the shape of what it carries, what
its helper calls charge and where it may stop. `chargeSum_uniform` gives
`count · (body + 1)` under a uniform body bound.

*Passing.* `Passes` reads the ideal meaning in `Always`, with the challenge
answers a relation admits and a postcondition for stops. With every answer and
stops allowed it implies `Continues` (`continues_of_passes`), which the charge
bound needs; with the answers of a challenge function and no stop allowed, the
ideal meaning in `Id` passes on to a state `holds` holds of (`idealK_oracle`).
One statement per iteration, on every proof and every answer, therefore serves
both the charge bound and an honest run, and `iterateM_invariant` composes an
honest run's iterations from a per-iteration invariant.

*Honest proof bytes.* `messageBytes` frames messages of one receive type after
the framing magic and the binding; when the decoder inverts the encoder at that
type and every encoding fits in one proof, they decode to the messages
(`decodeProof_messages`), and the header is the expected one.

The rule refuses a program whose calculations come in another order than the
constructed instructions. A normalization that reschedules pure, total
calculations without crossing a transcript operation's inputs
([normalization invariant](../../../docs/spec/verification/refinement.md#normalization-across-transcript-operations))
preserves the ideal meaning's outcome and challenge interaction, but not where a
bounded run stops: the metered meaning charges each instruction where it runs.
A theorem about such a program's metered executions therefore needs its own
pruning relation at every budget, as `metered_prunes` is for the lowering rule,
or a budget of at least the total charge, under which `execute_ideal` and
`validate_ideal` identify the metered meaning with the ideal one.

## The compiled Schnorr proof verifier

`ZkcExamples.Executable.SchnorrProof` applies the rule to the validator of the
`zkc.program/0` candidate of `example::Proof`
(`SchnorrProofProgramData`, rendered from the exact program bytes). The rule
accepts it against the constructed validator of
`ZkcExamples.Construction.SchnorrProof`; the validator calls no helper, and a
complete run charges 25 instructions. `executable_transform` composes the rule
with the composed transcript-construction and participant projection rules
(`SchnorrProof.compiled_transform`, an instance of
`Zkc.Construction.compiled_transform`; no equation specific to the Entry): at
any budget of at least 25, under the Entry's checked occurrence context, the
executable's observations and challenge interaction are those of the
Fiat–Shamir transform of the original Proof Entry's verifier on the decoded
proof. The composed rules are applied to the admitted original
(`SchnorrProof.imported`). The Entry-specific equations about a program's
meaning on the chain are all on the original side. Two are checked by the
kernel's evaluation: `SchnorrProof.process_equation` equates the admitted
original Proof Entry's validator with the common Schnorr experiment that the
VCVio consumer uses, and `SchnorrProofBinding.formula_process` gives the process
of the DLog formula the original retains, from which the knowledge target is
read. `SchnorrProof.original_verifier` and `verifier_correspondence` are derived
from these with definitions and general lemmas. The other Entry-specific facts
on the chain are wiring: the derived context, the input relation and the
position of the acceptance output.
`executable_validate` and `executable_rejects` state host validation in the same
terms.

`ZkcSecurity.Examples.ExecutableSchnorrFiatShamir` transfers the compiled
knowledge-soundness bound to provers of proof bytes. `decoded` turns a byte
prover into a prover of typed proofs; for every proof, host validation is either
the ideal verification of the decoded pair or rejects on every path
(`validate_cases`), so acceptance by the executable is bounded by acceptance of
the decoded prover (`acceptance_le`). `knowledge_soundness` states
`acc * (acc / (Q + 1) - 1 / |F|)` at most the extraction probability for every
decoder, host budget and expected binding.

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

`ZkcExamples.Executable.SumcheckFamily` proves the executable theorems once for
every compiled validator of the Sumcheck family. An `Artifact` carries a
constructed validator and its executable program with the facts the kernel
checks per compile: the lowering rule's acceptance, the family's instructions
(`ZkcExamples.Executable.SumcheckShape`) with the compile's names and static
maximum, the reading's code and receive plan, the occurrence templates under the
context, the bound of the empty point's body, and the helper meanings,
preparation and result sorts of the admitted original. One statement describes a
round (`round_passes`): on every proof and under every answer, the round either
stops (refused when its two messages are not scalar coordinates, rejected when
their sum is not the claim) or passes on to the point extended by the drawn
answer, the claim updated by the answer and the transcript with both messages,
the challenge and its delivery absorbed. Its charge (`roundCharge`) is computed
from the reading by evaluation. No proof in the family depends on the value of
the maximum, which an artifact bounds below 64, the terminal check's bound on
the point's coordinates.
`ZkcExamples.Executable.SumcheckProof.artifact` is this Entry's artifact.

`executable_metered` instantiates `execute_metered`. `executable_prunes` and
`executable_transform_prunes` state that host validation of proof bytes prunes,
at every budget and with every framing header, the ideal acceptance of the
decoded proof, which `SumcheckProof.compiled_transform` makes the acceptance of
the Fiat–Shamir transform of the original Sumcheck validator. The three called
helpers return values of their declared result sorts (`helpersSorted`), since
each call declares its checked helper's outputs.

`ZkcExamples.Executable.SumcheckCharges` bounds the charges of a complete run on
a table of `2 ^ rounds` values. The charge is derived from the reading
(`Artifact.charge`): the empty point's call and body, the loop's entry, the sum
of the rounds' charges and yields, the terminal check's call with what its body
charges, and the return. The loop is bounded by `FitsK.loop_invariant` with the
invariant that the carried point has one coordinate per completed round. For
this Entry `charge rounds = 68 + 59 · rounds` (`charge_eq`): per round, 38
instructions in the loop body, the point extension's body included, its yield,
and 20 in the terminal check: 14 in its fold and 3 in each of its two shape
checks' doubling loops. It is `Sufficient` for every proof and
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

`ZkcExamples.Executable.DeferredRounds` applies the rule to the validator of the
`zkc.program/0` candidate of the
[deferred-rounds fixture](../../../common/tests/fixtures/projects/deferred-rounds/README.md),
a two-round Fiat–Shamir proof whose verifier consumes the first round's product
only at the end. The constructed validator computes that product after the
first draw; the program computes it, with every other product, in one
calculation call after the second draw. The rule accepts the pair (`accepted`)
by normalization (`rescheduled`: the reading is not the constructed validator
instruction for instruction), and a complete run charges 35 instructions.
`executable_prunes` and `executable_validate` state host validation in terms of
the constructed validator's ideal acceptance of the decoded proof, at every
budget and at a budget of at least 35. The transcript-construction check
accepts the Entry's export (`ZkcExamples.Construction.DeferredRounds.accepted`);
the participant projection rule is not applied to it, so these theorems stop
at the constructed validator.

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
  within the runtime's other resource limits.
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

The constructed-participant export carries no trusted claim about instructions:
the construction and projection rules check them against the original export and
the lowering rule against the program. Its policy must equal the deployment's, and the
deployment's role map, which the runtime uses, must select the acceptance
position and public inputs of the Lean statement; the bridge checks both.
Encoding and challenge-distribution assumptions remain those of the transcript
model.
