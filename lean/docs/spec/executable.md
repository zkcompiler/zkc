# Executable validator stage

The [transcript-construction](fiat-shamir.md) and
[participant projection](participant-projection.md) rules relate a native proof
deployment's constructed validator to the original verifier. This page owns the
next stage: the validator participant of the deployment's `zkc.program/0`
candidate, which the runtime admits and executes. A per-compile lowering rule
relates the two, so that a theorem about the constructed validator transfers to
the executable program. The modules are `Zkc.Executable.{Program, Execution,
Installed, Lowering, Soundness}`.

## Carrier

`Validator` holds the participant that the program's entry map assigns to the
deployment's entry and validator role, with every local function it calls and
every operation binding those functions use. Names, sites, schemas and physical
types are kept as the artifact spells them; a physical type is a value sort with
a representation, such as G1 at `arkworks.g1/0`. An occurrence template carried
by a transcript operation is decoded; other parameters stay text. Participant
instructions are typed receives, local calls and the final return; function
instructions are operations on declared bindings and the final return. Any
other instruction is kept as unsupported, which the rule refuses. The carrier
fixes no meaning.

## Meaning

`execute` runs a validator as the native runner does, on data inputs, the host's
initial transcript and the proof's message bytes, with the deployment's
occurrence `Context`, a challenge function in any monad, a decoder and an
instruction budget.

- Work. A local call becomes a frame entry, the body's operations and the
  frame's return. Every receive, frame entry, operation, frame return and final
  return is charged one instruction. The budget is checked before a participant
  action is exposed and before each charge inside a frame, so a budget of `b`
  executes exactly the first `b` charged steps.
- Framing. A receive reads an eight-byte little-endian length and that many
  bytes. A missing message cancels the run; a message that does not decode at
  the receive's physical type stops it after charging the receive. A decoded
  value of another sort is a contract failure.
- Operations. A binding resolves through a `Vocabulary`: each row assigns a
  meaning to an exact contract, static arguments and installed implementation,
  and each representation row admits a sort at a representation. Meanings are
  those of `Zkc.Construction`: structured calculations
  (`Zkc.Construction.calculate`), the empty coordinate vector, and observation
  and challenge on the ideal transcript model. A transcript operation's
  occurrence template is named by its model occurrence under the context; a
  template without one is a contract failure, as it is a refusal of the ideal
  meaning.
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
arkworks scalar-field and G1 kernels, the native index kernel and the Merlin
transcript kernels of `merlin3.bls12-381.fr64be/0`. The Schnorr validator below
uses seven of its nine operation rows; the scalar-field addition and
multiplication rows serve the producer.

## Lowering rule

`Validator.read` reads the validator's machine work back as constructed
instructions. Frame entries and returns are transparent: formals denote actual
operands and results denote the operands of the return, as the
constructed-participant export expands helpers. Each operation is read through
the vocabulary's meaning, with checked operand sorts, consumption of the live
transcript and the live transcript as the only returned transcript. A local
call's operands must have the sorts of its declared formals, function and
binding symbols must be distinct, and every declared type and receive must have
an admitted representation. The reading records the cumulative charge at which
each instruction executes, the charge of a complete run and the receive types
in order.

`checkLowering vocabulary participant validator` is the per-compile rule: the
reading must equal the constructed validator's instructions, returned
references, input and output sorts, symbol, entry and validator role. A refusal
names its reason: an unsupported instruction, an uninstalled binding, an
operand, sort or custody failure, a duplicated symbol, an unadmitted
representation, a differing part or the first differing instruction.

## Soundness

`metered` is the ideal meaning of constructed instructions under a budget, in
the continuation style of `Zkc.Construction.idealK`: an instruction runs, as
`idealStep` runs it, only if its charge is within the budget, and returning
needs the total charge. `decodeProof` decodes the message bytes at the receive types,
up to the first message that is missing or does not decode, and marks bytes left
after the last receive as one unread entry.

For every validator the rule reads, every occurrence context, challenge function
in every lawful monad, helper table, decoder, budget, data input admitted at the
entry sorts, initial transcript and byte string:

| Theorem | Statement |
|---|---|
| `execute_metered` | The executable and the metered ideal meaning of the reading on the decoded proof have the same observation and the same challenge interaction. An observation is the outcome class (a return with its values, a budget stop, or a refusal, which covers decoding, truncation and contract failures) and, after a normal return, whether the whole proof was read |
| `execute_ideal` | With a budget of at least the total charge, the same holds for the ideal meaning itself |
| `execute_short` | Below the total charge every observation is a stop; it rests on `idealK_constant`, which states that the ideal meaning of any program returns only stops or results of its continuation |
| `validate_ideal` / `validate_rejects` | With the expected header and a sufficient budget, host validation is the ideal acceptance of the decoded proof; otherwise it rejects on every path |
| `execute_cleaned` | Every run leaves every frame it entered, the participant's included, and each exit leaves the innermost frame still open, so a stop leaves the active frames innermost first |
| `checkLowering_sound` | An accepted pair reads back exactly as the constructed validator, for its entry and validator role |

Acceptance is reflected at every budget, which is what a soundness consumer
needs. Completeness additionally needs a budget of at least the total charge, a
decoder that recovers what the producer encoded, the host's binding in the
header, and a producer that completes. The relation preserves outcome classes,
the challenge interaction, the consumed proof on return and acceptance. It does
not relate stop sites, frame events or the instructions charged at a stop,
which belong to the executable meaning alone. Retiring the live transcript on a
stop, and the returned one on a return, is part of the meaning's definition.
The meaning has one resource, the instruction budget.

## The compiled Schnorr proof verifier

`ZkcExamples.Executable.SchnorrProof` applies the rule to the validator of the
`zkc.program/0` candidate of `example::Proof`
(`SchnorrProofProgramData`, rendered from the exact program bytes). The rule
accepts it against the constructed validator of
`ZkcExamples.Construction.SchnorrProof`; a complete run charges 25
instructions. `executable_transform` composes the rule with the composed
transcript-construction and participant projection rules
(`SchnorrProof.compiled_transform`, an instance of
`Zkc.Construction.compiled_transform`; no equation specific to the Entry): at
any budget of at least 25, under the Entry's checked occurrence context, the
executable's observations and challenge interaction are those of the
Fiat–Shamir transform of the original Proof Entry's verifier on the decoded
proof. The only Entry-specific equation on the chain is on the original side:
`SchnorrProof.process_equation`, kernel-checked, equates the admitted original
Proof Entry's validator with the common Schnorr experiment that the VCVio
consumer uses.
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

## Named assumptions and trusted links

The security statement keeps the random-oracle, binding and fixed-statement
assumptions of the [compiled theorem](fiat-shamir.md#named-assumptions). Its
transport and native-correctness assumptions are replaced by the following.

- The runtime accepts proof bytes for the admitted validator only when
  `validate` accepts them, for the same expected binding, data inputs and
  challenge function. Soundness needs only this direction; completeness also
  needs the converse at a sufficient budget and within the runtime's other
  resource limits.
- Installed kernels implement the meanings of `installed`, at the admitted
  representations.
- The native codec is a function of a message's bytes and type. Soundness needs
  no other property of it.
- The renderer reads the admitted program bytes exactly, and the structured
  exporter and its renderer denote the original MLIR.

The constructed-participant export carries no trusted claim about instructions:
the construction and projection rules check them against the original export and
the lowering rule against the program. Its policy must equal the deployment's, and the
deployment's role map, which the runtime uses, must select the acceptance
position and public inputs of the Lean statement; the bridge checks both.
Encoding and challenge-distribution assumptions remain those of the transcript
model.
