# Constructed participant admission

`Zkc.Source.Constructed` admits the actual carrier defined by the
[native export contract](../../../docs/spec/formats/constructed-source.md).
It reuses `Source.Program`, its typed contexts, raw decoding and `PIR.Proc`.
There is no second protocol schedule or security kernel.

A type is a finite list of nominal native type strings, representing a result
product. Scalars are singleton products. `Primitive` retains its exact signature,
attributes, binding and invocation origin. `Op.primitive`, `Op.project` and
`Op.pack` form the vocabulary. Projection and final packing have fixed pure
meanings over heterogeneous `Values`; they cannot replace a provider's successor
state. `Meaning` supplies the scalar carriers, Boolean interpretation and a
`PIR.Proc` for each primitive with its actual operands and complete typed reply.

`Snapshot.check` lowers flat instructions into the existing raw source, elaborates
all operand/result references and checks exact erasure. A guard becomes a branch
whose false edge halts with `reject`. An explicit terminal stop must be last and
have no returned references. Unknown instructions, out-of-range projections,
ill-typed operands and stop tails refuse before execution. Guard attributes are
retained identity/provenance metadata; they do not create a new observed event.
Primitive stops and early guards preserve the ordinary `Proc.bind` stop behavior.

The maintained laws are:

- `Snapshot.check_exact`: successful admission's program erases to precisely the
  lowered actual carrier, including unused effects, returns and guard failures.
- `Snapshot.check_elaborate`: re-elaboration of that actual carrier recovers the
  admitted typed program.
- `Snapshot.imported_checked`: the proof-indexed successful-check extractor
  returns the actual checker result, without a fallback or asserted correspondence.
- `Imported.reelaborate`: erasure/re-elaboration recovers the same typed program.
- `Snapshot.check_denotation_unique`: two successful admissions of the same
  carrier have equal complete denotations for every interpretation and input.
- `Snapshot.check_execute`: direct execution of the flat instruction carrier
  equals the checked typed program for every primitive meaning and every input.
  The direct evaluator does not call lowering, elaboration or typed denotation.
  `lower_denotation` proves the pack/project/guard translation into raw syntax;
  `RawProgram.denote_elaborate` proves raw-to-typed execution correspondence.
- `Snapshot.check_denoteRaw`: the intermediate raw evaluator has the same
  denotation, independently of the flat-instruction evaluator.
- `project_reply` and `pack_reply`: bridge-introduced result movement is pure and
  returns precisely the selected component or complete ordered product.

These are admission, representation and source-model execution laws. They do not prove native C++
exporter correctness or a Fiat–Shamir reduction. Applying them to native output
requires the checked native export and exact artifact regeneration. A protocol
consumer must separately check primitive descriptors and prove its actual-body
normalization equation under a specified interpretation. No assumed
correspondence field replaces that equation.

The generated realization proof audits both `source_denotation` and
`raw_denotation` in addition to admission and its protocol-specific equation.
This closes translation within the declared export grammar. JSON parsing,
native extraction, selected Local expansion before export, nominal type meaning
and production primitive implementations remain explicit boundaries.

`ZkcTools.Constructed.Replay` checks reached primitive names and actual operands
against explicit replies, keeping full result tuples, stops and event order.
Its natural-number tokens and the bridge tests' Z/97 arithmetic, tokenized codec
and deterministic state-sensitive transcript are test meanings. They make no
production field/curve, byte-decoder, Merlin or random-oracle conformance claim.
The [bridge driver](../../bridges/constructed/README.md) states reproduction and
failure controls.
